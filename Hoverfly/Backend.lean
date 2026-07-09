import ProofWidgets

import Palamedes.Synthesizer

namespace Backend
open Lean ProofWidgets Server Lean.Meta Lean.Elab.Tactic

-- TODO: Need this to make the tactics resolve correctly
open Gen.CorrectGen

def StateId := Nat
  deriving OfNat, BEq, Hashable, ToJson, FromJson, HAdd, ToString

structure ClusterInfo where
  members : List StateId
  sharedMVars : List MVarId

structure State where
  nodeCounter : StateId := 0
  goalMap : Std.HashMap StateId (MVarId × Elab.Term.SavedState) := ∅
  tacticMap : Std.HashMap StateId (Syntax × StateId) := ∅
  clusterMap : Std.HashMap StateId ClusterInfo := ∅
  deriving TypeName

structure APINode where
  isGoal : Bool
  id : StateId
  display : String
  tacticError : Option String := none
  noop : Bool := false
  originalId : Option StateId := none
  leanOrder : Nat := 0
  deriving ToJson, FromJson

structure GetSubgoalsParams where
  id : StateId
  stateRef : WithRpcRef State
  pos : Lsp.Position
  deriving RpcEncodable

def getGoalClusters (goals : List MVarId) : MetaM (List (List MVarId)) := do
  let mvarGoalLists ← goals.mapM (fun g => do
    let mvs ← g.getMVarDependencies
    let unassigned ← mvs.toList.filterM fun m => do return !(← m.isAssigned)
    return (g, unassigned))
  let mvarLists := mvarGoalLists.map (fun (_,x) => x)
  let f mvs clustersSoFar : List (List MVarId) :=
    let g mv acc : List (List MVarId) :=
      let (withMv, withoutMv) := acc.partition (fun l => l.contains mv)
      withMv.flatten.eraseDups :: withoutMv
    mvs.fold g clustersSoFar
  let clusters : List (List MVarId) := mvarLists.fold f mvarLists
  let grouped := clusters.filterMap fun cl =>
    let gs := (mvarGoalLists.filter fun (_, mvs) => mvs.any cl.contains).map (·.1)
    if gs.isEmpty then none else some gs
  let touched := grouped.flatten
  let singles :=
    (mvarGoalLists.filter fun (g, _) => !touched.contains g).map (fun (g, _) => [g])
  return grouped ++ singles

def unassignedDeps (g : MVarId) : MetaM (List MVarId) := do
  let deps ← g.getMVarDependencies
  deps.toList.filterM fun m => do return !(← m.isAssigned)

def sharedMVars (goals : List MVarId) : MetaM (List MVarId) := do
  let deps ← goals.mapM unassignedDeps
  let occursInTwo m := (deps.filter (·.contains m)).length ≥ 2
  return deps.flatten.eraseDups.filter occursInTwo

def dropMVarGoals (goals : List MVarId) : MetaM (List MVarId) :=
  goals.filterM fun g => do
    let others := goals.filter (· != g)
    return !(← others.anyM fun g' => do return (← unassignedDeps g').contains g)

def carriedSiblings
    (clusterMap : Std.HashMap StateId ClusterInfo)
    (goalMap : Std.HashMap StateId (MVarId × Elab.Term.SavedState))
    (parentId : StateId) : MetaM (List (MVarId × StateId)) := do
  match clusterMap.get? parentId with
  | none => return []
  | some ⟨members, sharedMVars⟩ =>
    if !(← sharedMVars.anyM (·.isAssigned)) then
      return []
    let siblingIds := members.filter (· != parentId)
    siblingIds.filterMapM fun sid => do
      match goalMap.get? sid with
      | none => return none
      | some (smv, _) =>
        if ← smv.isAssigned then return none else return some (smv, sid)

/--
Like `restoreState`, but *also* rewinds the name generator (and the macro-scope and
auxiliary-declaration generators) to the values captured in `s`.

`Core.SavedState.restore` deliberately restores only `env`/`messages`/`infoState` and
leaves `ngen` alone, because within a single elaboration thread the name generator only
ever moves forward, so it must not be rolled back. That assumption breaks for us: every
RPC request runs in a *fresh* `RequestM.runTermElabM` seeded from the `hoverfly`
snapshot's command state, so `ngen` is reset to the snapshot value on each call. Plain
`restoreState` then leaves `ngen` pointing *before* the `FVarId`/`MVarId`s that were
allocated (in a previous request) and baked into `s`'s metavariable context. The next
tactic re-issues those exact ids, clobbering the goal mvar and hypotheses in the restored
context — which surfaces as nonsense like `function expected ?α`. Restoring `ngen` makes
fresh allocations continue *past* everything already in `s`. -/
def restoreStateFull (s : Lean.Elab.Term.SavedState) : Lean.Elab.TermElabM Unit := do
  restoreState s
  modifyThe Core.State fun st => { st with
    ngen           := s.meta.core.ngen
    nextMacroScope := s.meta.core.nextMacroScope
    auxDeclNGen    := s.meta.core.auxDeclNGen }

@[server_rpc_method]
def getSubgoals
  (_params : GetSubgoalsParams)
  : RequestM (RequestTask ((List (List APINode)) × WithRpcRef State)) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do
      -- get counter and maps
      let {nodeCounter, goalMap, tacticMap, clusterMap}
        := _params.stateRef.val

      -- get syntax and id of parent goal for tactic
      match tacticMap.get? _params.id with
      | some (stx, parentId) =>

        -- get mvarId and proof state for parent goal of tactic
        match goalMap.get? parentId with
        | some (mvarId, proofState) =>

          -- restore proof state (including the name generator, see `restoreStateFull`)
          liftM (restoreStateFull proofState : Lean.Elab.TermElabM Unit)

          try
            -- run tactic
            let rawResult : List Lean.MVarId <- Elab.Term.withoutErrToSorry do
              run mvarId do
                evalTactic stx
            let result ← dropMVarGoals rawResult

            let copies ← carriedSiblings clusterMap goalMap parentId
            let copyOf : Std.HashMap MVarId StateId :=
              copies.foldl (fun m (smv, sid) => m.insert smv sid) ∅
            let leanOrderMap : Std.HashMap MVarId Nat :=
              (result ++ copies.map (·.1)).zipIdx.foldl
                (fun m (mv, i) => m.insert mv i) ∅
            let clusters ← getGoalClusters (result ++ copies.map (·.1))

            -- add each new goal to map and return nodes and updated counter
            let newProofState ←
              liftM (saveState : Lean.Elab.TermElabM Lean.Elab.Term.SavedState)
            let f t mvarId := match t with
              | (nodes, tempGoalMap, c) => do
                let goalPretty ← (ppGoal mvarId)
                let apiNode : APINode :=
                  {isGoal := true, id := c, display := goalPretty.pretty,
                   originalId := copyOf.get? mvarId,
                   leanOrder := (leanOrderMap.get? mvarId).getD 0}
                let goalInfo := (mvarId, newProofState)
                let newMap := tempGoalMap.insert c goalInfo
                return (apiNode :: nodes, newMap, c + 1)
            let g (t : List (List APINode)
                    × Std.HashMap StateId (MVarId × Elab.Term.SavedState)
                    × Std.HashMap StateId ClusterInfo × StateId) mvarIds :=
              match t with
              | (gss, goalMap, clusterMap, count) => do
                let (gs, newMap, newCount) ← mvarIds.foldlM f ([], goalMap, count)
                let members := gs.map (·.id)
                let info : ClusterInfo := { members, sharedMVars := ← sharedMVars mvarIds }
                let newClusterMap := members.foldl (·.insert · info) clusterMap
                return (gs :: gss, newMap, newClusterMap, newCount)
            let (goalsRev, newGoalMap, newClusterMap, newCounter) ←
              clusters.foldlM g ([], goalMap, clusterMap, nodeCounter)
            let goals := goalsRev.reverse.map (·.reverse)

            -- update state
            let newState ← WithRpcRef.mk {
                nodeCounter := newCounter
                goalMap := newGoalMap,
                tacticMap := tacticMap,
                clusterMap := newClusterMap
              }

            pure (goals, newState)
          catch e =>
            -- Surface tactic failures as a node instead of letting them escape as an
            -- uncaught JSON-RPC error (which shows up as "Uncaught (in promise)").
            let errNode : APINode := {
              isGoal := true, id := nodeCounter,
              display := s!"tactic '{stx.prettyPrint.pretty}' failed:\n\
                {← e.toMessageData.toString}"
            }
            pure ([[errNode]], _params.stateRef)
        | _ =>
          let errNode : APINode := {
              isGoal := true, id := nodeCounter,
              display := s!"Unable to find proof state for goal " ++
                s!"'{parentId}'."
            }
          -- TODO: error behavior
          pure ([[errNode]], _params.stateRef)
      | _ =>
        let errNode : APINode := {
            isGoal := true, id := nodeCounter,
            display := s!"Unable to find parent goal of tactic " ++
                s!"{_params.id}."
          }
        -- TODO: error behavior
        pure ([[errNode]], _params.stateRef)

structure GetApplicableTacticsParams where
  id : StateId
  stateRef : WithRpcRef State
  pos : Lsp.Position
  deriving RpcEncodable

-- TODO
open Syntax in
private def argTactics : (List (Name → Syntax)) :=
  let pos := (String.Pos.Raw.mk 0) -- TODO
  let info := SourceInfo.none
  let raw := (Substring.Raw.mk "todo raw" pos pos) -- TODO
  [
    fun n =>
      node info `Elab.induction #[ident info raw n []],
    fun n =>
      node info `Elab.cases #[ident info raw n []],
    fun n =>
      node info `Elab.exists #[ident info raw n []]
   ]

-- TODO
def tacticListGeneral : Elab.TermElabM (List Syntax) := do
  let tacs :=  [
    ← `(tactic | apply And.intro),
    ← `(tactic | apply Exists.intro),
    ← `(tactic | apply Nat.le_trans), -- TODO
    ← `(tactic | apply Nat.zero_le), -- TODO
    ← `(tactic | apply [Nat.sub_add_cancel]),
    ← `(tactic | assumption),
    ← `(tactic | contradiction),
    ← `(tactic | intro),
    ← `(tactic | intros),
    ← `(tactic | rfl),
    ← `(tactic | rw [Eq.comm]),
    ← `(tactic | simp_all),
    ← `(tactic | skip <;> skip <;> skip <;> skip <;> skip <;> skip),
    ← `(tactic | subst_eqs)
  ]

  return List.map Lean.TSyntax.raw tacs

-- TODO
def tacticListPalamedes : Elab.TermElabM (List Syntax) := do
  let tacs := [
      ← `(tactic | apply s_arbAtom _),
      ← `(tactic | apply s_arbBool),
      ← `(tactic | apply s_arbColor),
      ← `(tactic | apply s_arbLabel),
      ← `(tactic | apply s_arbNat),
      ← `(tactic | apply s_arbTuple),
      ← `(tactic | apply s_arbTy),
      ← `(tactic | apply s_arbUnit),
      ← `(tactic | apply (s_between (by first | aesop | omega))),
      ← `(tactic | apply s_between_partial),
      ← `(tactic | apply s_gt),
      ← `(tactic | apply s_lt_partial),
      ← `(tactic | apply s_mod2_partial),
      ← `(tactic | apply s_pick),
      ← `(tactic | apply s_pure),
      ← `(tactic | assumption),
      ← `(tactic | (goal_is_eq; apply convert (by norm_for_elements) (s_elements_partial _))),
      ← `(tactic | normalize_and_apply),
      ← `(tactic | normalize_and_apply_unfold),
      ← `(tactic | ((repeat apply duncurry); intro)),
      ← `(tactic | skip)
    ]
  return List.map Lean.TSyntax.raw tacs


@[server_rpc_method]
def getApplicableTactics
  (_params : GetApplicableTacticsParams)
  : RequestM (RequestTask ((List APINode) × WithRpcRef State)) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do
      -- get counter and maps
      let {nodeCounter, goalMap, tacticMap, clusterMap}
        := _params.stateRef.val

      -- get mvarId and proof state for goal (TODO: necessary?)
      match goalMap.get? _params.id with
      | some (mvarId, proofState) =>

        -- get all tactics


        -- let ts ← tacticListPalamedes
        let ts ← tacticListGeneral


        liftM (restoreStateFull proofState : Lean.Elab.TermElabM Unit)
        let mut tsArray := ts.toArray
        let foo := ← getLocalHyps
        let allDecls := (← getLCtx).decls.toList
        for decl? in allDecls do
          let some decl := decl? | continue
          if decl.isImplementationDetail then continue
          let declName := decl.userName
          for tac in argTactics do
            tsArray := tsArray.push (tac declName)
        let ts' := tsArray.toList


        -- run each tactic, recording the error message if it failed and whether
        -- it left the proof state unchanged
        let evalTac t :
            RequestT Elab.TermElabM (Syntax × Option String × Bool) := do
          liftM (restoreStateFull proofState : Lean.Elab.TermElabM Unit)
          /- run the tactic
            - if the tactic throws, record the error message
            - if the tactic "fails softly" (logs an error-severity message), record the error message
            - if the tactic doesn't assign or change the goal, mark it no-op -/
          let msgsBefore ←
            liftM ((do return (← getThe Core.State).messages.toList) : Elab.TermElabM _)
          try
            let goals ← Elab.Term.withoutErrToSorry do
              run mvarId do
                evalTactic t
            let newMsgs ←
              liftM ((do return (← getThe Core.State).messages.toList.drop msgsBefore.length)
                : Elab.TermElabM _)
            match newMsgs.find? (fun m => m.severity matches .error) with
            | some err => return (t, some (← err.data.toString), false)
            | none =>
              let assigned ← liftM (mvarId.isAssigned : Lean.Elab.TermElabM Bool)
              return (t, none, goals == [mvarId] && !assigned)
          catch e =>
            return (t, some (← e.toMessageData.toString), false)
        let results ← ts'.mapM evalTac
        liftM (restoreStateFull proofState : Lean.Elab.TermElabM Unit)

        let (succeedingResults, failingResults) :=
          results.partition (·.2.1.isNone)

        -- add each new tactic to map and return nodes and updated counter
        let f acc res := match acc, res with
          | (nodes, tempTacticMap, c), (stx, tacErr, noop) =>
            let apiNode : APINode :=
              {isGoal := false, id := c,
                display := s!"ts: {ts.length}, tsArray: {tsArray.size}, ts': {ts'.length}, "
                  ++ s!"allDecls: {allDecls.length}, localHyps: {foo.size}", -- TODO
                -- display := stx.prettyPrint.pretty,
                tacticError := tacErr, noop := noop}
            let tacticInfo := (stx, _params.id)
            let newMap := tempTacticMap.insert c tacticInfo
            (apiNode :: nodes, newMap, c + 1)
        let (tacticsSuccess, newTacticMapSuccess, newCounterSuccess) :=
          succeedingResults.foldl f ([], tacticMap, nodeCounter)
        let (tacticsAll, newTacticMapAll, newCounterAll) :=
          failingResults.foldl f
            (tacticsSuccess, newTacticMapSuccess, newCounterSuccess)

        -- update state (cluster membership is unchanged by tactic expansion)
        let newState ← WithRpcRef.mk {
            nodeCounter := newCounterAll
            goalMap := goalMap,
            tacticMap := newTacticMapAll,
            clusterMap := clusterMap
          }

        pure (tacticsAll, newState)
      | _ =>
        let errNode : APINode := {
            isGoal := true, id := nodeCounter,
            display := s!"Unable to find state for goal " ++
                s!"{_params.id}."
          }
        pure ([errNode], _params.stateRef) -- TODO: error behavior


@[widget_module]
def checkWidget : Widget.Module where
  javascript := include_str ".."/".lake"/"build"/"js"/"Hoverfly.js"

open scoped Json in
elab stx:"hoverfly" : tactic => do
  let rootProofState ← liftM (saveState : Lean.Elab.TermElabM _)
  let rootMVarId ← getMainGoal

  -- make API copy of root goal
  let display ← ppGoal rootMVarId
  let rootGoal : APINode :=
          {isGoal := true, id := 0, display := display.pretty'}

  -- initialize map of goal ids to MVarIds and States
  let initialGoalMap := Std.HashMap.ofList [
    (rootGoal.id, (rootMVarId, rootProofState))
    ]

  -- initialize state
  let initialState : State := {
      nodeCounter := rootGoal.id + 1,
      goalMap := initialGoalMap,
      tacticMap := ∅
    }
  let ref ← WithRpcRef.mk initialState

  let jsonRange := toJson ((← getFileMap).lspRangeOfStx? stx)

  Widget.savePanelWidgetInfo checkWidget.javascriptHash
    (do
      let jsonRoot ← rpcEncode rootGoal
      let jsonApiData ← rpcEncode ref
      pure $ json% { root: $(jsonRoot) , apiData: $(jsonApiData),
                     range: $(jsonRange) }) stx

end Backend
