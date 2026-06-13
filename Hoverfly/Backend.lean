import ProofWidgets

namespace Backend
open Lean ProofWidgets Server

def StateId := Nat
  deriving OfNat, BEq, Hashable, ToJson, FromJson, HAdd

structure State where
  nodeCounter : StateId := 0
  goalMap : Std.HashMap StateId (MVarId × Elab.Term.SavedState) := ∅
  tacticMap : Std.HashMap StateId (Syntax × StateId) := ∅
  deriving TypeName

structure APINode where
  isGoal : Bool
  id : StateId
  display : String
  deriving ToJson, FromJson

structure GetSubgoalsParams where
  id : StateId
  stateRef : WithRpcRef State
  pos : Lsp.Position
  deriving RpcEncodable

-- TODO there's got to be a better function for this already
def showGoal (mvarId : MVarId) : MetaM String := do
  let ppCtxt : PPContext := {
    env := (← getEnv),
    mctx := (← getMCtx),
    lctx := (← getLCtx),
    opts := (← getOptions),
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
    }
  let format ← ppGoal ppCtxt mvarId
  return format.pretty

@[server_rpc_method]
def getSubgoals
  (_params : GetSubgoalsParams)
  : RequestM (RequestTask ((List APINode) × WithRpcRef State)) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do
      -- get counter and maps
      let {nodeCounter, goalMap, tacticMap}
        := _params.stateRef.val

      -- get syntax and id of parent goal for tactic
      match tacticMap.get? _params.id with
      | some (stx, parentId) =>

        -- get mvarId and proof state for parent goal of tactic
        match goalMap.get? parentId with
        | some (mvarId, proofState) =>

          -- restore proof state for parent goal of tactic
          liftM (restoreState proofState : Lean.Elab.TermElabM Unit)

          -- run tactic
          let result : List Lean.MVarId <- Lean.Elab.Tactic.run mvarId do
            Lean.Elab.Tactic.evalTactic stx

          -- add each new goal to map and return nodes and updated counter
          let newProofState ←
            liftM (saveState : Lean.Elab.TermElabM Lean.Elab.Term.SavedState)
          let f t mvarId := match t with
            | (nodes, tempGoalMap, c) => do
              let goalPretty ← showGoal mvarId
              let apiNode : APINode :=
                {isGoal := true, id := c, display := goalPretty}
              let goalInfo := (mvarId, newProofState)
              let newMap := tempGoalMap.insert c goalInfo
              return (apiNode :: nodes, newMap, c + 1)
          let (goals, newGoalMap, newCounter) ←
            result.foldlM f ([], goalMap, nodeCounter)

          -- update state
          let newState ← WithRpcRef.mk {
              nodeCounter := newCounter
              goalMap := newGoalMap,
              tacticMap := tacticMap
            }

          pure (goals, newState)
        | _ => pure ([], _params.stateRef) -- TODO: error behavior
      | _ => pure ([], _params.stateRef) -- TODO: error behavior

structure GetApplicableTacticsParams where
  id : StateId
  stateRef : WithRpcRef State
  pos : Lsp.Position
  deriving RpcEncodable

-- TODO
def tacticList : Elab.TermElabM (List Syntax) := do
  let tac_rfl ← `(tactic | rfl) --TODO
  let tac_and ← `(tactic | apply And.intro)
  let tac_intros ← `(tactic | intros)
  let tac_assumption ← `(tactic | assumption)
  let tac_contradiction ← `(tactic | contradiction)

  let tac_simp_all ← `(tactic | simp_all)
  let tac_very_long ← `(tactic | skip <;> skip <;> skip <;> skip <;> skip <;> skip)

  let tac_subst_eqs ← `(tactic | subst_eqs)
  let tac_intro ← `(tactic | intro)
  let tac_rw_eq_comm ← `(tactic | rw [Eq.comm])

  return List.map Lean.TSyntax.raw
    [tac_rfl, tac_and, tac_intros, tac_assumption, tac_contradiction,
      tac_simp_all, tac_very_long, tac_subst_eqs, tac_intro, tac_rw_eq_comm
    ]

@[server_rpc_method]
def getApplicableTactics
  (_params : GetApplicableTacticsParams)
  : RequestM (RequestTask ((List APINode) × WithRpcRef State)) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do
      -- get counter and maps
      let {nodeCounter, goalMap, tacticMap}
        := _params.stateRef.val

      -- get mvarId and proof state for goal (TODO: necessary?)
      match goalMap.get? _params.id with
      | some (mvarId, proofState) =>

        -- get all tactics
        let ts ← tacticList

        -- filter for tactics that don't fail on the goal
        let succeeds t : RequestT Elab.TermElabM Bool := do
          liftM (restoreState proofState : Lean.Elab.TermElabM Unit)

          -- run tactic
          try
            let _ <- Lean.Elab.Tactic.run mvarId do
              Lean.Elab.Tactic.evalTactic t
            return true
          catch _ => return false
        let succeedingTactics ← List.filterM succeeds ts
        liftM (restoreState proofState : Lean.Elab.TermElabM Unit)

        -- add each new tactic to map and return nodes and updated counter
        let f t stx := match t with
          | (nodes, tempTacticMap, c) =>
            let apiNode : APINode :=
              {isGoal := false, id := c, display := stx.prettyPrint.pretty}
            let tacticInfo := (stx, _params.id)
            let newMap := tempTacticMap.insert c tacticInfo
            (apiNode :: nodes, newMap, c + 1)
        let (tactics, newTacticMap, newCounter) :=
          succeedingTactics.foldl f ([], tacticMap, nodeCounter)

        -- update state
        let newState ← WithRpcRef.mk {
            nodeCounter := newCounter
            goalMap := goalMap,
            tacticMap := newTacticMap
          }

        pure (tactics, newState)
      | _ => pure ([], _params.stateRef) -- TODO: error behavior


@[widget_module]
def checkWidget : Widget.Module where
  javascript := include_str ".."/".lake"/"build"/"js"/"Hoverfly.js"

open scoped Json in
elab stx:"hoverfly" : tactic => do
  let rootProofState ← liftM (saveState : Lean.Elab.TermElabM _)
  let rootMVarId ← Elab.Tactic.getMainGoal

  -- make API copy of root goal
  let display ← Meta.ppGoal rootMVarId
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

  Widget.savePanelWidgetInfo checkWidget.javascriptHash
    (do
      let jsonRoot ← rpcEncode rootGoal
      let jsonApiData ← rpcEncode ref
      pure $ json% { root: $(jsonRoot) , apiData: $(jsonApiData) }) stx

theorem foobar : 1 = 1 /\ 2 = 2 := by
  hoverfly
  sorry

theorem demo_simple (very_very_long_variable_name : Nat) :
  very_very_long_variable_name = 1 ->
  ¬(very_very_long_variable_name = 2) /\ 1 = very_very_long_variable_name := by
  hoverfly
  sorry

theorem demo (n m : Nat) : n <= m → ∃ x, m = x + n := by
  sorry
-- Proof 0:
  -- intros
  -- exists (m - n)
  -- rw [Nat.sub_add_cancel]
  -- assumption
-- Proof 1:
  -- apply Nat.exists_eq_add_of_le'
-- Proof 2:
  --  intros
  --  apply Nat.exists_eq_add_of_le'
  --  assumption
-- Proof 2:
  -- revert m
  -- induction n
  -- case zero =>
  --   intro m h
  --   exists m
  -- case succ n' h =>
  --   intro m hn'm
  --   cases m
  --   case zero => contradiction
  --   case succ m' =>
  --     specialize h m'
  --     have h' := Nat.le_of_add_le_add_right hn'm
  --     have ⟨x, h⟩ := h h'
  --     exists x
  --     rw [←Nat.add_assoc, Nat.add_one_inj]
  --     assumption

end Backend
