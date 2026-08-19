import ProofWidgets
import Hoverfly.Attribute

namespace Backend
open Lean Lean.Meta Lean.Elab.Tactic
open ProofWidgets Server
open State MVar FunTac Util TacticUtil

structure APINode where
  isGoal : Bool
  id : StateId
  display : String
  tacticError : Option String := none
  noop : Bool := false
  solvesGoal : Bool := false -- todo: maybe make this and noop an enum?
  originalId : Option StateId := none
  leanOrder : Nat := 0
  sharedMVars : List String := []
  deriving ToJson, FromJson

structure GetSubgoalsParams where
  id : StateId
  stateRef : WithRpcRef State.State
  pos : Lsp.Position
  deriving RpcEncodable


@[server_rpc_method]
def getSubgoals
  (_params : GetSubgoalsParams)
  : RequestM (RequestTask ((List (List APINode)) × WithRpcRef State.State)) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do
      -- get counter and maps
      let {allTactics, nodeCounter, goalMap, tacticMap, clusterMap}
        := _params.stateRef.val

      -- get syntax and id of parent goal for tactic
      match tacticMap.get? _params.id with
      | some (tacOutput, parentId) =>

        -- check that the parent goal is known
        match goalMap.get? parentId with
        | some _ =>

          -- restore proof state (including the name generator, see `restoreStateFull`) from the state after running the tactic
          liftM (restoreStateFull tacOutput.postState : Lean.Elab.TermElabM Unit)

          try
            -- run tactic
            let rawResult := tacOutput.goals
            let result ← dropMVarGoals rawResult

            -- copy entangled siblings
            let copies ← carriedSiblings clusterMap goalMap parentId
            let copyOf : Std.HashMap MVarId StateId :=
              copies.foldl (fun m (smv, sid) => m.insert smv sid) ∅
            let leanOrderMap : Std.HashMap MVarId Nat :=
              (result ++ copies.map (·.1)).zipIdx.foldl
                (fun m (mv, i) => m.insert mv i) ∅
            let clusters ← getGoalClusters (result ++ copies.map (·.1))

            -- entangled sibling handling may have touched the state, so save
            -- the current one rather than reusing `tacOutput.postState`
            let newProofState ←
              liftM (saveState : Lean.Elab.TermElabM Lean.Elab.Term.SavedState)

            -- add each new goal to map and return nodes and updated counter
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
                let shared ← sharedMVars mvarIds
                let info : ClusterInfo := { members, sharedMVars := shared }
                let newClusterMap := members.foldl (·.insert · info) clusterMap
                let sharedNames ← shared.mapM fun m =>
                  return (← ppExpr (mkMVar m)).pretty
                let gs := gs.map ({ · with sharedMVars := sharedNames })
                return (gs :: gss, newMap, newClusterMap, newCount)
            let (goalsRev, newGoalMap, newClusterMap, newCounter) ←
              clusters.foldlM g ([], goalMap, clusterMap, nodeCounter)
            let goals := goalsRev.reverse.map (·.reverse)

            -- update state
            let newState ← WithRpcRef.mk {
                allTactics := allTactics,
                nodeCounter := newCounter,
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
              display := s!"tactic '{tacOutput.stx.prettyPrint.pretty}' failed:\n\
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
  stateRef : WithRpcRef State.State
  pos : Lsp.Position
  deriving RpcEncodable

-- TODO
def nameToString (n : Name) : String :=
  n.toString
  -- match n with
  -- | .str _ s => s
  -- | .num p i => p.toString
  -- | _ => "?"


@[server_rpc_method]
def getApplicableTactics
  (_params : GetApplicableTacticsParams)
  : RequestM (RequestTask ((List (List APINode)) × WithRpcRef State.State)) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do
      -- get all tactics, counter, and maps
      let {allTactics, nodeCounter, goalMap, tacticMap, clusterMap}
        := _params.stateRef.val

      -- get mvarId and proof state for goal
      match goalMap.get? _params.id with
      | some (mvarId, proofState) =>
        let tacInput : TacInput := {goal:=mvarId, savedState:=proofState}
        let results ← allTactics.mapM (fun t => t tacInput)
        liftM (restoreStateFull proofState : Lean.Elab.TermElabM Unit)

        -- add each new tactic to map and get list of api nodes and updated counter
        let mut tacListList := []
        let mut counter := nodeCounter
        let mut tacMap := tacticMap
        for resList in results do
          let mut tacList := []
          for result@{stx, goals, display, isNoop, solvesGoal, postState, error} in resList do
            let tacErr :=
              if isErrTacOutput result then
                some (error.getD "tactic left no goals without closing the goal")
              else none
            let apiNode : APINode :=
              {isGoal := false, id := counter,
                display := display,
                tacticError := tacErr,
                noop := isNoop, solvesGoal := solvesGoal}
            tacList := apiNode :: tacList
            tacMap := tacMap.insert counter (result, _params.id)
            counter := counter + 1
          tacListList := tacList :: tacListList

        -- update state (cluster membership is unchanged by tactic expansion)
        let newState ← WithRpcRef.mk {
            allTactics := allTactics
            nodeCounter := counter
            goalMap := goalMap,
            tacticMap := tacMap,
            clusterMap := clusterMap
          }

        pure (tacListList, newState)
      | _ =>
        let errNode : APINode := {
            isGoal := true, id := nodeCounter,
            display := s!"Unable to find state for goal " ++
                s!"{_params.id}."
          }
        pure ([[errNode]], _params.stateRef) -- TODO: error behavior


@[widget_module]
def checkWidget : Widget.Module where
  javascript := include_str ".."/"src"/"assets"/"js"/"Hoverfly.js"

open scoped Json in
elab stx:"hoverfly" : tactic => do
  let lemmaApps ← (hoverflyLemmas (← getEnv)).mapM fun n =>
    `(tactic| apply $(mkIdent (`_root_ ++ n)):term)
  let tacs := (hoverflyTactics (← getEnv)).toList

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
  let initialState : State.State := {
      allTactics := tacs ++
        (lemmaApps.toList.map (fun t => tacticToFunTac t.raw)) -- TODO, we need the rest
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
  let sorryTac ← `(tactic | sorry)
  evalTactic (TSyntax.raw sorryTac)

end Backend
