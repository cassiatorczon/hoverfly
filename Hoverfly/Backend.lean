import ProofWidgets

namespace Backend
open Lean ProofWidgets Server

deriving instance TypeName for Nat
deriving instance TypeName for Elab.Term.SavedState

-- TODO can we make this not unsafe
unsafe instance [TypeName α] [TypeName β]
  : TypeName (α × β) :=
  TypeName.mk (α × β) (`Prod ++ TypeName.typeName α ++ TypeName.typeName β)

-- TODO can we make this not unsafe
unsafe instance [BEq α] [Hashable α] [TypeName α] [TypeName β]
  : TypeName (Std.HashMap α β) :=
  TypeName.mk (Std.HashMap α β) (`Std.HashMap ++ TypeName.typeName α ++ TypeName.typeName β)

def StateId := Nat
  deriving OfNat, BEq, Hashable, ToJson, FromJson, HAdd

structure State where
  nodeCounter : StateId := 0
  goalMap : Std.HashMap StateId (MVarId × Elab.Term.SavedState) := ∅
  tacticMap : Std.HashMap StateId (Syntax × StateId) := ∅
  deriving TypeName

structure APINode where
  id : StateId
  display : String
  deriving ToJson, FromJson

structure GetInitialStateParams where
  -- goals : Array Widget.InteractiveGoal --TODO
  goal : Widget.InteractiveGoal
  pos : Lsp.Position --TODO
  deriving RpcEncodable

/--
Gets initial goal state.
Stores a proof state server-side and returns a reference to it.
-/
@[server_rpc_method]
def getInitialState
  (_params : GetInitialStateParams)
  : RequestM (RequestTask (APINode × WithRpcRef State)) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do

      -- get root goal API info
      let display : String := toString _params.goal.pretty
      let rootGoal : APINode := {id := 0, display := display}

      -- get proof state and mvarId at root goal
      let rootProofState ← liftM (saveState : Lean.Elab.TermElabM _)
      let rootMVarId := _params.goal.mvarId

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
      return (rootGoal, ref)


structure GetSubgoalsParams where
  id : StateId
  stateRef : WithRpcRef State
  pos : Lsp.Position
  deriving RpcEncodable

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
          let newProofState ← liftM (saveState : Lean.Elab.TermElabM Lean.Elab.Term.SavedState)
          let f t mvarId := match t with
            | (nodes, tempGoalMap, c) =>
              let apiNode : APINode := {id := c, display :="todo"}
              let goalInfo := (mvarId, newProofState)
              let newMap := tempGoalMap.insert c goalInfo
              (apiNode :: nodes, newMap, c + 1)
          let (goals, newGoalMap, newCounter) := result.foldl f ([], goalMap, nodeCounter)

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
        let ts : List Syntax := by sorry

        -- add each new tactic to map and return nodes and updated counter
        let f t stx := match t with
          | (nodes, tempTacticMap, c) =>
            let apiNode : APINode := {id := c, display :="todo"}
            let tacticInfo := (stx, _params.id)
            let newMap := tempTacticMap.insert c tacticInfo
            (apiNode :: nodes, newMap, c + 1)
        let (tactics, newTacticMap, newCounter) := ts.foldl f ([], tacticMap, nodeCounter)

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

-- open Lean.Elab.Tactic in
-- def myTactic : Tactic := λ stx => do
--   -- let env <- getEnv
--   let g <- Elab.Tactic.getMainGoal -- means myTactic must
--   g.withContext do

-- --   return

-- open scoped Json in
-- elab stx:"myWidgetTactic" : tactic => do
--   let some tacticRange := (← getFileMap).lspRangeOfStx? stx | return
--   Widget.savePanelWidgetInfo checkWidget.javascriptHash
--     (pure $ json% { tacticRange: $(tacticRange) }) stx

-- theorem foobar : P ∧ Q -> P := by
--   skip
--   skip
--   myWidgetTactic
--   sorry

end Backend
