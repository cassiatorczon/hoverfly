-- import Hoverfly.Backend
import ProofWidgets

namespace API
open Lean ProofWidgets

deriving instance TypeName for Nat
deriving instance TypeName for Elab.Term.SavedState
instance [BEq α] [Hashable α] [TypeName α] [TypeName β]
  : TypeName (α × β) := by sorry
instance [BEq α] [Hashable α] [TypeName α] [TypeName β]
  : TypeName (Std.HashMap α β) := by sorry

deriving instance ToJson for String.Pos.Raw
deriving instance ToJson for Substring.Raw
deriving instance ToJson for SourceInfo
deriving instance ToJson for Syntax.Preresolved
deriving instance ToJson for Syntax

deriving instance FromJson for String.Pos.Raw
deriving instance FromJson for Substring.Raw
deriving instance FromJson for SourceInfo
deriving instance FromJson for Syntax.Preresolved
deriving instance FromJson for Syntax

mutual
structure Goal where
  stateId : Nat
  goalId : MVarId -- TODO could go in map
  display : String -- todo could go in map on the other side
  children : List Tactic
  deriving ToJson, FromJson

structure Tactic where
  stateId : Nat -- gets this from parent
  tacticName : Syntax -- TODO could go in map
  parentMVar : MVarId -- could get this from map if we put goalId there
  display : String -- todo could go in map on other side
  children : List Goal
  deriving ToJson, FromJson
end

instance : Server.RpcEncodable Goal where
  rpcEncode goal := pure (toJson goal)
  rpcDecode json := fromJson? json |>.mapError (·)

instance : Server.RpcEncodable (List Goal) where
  rpcEncode goals := pure (toJson goals)
  rpcDecode json := fromJson? json |>.mapError (·)

instance : Server.RpcEncodable Tactic where
  rpcEncode tactic := pure (toJson tactic)
  rpcDecode json := fromJson? json |>.mapError (·)

deriving instance Server.RpcEncodable for Nat

open Server in
instance [BEq α] [Hashable α] [RpcEncodable α] [RpcEncodable β]
  : RpcEncodable (Std.HashMap α β) := by sorry

open Server in
instance [BEq α] [Hashable α] [RpcEncodable α] [RpcEncodable β]
  : RpcEncodable (α × β) := by sorry

-- it could synthesize this before I added × Nat :(
open Server in
instance : RpcEncodable (WithRpcRef ((Std.HashMap Nat Elab.Term.SavedState) × Nat)) := by sorry

open Lean ProofWidgets Server

-- mutual
-- def backendGoalToAPIGoal (g : Backend.Goal) : Goal :=
--   match g with
--   | Backend.Goal.Goal id data children =>
--     {id := id, mvarId := mvarId, data := data, children := children.map (fun t => backendTacticToAPITactic t)}
-- termination_by (sizeOf g)

-- def backendTacticToAPITactic (t : Backend.Tactic) : Tactic :=
--   match t with
--   | Backend.Tactic.Tactic id data children =>
--     {id := id, data := data, children := children.map (fun g => backendGoalToAPIGoal g)}
-- termination_by (sizeOf t)
-- end

-- @[simp]
-- theorem size_of_list_tactic (x : Tactic) (l : List Tactic) (h : x ∈ l) : sizeOf x <= sizeOf l := by
--   induction l <;> simp_all
--   cases h <;> simp_all <;> omega

-- @[simp]
-- theorem size_of_list_goal (x : Goal) (l : List Goal) (h : x ∈ l) : sizeOf x <= sizeOf l := by
--   induction l <;> simp_all
--   cases h <;> simp_all <;> omega

-- mutual
-- -- set_option pp.explicit true
-- def APIGoaltoBackendGoal (g : Goal) : Backend.Goal :=
--   Backend.Goal.Goal g.id g.data (g.children.map (fun t => APITacticToBackendTactic t))
-- termination_by (sizeOf g)
-- decreasing_by
--   cases g
--   simp_all
--   rw [Nat.add_assoc]
--   rw [Nat.lt_one_add_iff]
--   apply Nat.le_add_left_of_le
--   apply size_of_list_tactic
--   assumption

-- def APITacticToBackendTactic (t : Tactic) : Backend.Tactic :=
--   Backend.Tactic.Tactic t.id t.data (t.children.map (fun g => APIGoaltoBackendGoal g))
-- termination_by (sizeOf t)
-- decreasing_by
--   cases t
--   simp_all
--   rw [Nat.add_assoc]
--   rw [Nat.add_assoc]
--   rw [Nat.lt_one_add_iff]
--   rw [← Nat.add_assoc]
--   apply Nat.le_add_left_of_le
--   apply size_of_list_goal
--   assumption

-- end

structure GetInitialStateParams where
  goals : Array Widget.InteractiveGoal --TODO
  pos : Lsp.Position --TODO
  deriving RpcEncodable

/--
Gets initial goal state.
Stores a proof state server-side and returns a reference to it.
-/
@[server_rpc_method]
def getInitialState
  (_params : GetInitialStateParams)
  : RequestM (RequestTask (Goal × WithRpcRef ((Std.HashMap Nat Elab.Term.SavedState) × Nat))) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do
      let initialGoal : Goal := --TODO
        {stateId:=0, goalId:= MVarId.mk Name.anonymous, display := "P /\\ Q", children := []} --TODO
      let initialProofState ← liftM (saveState : Lean.Elab.TermElabM _)
      let initialMap := Std.HashMap.ofList [(initialGoal.stateId, initialProofState)]
      let ref ← WithRpcRef.mk (initialMap, (1 : Nat))
      return (initialGoal, ref)


structure GetSubgoalsParams where
  t : Tactic
  statesRef : WithRpcRef ((Std.HashMap Nat Elab.Term.SavedState) × Nat)
  pos : Lsp.Position
  deriving RpcEncodable

@[server_rpc_method]
def getSubgoals
  (_params : GetSubgoalsParams)
  : RequestM (RequestTask ((List Goal) × (WithRpcRef ((Std.HashMap Nat Elab.Term.SavedState) × Nat)))) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do
      let t := _params.t
      let (stateMap, counter) := _params.statesRef.val
      match stateMap.get? t.stateId with
      | some proofState =>
        liftM (restoreState proofState : Lean.Elab.TermElabM Unit)
        let result : List Lean.MVarId <- Lean.Elab.Tactic.run t.parentMVar do
          Lean.Elab.Tactic.evalTactic t.tacticName
        let newProofState ← liftM (saveState : Lean.Elab.TermElabM Lean.Elab.Term.SavedState)
        let comb p mvarId := match p with
          | (gs, c) =>
            let g : Goal := {stateId := c, goalId := mvarId, display := "todo", children := []}
            (g :: gs, c + 1)
        let (goals, newCounter) := result.foldl comb ([], counter)
        let newStateMap
          := goals.foldl (fun map goal => map.insert goal.stateId newProofState) stateMap
        let newState ← WithRpcRef.mk (newStateMap, newCounter)
        pure (goals, newState)
      | _ => pure ([], _params.statesRef) -- TODO: error behavior

structure GetApplicableTacticsParams where
  g : Goal
  statesRef : WithRpcRef (Std.HashMap Nat Elab.Term.SavedState)
  pos : Lsp.Position
  deriving RpcEncodable

@[server_rpc_method]
def getApplicableTactics
  (_params : GetApplicableTacticsParams)
  : RequestM (RequestTask (List Tactic)) :=
  RequestM.withWaitFindSnapAtPos _params.pos fun snap => do
    RequestM.runTermElabM snap do
      let ts := by sorry
      pure $ ts

-- --TODO
-- @[server_rpc_method]
-- def temporaryTest (_ : String): RequestM (RequestTask String) :=
--   RequestM.pureTask $ pure $ Backend.temporaryTest

@[widget_module]
def checkWidget : Widget.Module where
  javascript := include_str ".."/".lake"/"build"/"js"/"Hoverfly.js"

-- open scoped Json in
-- elab stx:"myWidgetTactic" : tactic => do
--   let some tacticRange := (← getFileMap).lspRangeOfStx? stx | return
--   Widget.savePanelWidgetInfo checkWidget.javascriptHash
--     (pure $ json% { tacticRange: $(tacticRange) }) stx



-- open Lean.Elab.Tactic in
-- def myTactic : Tactic := λ stx => do
--   -- let env <- getEnv
--   let g <- Elab.Tactic.getMainGoal -- means myTactic must
--   g.withContext do

-- --   return

-- theorem foobar : P ∧ Q -> P := by
--   skip
--   skip
--   myWidgetTactic
--   sorry

end API
