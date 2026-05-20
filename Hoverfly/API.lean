import Hoverfly.Backend
import ProofWidgets

namespace API
open Lean ProofWidgets

def GoalId := MVarId
deriving ToJson, FromJson

mutual
structure Goal where
  id : GoalId -- TODO type
  -- state: Lean.Elab.Tactic.SavedState
  data : String -- TODO type
  children : List Tactic
  deriving ToJson, FromJson

structure Tactic where
  id : String
  data : String
  children : List Goal
  deriving ToJson, FromJson
end

instance : Server.RpcEncodable Goal where
  rpcEncode goal := pure (toJson goal)
  rpcDecode json := fromJson? json |>.mapError (·)

instance : Server.RpcEncodable Tactic where
  rpcEncode tactic := pure (toJson tactic)
  rpcDecode json := fromJson? json |>.mapError (·)

open Lean ProofWidgets Server

mutual
def backendGoalToAPIGoal (g : Backend.Goal) : Goal :=
  match g with
  | Backend.Goal.Goal id data children =>
    {id := id, data := data, children := children.map (fun t => backendTacticToAPITactic t)}
termination_by (sizeOf g)

def backendTacticToAPITactic (t : Backend.Tactic) : Tactic :=
  match t with
  | Backend.Tactic.Tactic id data children =>
    {id := id, data := data, children := children.map (fun g => backendGoalToAPIGoal g)}
termination_by (sizeOf t)
end

@[simp]
theorem size_of_list_tactic (x : Tactic) (l : List Tactic) (h : x ∈ l) : sizeOf x <= sizeOf l := by
  induction l <;> simp_all
  cases h <;> simp_all <;> omega

@[simp]
theorem size_of_list_goal (x : Goal) (l : List Goal) (h : x ∈ l) : sizeOf x <= sizeOf l := by
  induction l <;> simp_all
  cases h <;> simp_all <;> omega

mutual
-- set_option pp.explicit true
def APIGoaltoBackendGoal (g : Goal) : Backend.Goal :=
  Backend.Goal.Goal g.id g.data (g.children.map (fun t => APITacticToBackendTactic t))
termination_by (sizeOf g)
decreasing_by
  cases g
  simp_all
  rw [Nat.add_assoc]
  rw [Nat.lt_one_add_iff]
  apply Nat.le_add_left_of_le
  apply size_of_list_tactic
  assumption

def APITacticToBackendTactic (t : Tactic) : Backend.Tactic :=
  Backend.Tactic.Tactic t.id t.data (t.children.map (fun g => APIGoaltoBackendGoal g))
termination_by (sizeOf t)
decreasing_by
  cases t
  simp_all
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.lt_one_add_iff]
  rw [← Nat.add_assoc]
  apply Nat.le_add_left_of_le
  apply size_of_list_goal
  assumption

end

structure GetInitialStateParams where
  goals : Array Widget.InteractiveGoal
  deriving RpcEncodable

-- TODO arg
@[server_rpc_method]
def getInitialState (_params : GetInitialStateParams) : RequestM (RequestTask Goal) :=
  -- TODO
  RequestM.asTask $ do
    return backendGoalToAPIGoal (Backend.getInitialState "")

open Server RequestM in
def getApplicableTactics'
  (pos : Lsp.Position) -- root position
  (root : Goal)
  (current : Goal)
  : RequestM (RequestTask Unit) := do
  withWaitFindSnapAtPos pos fun snap => do
    -- Get the elaboration state
    RequestM.runTermElabM snap do
      -- Run a tactic
      let result : List Lean.MVarId <- Lean.Elab.Tactic.run root.id do
        Lean.Elab.Tactic.evalTactic (← `(tactic | skip))
      return ()

@[server_rpc_method]
def getSubgoals (t : Tactic) : RequestM (RequestTask (List Goal)) :=
  -- TODO
  let tB := APITacticToBackendTactic t
  let gsB := Backend.getSubgoals tB
  let gs := gsB.map (fun g => backendGoalToAPIGoal g)
  RequestM.pureTask $ pure $ gs

@[server_rpc_method]
def getApplicableTactics (g : Goal) : RequestM (RequestTask (List Tactic)) :=
  -- TODO
  let gB := APIGoaltoBackendGoal g
  let tsB := Backend.getApplicableTactics gB
  let ts := tsB.map (fun t => backendTacticToAPITactic t)
  RequestM.pureTask $ pure $ ts

--TODO
@[server_rpc_method]
def temporaryTest (_ : String): RequestM (RequestTask String) :=
  RequestM.pureTask $ pure $ Backend.temporaryTest

@[widget_module]
def checkWidget : Widget.Module where
  javascript := include_str ".."/".lake"/"build"/"js"/"Hoverfly.js"

open scoped Json in
elab stx:"myWidgetTactic" : tactic => do
  let some tacticRange := (← getFileMap).lspRangeOfStx? stx | return
  Widget.savePanelWidgetInfo checkWidget.javascriptHash
    (pure $ json% { tacticRange: $(tacticRange) }) stx



-- open Lean.Elab.Tactic in
-- def myTactic : Tactic := λ stx => do
--   -- let env <- getEnv
--   let g <- Elab.Tactic.getMainGoal -- means myTactic must
--   g.withContext do

--   return

theorem foobar : P ∧ Q -> P := by
  skip
  skip
  myWidgetTactic
  sorry

end API
