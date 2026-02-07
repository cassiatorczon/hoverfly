import ProofWidgets
import Hoverfly.Backend

namespace API
open Lean ProofWidgets

instance : ToJson String := inferInstanceAs (ToJson String)
instance : FromJson String := inferInstanceAs (FromJson String)

instance : ToJson String := inferInstanceAs (ToJson String)
instance : FromJson String := inferInstanceAs (FromJson String)

mutual
structure Goal where
  id : String -- TODO type
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
  rw [Nat.add_assoc]
  rw [Nat.lt_one_add_iff]
  rw [← Nat.add_assoc]
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

-- TODO arg
@[server_rpc_method]
def getInitialState (_ : String) : RequestM (RequestTask Goal) :=
  -- TODO
  RequestM.asTask $ pure $
   backendGoalToAPIGoal (Backend.getInitialState "")

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

#widget checkWidget


namespace API
