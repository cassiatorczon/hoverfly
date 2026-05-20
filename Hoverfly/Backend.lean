import Lean.Expr
namespace Internal

-- TODO
def temporaryTest : String := ""

end Internal

namespace Backend
open Lean

def GoalId := MVarId

mutual

inductive Goal : Type where
| Goal (id : MVarId) (data : String) (children : List Tactic) : Goal
  --(goalRange : Range)
inductive Tactic : Type where
| Tactic (id : String) (data : String) (children : List Goal) : Tactic

end

--TODO
def t0 := Tactic.Tactic "t0" "split" []
def t1 := Tactic.Tactic "t1" "id" []
def t2 := Tactic.Tactic "t2" "exact P" []
def t3 := Tactic.Tactic "t3" "exact Q" []
def g0 := Goal.Goal {name:=Lean.Name.mkSimple "g0"} "P /\\ Q" [t0, t1]
def g1 := Goal.Goal {name:=Lean.Name.mkSimple "g1"} "P" []
def g2 := Goal.Goal {name:=Lean.Name.mkSimple "g2"} "Q" []
def g3 := Goal.Goal {name:=Lean.Name.mkSimple "g3"} "P /\\ Q" []

-- TODO
def getInitialState (_ : String) : Goal := g0

def getSubgoals (t : Tactic) : List Goal :=
  match t with
  | Tactic.Tactic "t0" _ _ =>
    [g1, g2]
  | Tactic.Tactic "t1" _ _ => [g3]
  | Tactic.Tactic "t2" _ _ => []
  | Tactic.Tactic "t3" _ _ => []
  | _ => []

def getApplicableTactics (g : Goal) : List Tactic :=
  match g with
  | Goal.Goal n _ _ =>
    if n.name.eqStr "g0"
    then [t0,t1]
    else if n.name.eqStr "g1"
      then [t2]
      else if n.name.eqStr "g2"
        then [t3]
        else if n.name.eqStr "g3"
        then []
        else []

-- TODO
def temporaryTest : String :=
  Internal.temporaryTest



end Backend

-- TODO: may delete Sizing section

namespace Sizing
open Backend

@[simp]
theorem size_of_list_tactic (x : Tactic) (l : List Tactic) (h : x ∈ l) : sizeOf x <= sizeOf l := by
  induction l <;> simp_all
  cases h <;> simp_all <;> omega

@[simp]
theorem size_of_list_goal (x : Goal) (l : List Goal) (h : x ∈ l) : sizeOf x <= sizeOf l := by
  induction l <;> simp_all
  cases h <;> simp_all <;> omega

mutual

def sizeGoal (g : Goal) : Nat :=
  match g with
  | Goal.Goal _ _ cs =>
      cs.foldl (fun acc t => acc + sizeTactic t) 1
termination_by sizeOf g
decreasing_by
  simp_all
  have ht : sizeOf t <= sizeOf cs := by simp_all
  omega

def sizeTactic (t : Tactic) : Nat :=
  match t with
  | Tactic.Tactic _ _ cs =>
      cs.foldl (fun acc g => acc + sizeGoal g) 1
termination_by sizeOf t
decreasing_by
  simp_all
  have hg : sizeOf g <= sizeOf cs := by simp_all
  omega

end

mutual

@[simp]
def depthGoal (g : Goal) : Nat :=
  match g with
  | Goal.Goal _ _ cs =>
      let depths := cs.map (fun t => depthTactic t)
      match h : depths with
      | [] => 1
      | t :: ts => 1 + (List.max depths (by simp_all))
termination_by sizeOf g
decreasing_by
  simp_all
  have ht : sizeOf t <= sizeOf cs := by simp_all
  omega

@[simp]
def depthTactic (t : Tactic) : Nat :=
  match t with
  | Tactic.Tactic _ _ cs =>
      let depths := cs.map (fun g => depthGoal g)
      match h : depths with
      | [] => 1
      | g :: gs => 1 + (List.max depths (by simp_all))
termination_by sizeOf t
decreasing_by
  simp_all
  have hg : sizeOf g <= sizeOf cs := by simp_all
  omega
end

@[simp]
theorem depth_decreasing_goal
  (id : GoalId)
  (data : String)
  (t : Tactic)
  (ts : List Tactic) :
  t ∈ ts →
  depthTactic t < depthGoal (Goal.Goal id data ts) := by
  intros h
  unfold depthGoal
  cases ts <;> simp_all
  conv =>
    rhs
    rhs
    simp [← List.map_cons]
  rw [Nat.add_comm]
  rw [← List.mem_cons] at h
  apply Nat.lt_add_one_of_le
  apply List.le_max_of_mem
  apply List.mem_map_of_mem
  assumption

@[simp]
theorem depth_decreasing_tactic
  (id : String)
  (data : String)
  (g : Goal)
  (gs  : List Goal) :
  g ∈ gs  →
  depthGoal g < depthTactic (Tactic.Tactic id data gs) := by
  intros h
  unfold depthTactic
  cases gs  <;> simp_all
  conv =>
    rhs
    rhs
    simp [← List.map_cons]
  rw [Nat.add_comm]
  rw [← List.mem_cons] at h
  apply Nat.lt_add_one_of_le
  apply List.le_max_of_mem
  apply List.mem_map_of_mem
  assumption

end Sizing


theorem foo (x : Int) :
  match x with
  | 0 => False /\ False
  | _ => False /\ False := by
  split
  case h_1 =>
    apply And.intro
    case left => sorry
    case right => sorry
  case h_2 => sorry
