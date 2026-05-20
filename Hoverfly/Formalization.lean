import Lean.Expr
import Lean.MetavarContext
import Aesop
import Hoverfly.RuleSets

def Hyp := String deriving BEq
def GoalData := String deriving BEq
def TacticData := String deriving BEq
def TermMetaVar := String deriving BEq

/-
Invariants in types:
* root is a goal
* all goals have only tactic children
* all tactics have only cluster children
* all clusters have only goal children
-/

def Set a := a -> Prop

mutual

inductive Goal : Type where -- or node
| goal (data : GoalData) (mvs : List TermMetaVar) (children : Set Tactic) : Goal -- assuming data and mvs match
deriving BEq
inductive Tactic : Type where -- and node
| tactic (data : TacticData) (children : List Cluster) : Tactic
deriving BEq
inductive Cluster : Type where -- or node
| cluster (mvs : List TermMetaVar) (children : List Goal) : Cluster
deriving BEq
end

open Goal Tactic Cluster

mutual

def checkTreeWithG (g : Goal) (checkG : Goal -> Bool) (checkT : Tactic -> Bool) (checkC : Cluster -> Bool) : Bool :=
  match g with
  | goal _ _ ts => checkG g && List.all ts (fun t => checkTreeWithT t checkG checkT checkC)
  termination_by (sizeOf g)
  decreasing_by sorry

def checkTreeWithT (t : Tactic) (checkG : Goal -> Bool) (checkT : Tactic -> Bool) (checkC : Cluster -> Bool) : Bool :=
  match t with
  | tactic _ cs => checkT t && List.all cs (fun c => checkTreeWithC c checkG checkT checkC)
  termination_by (sizeOf t)
  decreasing_by sorry

def checkTreeWithC (c : Cluster) (checkG : Goal -> Bool) (checkT : Tactic -> Bool) (checkC : Cluster -> Bool) : Bool :=
  match c with
  | cluster _ gs => checkC c && List.all gs (fun g => checkTreeWithG g checkG checkT checkC)
  termination_by (sizeOf c)
  decreasing_by sorry

end


inductive Tree : Type where
  | T (c : Cluster)

def checkTreeWith (t : Tree) (checkG : Goal -> Bool) (checkT : Tactic -> Bool) (checkC : Cluster -> Bool) : Bool :=
  match t with
  | Tree.T c => checkTreeWithC c checkG checkT checkC



def hasMVar (g : Goal) (mv : TermMetaVar) : Bool := by sorry
def tacticsForGoal (g : Goal) : List Tactic := by sorry
def subgoals (g : Goal) (t : Tactic) : List Cluster := by sorry


-- root cluster has no mvars
def rootHasNoMVars (t : Tree) : Bool := match t with
  | Tree.T (cluster mvs _) => [] == mvs

/-
* A goal appears as a grandchild of a tactic iff
    - it is a resulting subgoal from applying that tactic to its parent
    - it is in the same cluster as the parent (could make this "and one of the
      metavars of that cluster was assigned")
-/
def goalsValidForTactics (t : Tree) : Bool := by sorry

/-
well-formedness conditions for incomplete trees:
- either static rules apply for a goal, or we don't have children yet


* sets not lists (* -> Prop, define here)
* aesop trace = sequence of prefixes
-/


/-
Metavariable invariants:
* Among sibling clusters, TermMetaVar lists are disjoint.
* Among sibling clusters, a cluster has a goal as a child iff that child has a
  metavar in the cluster's list or is the metavar in the cluster's list
* Metavariables are in the same cluster list iff they are transitively
  connected by goals (or are the metavars).
* a goal has an mvar iff:
  - its closest ancestor goal had that mvar
  - the most recent tactic introduced that mvar
* every metavariable for a cluster appears as a goal (its type) in that cluster
  * when we instantiate it, we copy that goal and solve it with our value and
    then copy the rest of the cluster underneath
-/


-- correct tactics are shown for each goal
def tacticsValidForGoals (t : Tree) : Bool :=
  let checkG (g : Goal) : Bool := match g with
    | goal _ _ ts => ts.isPerm (tacticsForGoal g) && ts.isPerm (List.eraseDups ts)
  checkTreeWith t checkG (fun _ => True) (fun _ => True)


/- Experiment -/

theorem twoGtBad : ∀ (y : Fin 4), 2 >= y := by sorry
theorem zeroLtBad : ∀ (z : Fin 4), z >= 0 := by sorry

theorem twoGtZeroBad : (2 : Fin 4) >= 0 := by
  apply Fin.le_trans
  . apply zeroLtBad
  . apply twoGtBad
  . exact 3 -- this is necessary

@[aesop unsafe (rule_sets := [bad])]
theorem solve' {x : Fin 4} : (2 : Fin 4) >= 0 := by aesop

set_option trace.aesop true
theorem twoGtZeroBad' : (2 : Fin 4) >= 0 := by
  aesop
      (add unsafe 50% apply (by exact (3 : Fin 4))) -- fails without something like this
      (rule_sets := [-default, -builtin, bad])
      (config := {enableSimp := false})
