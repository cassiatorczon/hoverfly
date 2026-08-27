module

public import Hoverfly.FunTac
public import Lean.Data.Json.FromToJson.Basic
public import Lean.Elab.Term.TermElabM
public import Std.Data.HashMap.Basic

open Lean Elab FunTac

namespace State

-- TODO: this name has gotten confusing. state of what when
@[expose]
public def StateId := Nat
  deriving OfNat, BEq, Hashable, ToJson, FromJson, HAdd, ToString

/-
Clusters of goals that transitively share unassigned metavariables.

E.g., if we had four goals with unassigned mvar dependencies as follows:
* g0 depends on ?x
* g1 depends on ?x and ?y
* g2 depends on ?y
* g3 depends on ?z
* g4 depends on no mvars
then there would be three clusters with member lists:
* [g0, g1, g2]
* [g3]
* [g4]
.
"Transitive" above means that because g0 shares an mvar with g1 and g1 shares
an mvar with g2, g0 and g2 also end up in the same cluster.
-/
public structure ClusterInfo where
  members : List StateId -- IDs for states corresponding to goals in the cluster
  sharedMVars : List MVarId -- mvars transitively shared by goals in the cluster

public structure State where
  /- all proto-tactics available to the widget -/
  allTactics : List FunTac
  /- the number of nodes so far and also the ID for the next node to be created -/
  nodeCounter : StateId := 0
  /- a map of state IDs to their corresponding goals and proof states at those goals -/
  goalMap : Std.HashMap StateId (MVarId × Term.SavedState) := ∅
  /- a map of state IDs to corresponding tactic application results and parent goal IDs -/
  tacticMap : Std.HashMap StateId (TacOutput × StateId) := ∅
  /- a map of state IDs to the metavariable clusters containing the corresponding goals -/
  clusterMap : Std.HashMap StateId ClusterInfo := ∅
  deriving TypeName

end State
