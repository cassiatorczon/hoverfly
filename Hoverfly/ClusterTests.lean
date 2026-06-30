import Hoverfly.Backend

/-!
# Tests for `Backend.getGoalClusters`

This file is not imported by the library; run `lake build Hoverfly/ClusterTests.lean` to run.
-/

open Lean Lean.Meta Lean.Elab.Command Backend

namespace Backend.ClusterTests

private def natMVar : MetaM MVarId := do
  return (← mkFreshExprMVar (mkConst ``Nat)).mvarId!

private def eqGoal (lhs rhs : Expr) : MetaM MVarId := do
  return (← mkFreshExprMVar (← mkAppM ``Eq #[lhs, rhs])).mvarId!

/-- Checks if `a` and `b` appear together in some cluster of `cs`. -/
private def sameCluster (cs : List (List MVarId)) (a b : MVarId) : Bool :=
  cs.any fun c => c.contains a && c.contains b

private def expectCount (label : String) (cs : List (List MVarId)) (n : Nat) :
    MetaM Unit := do
  unless cs.length == n do
    throwError "{label}: expected {n} cluster(s), got {cs.length}: \
      {cs.map (·.map (·.name))}"

/- Transitive chain: `?b = 0`, `?b = ?c`, `?c = 1` form one cluster. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let c ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkMVar c)
  let g3 ← eqGoal (mkMVar c) (mkNatLit 1)
  let cs ← getGoalClusters [g1, g2, g3]
  expectCount "transitive chain" cs 1
  unless sameCluster cs g1 g3 do
    throwError "transitive chain: g1 and g3 should be transitively clustered"

/- Independent goals (`?b = 0`, `?c = 1`) form two singleton clusters. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let c ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar c) (mkNatLit 1)
  let cs ← getGoalClusters [g1, g2]
  expectCount "independent" cs 2
  if sameCluster cs g1 g2 then
    throwError "independent: g1 and g2 must not be clustered"

/- Directly shared metavariable: `?b = 0`, `?b = 1` form one cluster. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkNatLit 1)
  let cs ← getGoalClusters [g1, g2]
  expectCount "shared mvar" cs 1
  unless sameCluster cs g1 g2 do
    throwError "shared mvar: g1 and g2 should be clustered"

/- Two disjoint clusters: `{?b=0, ?b=1}` and `{?c=0, ?c=1}`. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let c ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkNatLit 1)
  let g3 ← eqGoal (mkMVar c) (mkNatLit 0)
  let g4 ← eqGoal (mkMVar c) (mkNatLit 1)
  let cs ← getGoalClusters [g1, g2, g3, g4]
  expectCount "two clusters" cs 2
  unless sameCluster cs g1 g2 && sameCluster cs g3 g4 do
    throwError "two clusters: each shared pair should be together"
  if sameCluster cs g1 g3 then
    throwError "two clusters: g1 and g3 must not be clustered"

/- Assigning the mvar breaks the clusters. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkNatLit 1)
  b.assign (mkNatLit 5)
  let cs ← getGoalClusters [g1, g2]
  expectCount "assigned shared mvar" cs 2

/- The empty goal list yields no clusters. -/
run_cmd liftTermElabM do
  let cs ← getGoalClusters []
  expectCount "empty" cs 0

/- `sharedMVars` reports a directly shared metavariable. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkNatLit 1)
  let ms ← sharedMVars [g1, g2]
  unless ms == [b] do
    throwError "sharedMVars shared: expected [?b], got {ms.map (·.name)}"

/- `sharedMVars` ignores a metavariable that occurs in only one goal. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let c ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar c) (mkNatLit 1)
  let ms ← sharedMVars [g1, g2]
  unless ms.isEmpty do
    throwError "sharedMVars independent: expected [], got {ms.map (·.name)}"

/- `sharedMVars` reports both link metavariables of a transitive chain. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let c ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkMVar c)
  let g3 ← eqGoal (mkMVar c) (mkNatLit 1)
  let ms ← sharedMVars [g1, g2, g3]
  unless ms.contains b && ms.contains c && ms.length == 2 do
    throwError "sharedMVars chain: expected both ?b and ?c, got {ms.map (·.name)}"

/- `sharedMVars` ignores an assigned metavariable. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkNatLit 1)
  b.assign (mkNatLit 5)
  let ms ← sharedMVars [g1, g2]
  unless ms.isEmpty do
    throwError "sharedMVars assigned: expected [], got {ms.map (·.name)}"

/-- A two-goal cluster: goal 0 (`g1`) and goal 1 (`g2`) share `?b`. Returns the
maps `getSubgoals` would hold, sharing one saved state across both goals. -/
private def twoGoalCluster (b g1 g2 : MVarId) : Lean.Elab.TermElabM
    (Std.HashMap StateId ClusterInfo
     × Std.HashMap StateId (MVarId × Lean.Elab.Term.SavedState)) := do
  let st ← Lean.Elab.Term.saveState
  let goalMap : Std.HashMap StateId (MVarId × Lean.Elab.Term.SavedState) :=
    Std.HashMap.ofList [(0, (g1, st)), (1, (g2, st))]
  let clusterMap : Std.HashMap StateId ClusterInfo :=
    Std.HashMap.ofList [(0, ⟨[0, 1], [b]⟩), (1, ⟨[0, 1], [b]⟩)]
  return (clusterMap, goalMap)

/- `carriedSiblings`: assigning the shared mvar carries the still-open sibling. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkNatLit 1)
  let (clusterMap, goalMap) ← twoGoalCluster b g1 g2
  b.assign (mkNatLit 5)
  let carried ← carriedSiblings clusterMap goalMap 0
  unless carried == [(g2, 1)] do
    throwError "carriedSiblings carry: expected sibling g2, got \
      {carried.map (fun (m, _) => m.name)}"

/- `carriedSiblings`: nothing is carried when no shared mvar was assigned. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkNatLit 1)
  let (clusterMap, goalMap) ← twoGoalCluster b g1 g2
  let carried ← carriedSiblings clusterMap goalMap 0
  unless carried.isEmpty do
    throwError "carriedSiblings no-assign: expected [], got \
      {carried.map (fun (m, _) => m.name)}"

/- `carriedSiblings`: a sibling closed as a side effect is dropped, not carried. -/
run_cmd liftTermElabM do
  let b ← natMVar
  let g1 ← eqGoal (mkMVar b) (mkNatLit 0)
  let g2 ← eqGoal (mkMVar b) (mkNatLit 1)
  let (clusterMap, goalMap) ← twoGoalCluster b g1 g2
  b.assign (mkNatLit 5)
  g2.assign (mkNatLit 0)  -- mark the sibling closed (type irrelevant here)
  let carried ← carriedSiblings clusterMap goalMap 0
  unless carried.isEmpty do
    throwError "carriedSiblings closed-sibling: expected [], got \
      {carried.map (fun (m, _) => m.name)}"

end Backend.ClusterTests
