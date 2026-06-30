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

end Backend.ClusterTests
