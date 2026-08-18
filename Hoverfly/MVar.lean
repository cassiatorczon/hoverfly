module

public import Hoverfly.State

open Lean State

namespace MVar

public def getGoalClusters (goals : List MVarId) : MetaM (List (List MVarId)) := do
  let mvarGoalLists ← goals.mapM (fun g => do
    let mvs ← g.getMVarDependencies
    let unassigned ← mvs.toList.filterM fun m => do return !(← m.isAssigned)
    return (g, unassigned))
  let mvarLists := mvarGoalLists.map (fun (_,x) => x)
  let f clustersSoFar mvs : List (List MVarId) :=
    let g acc mv : List (List MVarId) :=
      let (withMv, withoutMv) := acc.partition (fun l => l.contains mv)
      withMv.flatten.eraseDups :: withoutMv
    List.foldl g clustersSoFar mvs
  let clusters : List (List MVarId) := List.foldl f mvarLists mvarLists
  let grouped := clusters.filterMap fun cl =>
    let gs := (mvarGoalLists.filter fun (_, mvs) => mvs.any cl.contains).map (·.1)
    if gs.isEmpty then none else some gs
  let touched := grouped.flatten
  let singles :=
    (mvarGoalLists.filter fun (g, _) => !touched.contains g).map (fun (g, _) => [g])
  return grouped ++ singles

def unassignedDeps (g : MVarId) : MetaM (List MVarId) := do
  let deps ← g.getMVarDependencies
  deps.toList.filterM fun m => do return !(← m.isAssigned)

public def sharedMVars (goals : List MVarId) : MetaM (List MVarId) := do
  let deps ← goals.mapM unassignedDeps
  let occursInTwo m := (deps.filter (·.contains m)).length ≥ 2
  return deps.flatten.eraseDups.filter occursInTwo

public def dropMVarGoals (goals : List MVarId) : MetaM (List MVarId) :=
  goals.filterM fun g => do
    let others := goals.filter (· != g)
    return !(← others.anyM fun g' => do return (← unassignedDeps g').contains g)

public def carriedSiblings
    (clusterMap : Std.HashMap StateId ClusterInfo)
    (goalMap : Std.HashMap StateId (MVarId × Elab.Term.SavedState))
    (parentId : StateId) : MetaM (List (MVarId × StateId)) := do
  match clusterMap.get? parentId with
  | none => return []
  | some ⟨members, sharedMVars⟩ =>
    if !(← sharedMVars.anyM (·.isAssigned)) then
      return []
    let siblingIds := members.filter (· != parentId)
    siblingIds.filterMapM fun sid => do
      match goalMap.get? sid with
      | none => return none
      | some (smv, _) =>
        if ← smv.isAssigned then return none else return some (smv, sid)

end MVar
