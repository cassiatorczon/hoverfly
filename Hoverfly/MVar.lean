module

public import Hoverfly.State

open Lean State

namespace MVar

/-
Get the list of unassigned mvars on which a goal depends.
-/
def unassignedDeps (g : MVarId) : MetaM (List MVarId) := do
  let deps ← g.getMVarDependencies
  deps.toList.filterM fun m => do return !(← m.isAssigned)

/-
Get clusters of goals that transitively contain the same unassigned mvars.

I.e., if we had four goals with unassigned mvar dependencies as follows:
* g0 depends on ?x
* g1 depends on ?x and ?y
* g2 depends on ?y
* g3 depends on ?z
* g4 depends on no mvars
then the clusters would be [[g0, g1, g2], [g3], [g4]].
-/
public def getGoalClusters (goals : List MVarId) : MetaM (List (List MVarId)) := do
  -- get pairs of all goals and their lists of unassigned mvars
  let mvarGoalLists ← goals.mapM (fun g => do
    let unassigned ← unassignedDeps g
    return (g, unassigned))

  -- get groups of transitively shared mvars
  let mvarLists := mvarGoalLists.map (fun (_,x) => x)
  let mergeByMVList groupsSoFar mvs : List (List MVarId) :=
    let mergeByMV acc mv : List (List MVarId) :=
      -- merge all groups so far that contain the current mvar
      let (withMv, withoutMv) := acc.partition (fun l => l.contains mv)
      withMv.flatten.eraseDups :: withoutMv
    List.foldl mergeByMV groupsSoFar mvs
  let groups : List (List MVarId) := List.foldl mergeByMVList mvarLists mvarLists

  -- cluster goals by which group their mvars are in
  -- (all mvars for a given goal must be in the same group after previous step)
  let clustered := groups.filterMap fun cl =>
    let gs := (mvarGoalLists.filter fun (_, mvs) => mvs.any cl.contains).map (·.1)
    if gs.isEmpty then none else some gs

  -- add back in goals that do not depend on any mvars
  let touched := clustered.flatten
  let singles :=
    (mvarGoalLists.filter fun (g, _) => !touched.contains g).map (fun (g, _) => [g])
  return clustered ++ singles

/-
Get the corresponding list of mvars for a cluster of goals.
-/
public def sharedMVars (goals : List MVarId) : MetaM (List MVarId) := do
  let deps ← goals.mapM unassignedDeps
  let occursInTwo m := (deps.filter (·.contains m)).length ≥ 2
  return deps.flatten.eraseDups.filter occursInTwo

/-
Filter a list of goals, keeping only those that are NOT mvars on which other
goals depend. All goals in the input list are assumed to be unassigned.
-/
public def dropMVarGoals (goals : List MVarId) : MetaM (List MVarId) :=
  goals.filterM fun g => do
    let others := goals.filter (· != g)
    return !(← others.anyM fun g' => do return (← unassignedDeps g').contains g)

/-
For a given goal (with corresponding state given by `parentId`), if  any of the
mvars in the corresponding cluster are assigned a value, get a list of all the
unsolved goals for that cluster and their corresponding states.

-/
public def carriedSiblings
    (clusterMap : Std.HashMap StateId ClusterInfo)
    (goalMap : Std.HashMap StateId (MVarId × Elab.Term.SavedState))
    (parentId : StateId) : MetaM (List (MVarId × StateId)) := do
  match clusterMap.get? parentId with
  | none => return []
  | some ⟨members, sharedMVars⟩ =>
    -- if no mvars in the cluster have been assigned, no copying is needed
    if !(← sharedMVars.anyM (·.isAssigned)) then
      return []
    let siblingIds := members.filter (· != parentId)
    siblingIds.filterMapM fun sid => do
      match goalMap.get? sid with
      | none => return none
      | some (smv, _) =>
        if ← smv.isAssigned then return none else return some (smv, sid)

end MVar
