import { Fragment, useState } from 'react'
import { useRpcSession, useAsync, mapRpcError } from '@leanprover/infoview';
// import './App.css'

type Status = "selected" | "semiselected" | "unselected" | "hidden"

type Tactic = { id: string, name: string, children: Goal[], status: Status }

type Goal = { id: string, name: string, completed: boolean, children: Tactic[], status: Status }

type Node = Tactic | Goal

// function updateNode<N extends Node>(
//   root: N,
//   updateTactic?: (t: Tactic) => Tactic,
//   updateGoal?: (g: Goal) => Goal,
//   breakAfter?: (n: N) => boolean):
//   N {
//   const newRoot : N =
//     (updateGoal && root.kind === "goal")
//       ? updateGoal(root)
//       : ((updateTactic && root.kind === "tactic")
//         ? updateTactic(root)
//         : root)
//   if (breakAfter && breakAfter(root)) {
//     return newRoot
//   }

//   return {
//     ...newRoot, children: newRoot.children.map(g =>
//       updateRootedAtGoal(g, updateTactic, updateGoal, breakAfterTactic, breakAfterGoal))
//   }
// }

function updateRootedAtTactic(
  root: Tactic,
  updateTactic: (t: Tactic) => Tactic,
  updateGoal: (g: Goal) => Goal,
  breakAfterTactic: undefined | ((t: Tactic) => boolean),
  breakAfterGoal: undefined | ((g: Goal) => boolean)):
  Tactic {
  const newRoot = updateTactic(root);
  if (breakAfterTactic && breakAfterTactic(root)) {
    return newRoot
  }

  return {
    ...newRoot, children: newRoot.children.map(g =>
      updateRootedAtGoal(g, updateTactic, updateGoal, breakAfterTactic, breakAfterGoal))
  }
}

function updateRootedAtGoal(
  root: Goal,
  updateTactic: (t: Tactic) => Tactic,
  updateGoal: (g: Goal) => Goal,
  breakAfterTactic: undefined | ((t: Tactic) => boolean),
  breakAfterGoal: undefined | ((g: Goal) => boolean)):
  Goal {
  const newRoot = updateGoal(root);
  if (breakAfterGoal && breakAfterGoal(root)) {
    return newRoot
  }

  return {
    ...newRoot, children: newRoot.children.map(t =>
      updateRootedAtTactic(t, updateTactic, updateGoal, breakAfterTactic, breakAfterGoal))
  }
}

function renderGoal(goal: Goal, onClick: (id: string) => void): React.ReactNode {
  return (
    <Fragment key={goal.id}>
      <li onClick={() => onClick(goal.id)}>{goal.name} [{goal.status}]</li>
      <ul> {goal.children.map((child: Tactic) => renderTactic(child, onClick))}</ul >
    </Fragment>)
}

function renderTactic(tactic: Tactic, onClick: (id: string) => void): React.ReactNode {
  return (
    <Fragment key={tactic.id}>
      <li onClick={() => onClick(tactic.id)}>{tactic.name} [{tactic.status}]</li>
      <ul>{tactic.children.map((child: Goal) => renderGoal(child, onClick))}</ul>
    </Fragment>)
}

function changeStatus(goal: Goal, p: (n: Node) => boolean, newStatus: Status): Goal {
  const updateTactic = (t: Tactic) => p(t) ? { ...t, status: newStatus } : t
  const updateGoal = (g: Goal) => p(g) ? { ...g, status: newStatus } : g
  const breakAfter = (n: Node) => p(n)
  return updateRootedAtGoal(goal, updateTactic, updateGoal, breakAfter, breakAfter)
}

function handleTacticClick(goal: Goal, id: string): Goal {
  // TODO
  // change status
  // restore things OR
  //    show subgoals - requires rpc
  // mark applicable ancestors as completed
  // maybe hide previous things
  // hide unexplored neighboring tactics

  return goal
}

// TODO an isTreeValid function to run every time

// function selectedNodeRootedAtGoal(goal: Goal): string | undefined {
//   if (goal.status === 'selected') {
//     return goal.id
//   }
//   var id;
//   for (const t of goal.children) {
//     id = selectedNodeRootedAtTactic(t);
//     if (id !== undefined) {
//       break
//     }
//   }
//   return id
// }

// function selectedNodeRootedAtTactic(tactic: Tactic): string | undefined {
//   if (tactic.status === 'selected') {
//     return tactic.id
//   }
//   var id;
//   for (const g of tactic.children) {
//     id = selectedNodeRootedAtGoal(g);
//     if (id !== undefined) {
//       break
//     }
//   }
//   return id
// }

function handleGoalClick(goal: Goal, id: string): Goal {
  const previouslyExplored = false //TODO
  const previousNodeWasParent = true //TODO
  const previousNodeWasDescendant = false //TODO

  if (previouslyExplored) {
    // TODO restore status of subtree when abandoned
    // including which node was selected
    return goal
  } else {
    // TODO show applicable tactics
    changeStatus(goal, (n: Node) => n.id == id, 'selected')
  }

  if (previousNodeWasParent) {
    changeStatus(goal, (n: Node) => n.status === 'selected', 'semiselected')
  } else if (previousNodeWasDescendant) {
    // Change status of all nodes in applicable child subtree of current node to “unselected”
    // Hide that subtree, with:
    // Ellipsis
    // Caching
    // Marking for completeness retained
    return goal //TODO
  } else {
    //Change status of neighboring ancestor of that node to “unselected”
    // Hide neighboring ancestor subtree, with:
    // Ellipsis
    // Caching of subtree
    // Marking for completeness retained
    return goal //TODO
  }

  // restore stuff OR
  //    show applicable tactics
  // maybe hide stuff
  return goal
}

/*
List of operations:

Change node selection status (selected, unselected, semiselected, hidden?)
Mark goal node and applicable ancestors as completed

Show applicable tactics for a goal
Show subgoals for a tactic
Hide and cache subtree rooted at goal
Hide and cache subtree rooted at tactic
Restore subtree rooted at goal
Restore subtree rooted at tactic
Hide unexplored neighboring tactics

*/

function HoverflyTree({ goal, onClick }: { goal: Goal, onClick: (id: string) => void },) {

  return (
    <>
      <ul>
        {renderGoal(goal, onClick)}
      </ul>
    </>
  )
}

function Hoverfly() {
  const rs = useRpcSession()

  const st = useAsync(() =>
    rs.call('getInitialState', ""), [rs])

  return st.state === 'resolved' ? <HoverflyTree goal={st.value as Goal} onClick={(id: string) => { }} />
    : st.state === 'rejected' ?
      <p>{mapRpcError(st.error).message}</p>
      : <p>Loading...</p>
}

export default Hoverfly
