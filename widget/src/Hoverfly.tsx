import { Fragment, useState } from 'react'
import { useRpcSession, useAsync, mapRpcError } from '@leanprover/infoview';
// import './App.css'

type Status = "selected" | "semiselected" | "unselected"

type Tactic = { id: string, name: string, children: Goal[], status: Status, visible: boolean }

type Goal = { id: string, name: string, completed: boolean, children: Tactic[], status: Status, visible: boolean }

type Node = Tactic | Goal

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
  const previouslyExplored = false //TODO
  const previousNodeWasParent = true //TODO
  const previousNodeWasDescendant = false //TODO

  if (previouslyExplored) {
    // TODO restore status of subtree when abandoned
    // including which node was selected
    return goal
  } else {
    var newGoal = changeStatus(goal, (n: Node) => n.id == id, 'selected')
    return {
      ...newGoal, children:
        newGoal.children.map(t => changeTacticStatus(t, 'unselected'))
    }
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
  return goal
}

function treeValid(goal: Goal): boolean {
  /* Incomplete list of invariants:
  - all IDs are unique
  - all children of goals are tactics
  - all children of tactics are goals
  - exactly one node is selected
  - no grandchildren of selected node are visible
  - no "cousins" of selected node are visible
  - immediate children and all ancestors of selected goal
    are visible (and selected goal itself)
  - ancestor of selected goal iff 'semiselected'
  - a goal is completed iff all its descendant goals are */
  return true // TODO
}

function changeTacticStatus(t: Tactic, s: Status): Tactic {
  return { ...t, status: s }
}

function handleGoalClick(goal: Goal, id: string): Goal {
  const previouslyExplored = false //TODO
  const previousNodeWasParent = true //TODO
  const previousNodeWasDescendant = false //TODO

  if (previouslyExplored) {
    // TODO restore status of subtree when abandoned
    // including which node was selected
    return goal
  } else {
    var newGoal = changeStatus(goal, (n: Node) => n.id == id, 'selected')
    // todo this is mapping over the wrong children
    return {
      ...newGoal, children:
        newGoal.children.map(t => changeTacticStatus(t, 'unselected'))
    }
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
