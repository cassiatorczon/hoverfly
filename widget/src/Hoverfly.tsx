import { Fragment, useState } from 'react'
import { useRpcSession, useAsync, mapRpcError } from '@leanprover/infoview';
// import './App.css'

type ID = string

type Kind = "tactic" | "goal"

type Status = "selected" | "semiselected" | "unselected"

type MutableNode = {
  kind: Kind, // tactic or goal
  id: ID, // should be unique among all nodes; must have an immutable type
  data: string, // Lean-recognizable description
  completed: boolean, // a completed goal or tactic with all completed subgoals
  children: Node[], // applicable tactics for a goal, subgoals for a tactic
  status: Status, // display information
  visible: boolean // visibility in display
}

type Node = Readonly<MutableNode>

function assert(p: boolean, e: string): void {
  if (!p) {
    throw new Error(e)
  }
}

function updateNode(
  root: Node,
  update: (n: Node) => Node,
  breakAfter: ((t: Node) => boolean)):
  Node {
  const newRoot = update(root);

  if (breakAfter(root)) {
    return newRoot
  }

  return {
    ...newRoot, children: newRoot.children.map(g =>
      updateNode(g, update, breakAfter))
  }
}


function renderNode(n: Node, onClick: (id: ID) => void): React.ReactNode {
  if (!n.visible) {
    return
  }

  return (
    <Fragment key={n.id}>
      <li onClick={() => onClick(n.id)}>{n.data} [{n.status}]</li>
      <ul> {n.children.map((child: Node) => renderNode(child, onClick))}</ul >
    </Fragment>)
}

function changeNodeVisibility(n: Node, newVis: boolean): Node {
  return { ...n, visible: newVis }
}

function changeStatusAtSelected(root: Node, newStatus: Status): Node {
  const update = (n: Node) => n.status === 'selected'
    ? { ...n, status: newStatus } : n
  const breakAfter = (n: Node) => n.status === 'selected'
  return updateNode(root, update, breakAfter)
}

function changeStatusAtId(root: Node, id: ID, newStatus: Status): Node {
  const update = (n: Node) => n.id === id
    ? { ...n, status: newStatus } : n
  const pred = (n: Node) => n.id === id
  return updateNode(root, update, pred);
}

function isNonstrictAncestorOf(parentCand: Node, childId: ID)
  : boolean {
  if (parentCand.id === childId) {
    return true
  } else {
    return parentCand.children.some(
      (v: Node) => isNonstrictAncestorOf(v, childId))
  }
}

function nearestCommonAncestorWithSelected(n: Node, id: ID):
  Readonly<Node> {
  const selectedNonstrictAncestor = n.children.find(
    (c: Node) => c.status === 'semiselected' || c.status === 'selected')
  if (selectedNonstrictAncestor) {
    if (isNonstrictAncestorOf(selectedNonstrictAncestor, id)) {
      return selectedNonstrictAncestor.id === id
        ? selectedNonstrictAncestor
        : nearestCommonAncestorWithSelected(selectedNonstrictAncestor, id)
    } else {
      return n
    }
  } else {
    assert(n.status === 'selected',
      "Malformed tree: [" + n.data + "] is not selected and has no selected or"
      + " semiselected immediate children")
    return n
  }
}

function handleTacticClick(root: Node, clicked: Node): Node {
  const previouslyExplored = false //TODO

  if (clicked.status === 'selected') {
    // User has clicked the already-selected node. Do nothing.
    return root
  }
  const nca = nearestCommonAncestorWithSelected(root, clicked.id)

  var newGoal;
  if (previouslyExplored) {
    // TODO
    // restore status of subtree when abandoned
    // including which node was selected
    newGoal = root
  } else {
    // change node status to "selected"
    var newGoal1 = changeStatusAtId(root, clicked.id, 'selected')
    // TODO
    // show subgoals
    // if none, retrace path upward marking applicable nodes as completed
    newGoal = newGoal1
  }

  if (nca.id === clicked.id) {
    // previously selected node was a descendant of clicked node
    // Change status of all nodes in applicable child subtree of current node to “unselected”
    // Hide that subtree, with:
    // Ellipsis
    // Caching
    // Marking for completeness retained
    newGoal = root //TODO
  } else if (nca.status === 'selected') {
    // if the previous node was a non-parent ancestor, the
    // current node should never have been clickable
    assert(nca.children.some((c: Node) => c.id === clicked.id),
      "Non-child descendant of selected node should not be clickable.")
    // change parent to semiselected
    changeStatusAtSelected(root, 'semiselected')
  } else {
    //Change status of neighboring ancestor of that node to “unselected”
    // Hide neighboring ancestor subtree, with:
    // Ellipsis
    // Caching of subtree
    // Marking for completeness retained
    return root //TODO
  }

  // restore stuff OR
  //    show applicable tactics
  // maybe hide stuff
  return root
}

function checkUniqueIDs(root: Node, ids: Set<ID>): void {
  assert(!ids.has(root.id), "Malformed tree: duplicate ID (" + root.id + ").")

  const newIds = ids.add(root.id)
  for (var c of root.children) {
    checkUniqueIDs(c, newIds)
  }
}

function checkKinds(root: Node, expectedKind: Kind): void {
  assert(root.kind === expectedKind, "Malformed tree: expected node " + root.id
    + " to have kind " + expectedKind + ", but found kind " + root.kind + ".")

  const nextKind = expectedKind === 'goal' ? 'tactic' : 'goal'
  for (var c of root.children) {
    checkKinds(c, nextKind)
  }
}

function checkStatusAndVisibility(root: Node): void {
  // TODO Harry :)
}

function checkCompletedness(root: Node): void {
  let shouldBeCompleted = root.kind === 'goal'
    ? root.children.some((c: Node) => c.completed)
    : root.children.every((c: Node) => c.completed)
  assert(shouldBeCompleted === root.completed,
    "Incorrect 'completed' field for node " + root.id + "; expected "
    + shouldBeCompleted + " but found " + root.completed + ".")
}

function checkTree(root: Node): void {
  // root is a goal
  // all goals have only tactic children
  // all tactics have only goal children
  checkKinds(root, 'goal')

  // all IDs are unique
  checkUniqueIDs(root, new Set<ID>())

  // exactly one node is selected
  // no grandchildren of selected node are visible
  // no "cousins" of selected node are visible
  // immediate children and all ancestors of selected goal
  //   are visible (and selected goal itself)
  // ancestor of selected goal iff 'semiselected'
  checkStatusAndVisibility(root)

  // a goal is completed iff at least one of its children is completed
  // a tactic is completed iff it has no uncompleted children
  checkCompletedness(root)
}

function handleGoalClick(root: Node, clickedId: ID): Node {
  const previouslyExplored = false //TODO
  const previousNodeWasParent = true //TODO
  const previousNodeWasDescendant = false //TODO

  if (previouslyExplored) {
    // TODO restore status of subtree when abandoned
    // including which node was selected
    return root
  } else {
    var newGoal = changeStatusAtId(root, clickedId, 'selected')
    // todo this is mapping over the wrong children
    return {
      ...newGoal, children:
        newGoal.children.map(t =>
          changeStatusAtId(root, t.id, 'unselected'))
    }
  }

  if (previousNodeWasParent) {
    changeStatusAtSelected(root, 'semiselected')
  } else if (previousNodeWasDescendant) {
    // Change status of all nodes in applicable child subtree of current node to “unselected”
    // Hide that subtree, with:
    // Ellipsis
    // Caching
    // Marking for completeness retained
    return root //TODO
  } else {
    //Change status of neighboring ancestor of that node to “unselected”
    // Hide neighboring ancestor subtree, with:
    // Ellipsis
    // Caching of subtree
    // Marking for completeness retained
    return root //TODO
  }

  // restore stuff OR
  //    show applicable tactics
  // maybe hide stuff
  return root
}

function HoverflyTree({ root, onClick }
  : { root: Node, onClick: (id: ID) => void },) {
  return (
    <>
      <ul>
        {renderNode(root, onClick)}
      </ul>
    </>
  )
}

function Hoverfly() {
  const rs = useRpcSession()

  const st = useAsync(() =>
    rs.call('getInitialState', ""), [rs])

  return st.state === 'resolved'
    ? <HoverflyTree root={st.value as Node} onClick={(id: ID) => { }} />
    : st.state === 'rejected' ?
      <p>{mapRpcError(st.error).message}</p>
      : <p>Loading...</p>
}

export default Hoverfly
