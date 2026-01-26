import { Fragment, useState } from 'react'
import { useRpcSession, useAsync, mapRpcError } from '@leanprover/infoview';
// import './App.css'

type ID = string

type Kind = "tactic" | "goal"

type Status = "selected" | "semiselected" | "unselected"

type Node = {
  kind: Kind, // tactic or goal
  id: ID, // should be unique among all nodes
  data: string, // Lean-recognizable description
  final: boolean, // whether a goal is completed/a tactic is in the final script
  children: Node[], // applicable tactics for a goal, subgoals for a tactic
  status: Status, // display information
  visible: boolean // visibility in display
}

// type Node = Readonly<MutableNode>

function updateNode(
  root: Node,
  update: (n: Node) => Node,
  breakAfterNode: ((t: Node) => boolean)):
  Node {
  const newRoot = update(root);

  if (breakAfterNode(root)) {
    return newRoot
  }

  return {
    ...newRoot, children: newRoot.children.map(g =>
      updateNode(g, update, breakAfterNode))
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

function changeNodeVisibility(n: Readonly<Node>, visible: boolean): Node {
  return { ...n, visible: true }
}

function changeStatusAtSelected(root: Node, newStatus: Status): Node {
  const update = (n: Node) => n.status == 'selected'
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

function isNonstrictAncestorOf(parentCand: Readonly<Node>, childId: ID)
  : boolean {
  if (parentCand.id === childId) {
    return true
  } else {
    return parentCand.children.some(
      (v: Node) => isNonstrictAncestorOf(v, childId))
  }
}

function nearestCommonAncestorWithSelected(n: Readonly<Node>, id: ID):
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
    // Note: this should only happen if n is selected
    return n
  }
}

function handleTacticClick(root: Node, clicked: Node): Node {
  const previouslyExplored = false //TODO
  const previousNodeWasParent = true //TODO
  const previousNodeWasDescendant = false //TODO

  const nca = nearestCommonAncestorWithSelected(root, clicked.id);
  if (nca.id === clicked.id) {

  }

  if (previouslyExplored) {
    // TODO
    // restore status of subtree when abandoned
    // including which node was selected
    return root
  } else {
    // change node status to "selected"
    var newGoal = changeStatusAtId(root, clicked.id, 'selected')
    // TODO
    // show subgoals
    // if none, retrace path upward marking applicable nodes as final
    return newGoal
  }

  if (previousNodeWasParent) {
    // note: if the previous node was a non-parent ancestor, the
    // current node should never have been clickable
    // change parent to semiselected
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

function treeValid(root: Readonly<Node>): boolean {
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
