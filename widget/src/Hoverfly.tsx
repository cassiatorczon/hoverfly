import { Fragment, useState, useEffect } from 'react'
import { useRpcSession, useAsync, mapRpcError, RpcSessionAtPos } from '@leanprover/infoview';
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
  visible: boolean, // visibility in display
  explored: boolean, // whether the node has been explored
  cache: Node | undefined // previous version of the subtree rooted at this node
}

type Node = Readonly<MutableNode>

/* Check tree invariants */

function checkUniqueIDs(n: Node, ids: Set<ID>): void {
  assert(!ids.has(n.id), "Malformed tree: duplicate ID (" + n.id + ").")

  // TODO does the state here persist correctly
  var newIds = ids.add(n.id)
  for (var c of n.children) {
    checkUniqueIDs(c, newIds)
  }
}

function checkKinds(n: Node, expectedKind: Kind): void {
  assert(n.kind === expectedKind, "Malformed tree: expected node " + n.id
    + " to have kind " + expectedKind + ", but found kind " + n.kind + ".")

  const nextKind = expectedKind === 'goal' ? 'tactic' : 'goal'
  n.children.forEach((c: Node) => checkKinds(c, nextKind))
}

function checkStatusAndVisibility(n: Node): void {
  // invariants
  // goals: visible iff parent is selected/semiselected (or root)
  //
  // no grandchildren of selected node are visible
  // no "cousins" of selected node are visible (i.e., i)
  // immediate children and all ancestors of selected goal
  //   are visible (and selected goal itself)

  /* Invariants
  - exactly one node is selected
  - every ancestor of the selected node is 'semiselected'
  - (arguably completed goals whose parent tactic is also in the
    ancestor path of the selected node should be semiselected but
    we can debate that)
  -
  */

}

function checkCompletedness(n: Node): void {
  // report errors at leaves first
  n.children.forEach((c: Node) => checkCompletedness(c))

  let shouldBeCompleted = n.kind === 'goal'
    ? n.children.some((c: Node) => c.completed)
    : n.children.every((c: Node) => c.completed)
  assert(shouldBeCompleted === n.completed,
    "Incorrect 'completed' field for node " + n.id + "; expected "
    + shouldBeCompleted + " but found " + n.completed + ".")
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

/* Update tree */

async function updateNodes(
  n: Node,
  update: (n: Node) => Promise<Node>,
  breakAfter: ((n: Node) => boolean)):
  Promise<Node> {
  const newNode = await update(n);

  if (breakAfter(n)) {
    return newNode
  }

  return {
    ...newNode, children: await Promise.all(newNode.children.map((g) => updateNodes(g, update, breakAfter)))
  }
}

function changeNodeVisibility(n: Node, newVis: boolean): Node {
  return { ...n, visible: newVis }
}

async function changeStatusAtSelected(root: Node, newStatus: Status): Promise<Node> {
  const update = async (n: Node) => n.status === 'selected'
    ? { ...n, status: newStatus } : n
  const breakAfter = (n: Node) => n.status === 'selected'
  return updateNodes(root, update, breakAfter)
}

async function changeStatusAtId(root: Node, id: ID, newStatus: Status): Promise<Node> {
  const update = async (n: Node) => n.id === id ? { ...n, status: newStatus } : n
  const pred = (n: Node) => n.id === id
  return updateNodes(root, update, pred);
}

function cacheIfSelected(n: Node): Node {
  if (n.status === 'selected' || n.status === 'semiselected') {
    return { ...n, status: 'unselected', cache: n, children: [] }
  }
  return n
}

function cacheChild(n: Node): Node {
  let newChildren = n.children.map((c: Node) => cacheIfSelected(c))
  return { ...n, children: newChildren }
}

/* Get tree info */

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

/* Handlers */

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

async function handleClick(root: Node, clicked: Node, rs: RpcSessionAtPos): Promise<Node> {
  const previouslyExplored = false //TODO
  const previousNodeWasParent = true //TODO
  const previousNodeWasDescendant = false //TODO

  if (clicked.status === 'selected') {
    // User has clicked the already-selected node. Do nothing.
    return root
  }

  const nca = nearestCommonAncestorWithSelected(root, clicked.id)

  if (nca.id === clicked.id) {
    // previously selected node was a descendant of clicked node
    // cache applicable subtree of clicked node
    // change cliked node status to 'selected
    const ncaPostCache = cacheChild(nca)
    const ncaNewStatus = changeStatusAtId(root, ncaPostCache.id, 'selected')

    const update = async (n: Node) => n.id === nca.id ? ncaNewStatus : n
    const breakAfter = (n: Node) => n.id === nca.id
    return updateNodes(root, update, breakAfter)
  } else if (nca.status === 'selected') {
    // previously selected node was an ancestor of clicked node

    // if the previous node was a non-parent ancestor, the
    // current node should never have been clickable
    assert(nca.children.some((c: Node) => c.id === clicked.id),
      "Non-child descendant of selected node should not be clickable.")

    // change parent to semiselected
    const parentUpdated = await changeStatusAtSelected(root, 'semiselected')

    const breakAfter = (n: Node) => n.id === clicked.id
    if (clicked.explored) {
      // restore cache at clicked node

      if (!clicked.cache) {
        throw new
          Error("Attempted to restore nonexistent cache at node " + clicked.id)
      } else {
        const update = async (n: Node) => n.id === clicked.id ? (clicked.cache as Node) : n
        return updateNodes(parentUpdated, update, breakAfter)
      }
    } else {
      // change node status to selected
      const clickedUpdated = changeStatusAtId(root, clicked.id, 'selected')

      const update = async (n: Node) => n.id === clicked.id
        ? n.kind === 'goal'
          ? { ...await getApplicableTactics(n, rs), explored: true }
          : await getSubgoals(n, rs)
        : n
      return updateNodes(await clickedUpdated, update, breakAfter)
    }
  } else {
    // new node should be an immediate child of nca
    assert(nca.children.some((c: Node) => c.id === clicked.id),
      "Non-child descendant of nearest common ancestor of previously " +
      "selected node and newly clicked node node should not be clickable.")

    // cache branch corresponding to previous node
    const newNca = cacheChild(nca)
    const updateNca = async (n: Node) => n.id === nca.id ? newNca : n
    const breakAfterNca = (n: Node) => n.id === nca.id
    const newGoal = updateNodes(root, updateNca, breakAfterNca)

    const updateClicked = async (n: Node) =>
      n.id === clicked.id
        ? ({ ...n, status: 'selected', explored: true } as Node)
        : n
    const breakAfterClicked = (n: Node) => n.id === clicked.id
    return updateNodes(root, updateClicked, breakAfterClicked)
  }
}
// if (previouslyExplored) {
//   // TODO restore status of subtree when abandoned
//   // including which node was selected
//   return root
// } else {
//   var newGoal = changeStatusAtId(root, clickedId, 'selected')
//   // todo this is mapping over the wrong children
//   return {
//     ...newGoal, children:
//       newGoal.children.map(t =>
//         changeStatusAtId(root, t.id, 'unselected'))
//   }
// }

// if (previousNodeWasParent) {
//   changeStatusAtSelected(root, 'semiselected')
// } else if (previousNodeWasDescendant) {
//   // Change status of all nodes in applicable child subtree of current node to “unselected”
//   // Hide that subtree, with:
//   // Ellipsis
//   // Caching
//   // Marking for completeness retained
//   return root //TODO
// } else {
//   //Change status of neighboring ancestor of that node to “unselected”
//   // Hide neighboring ancestor subtree, with:
//   // Ellipsis
//   // Caching of subtree
//   // Marking for completeness retained
//   return root //TODO
// }

// // restore stuff OR
// //    show applicable tactics
// // maybe hide stuff
// return root
//}

/* Util */

function assert(p: boolean, e: string): void {
  if (!p) {
    throw new Error(e)
  }
}

/* External */

// given a goal node, returns the same node with
// applicable tactics added as children
async function getApplicableTactics(n: Node, rs: RpcSessionAtPos): Promise<Node> {
  assert(n.kind == 'goal',
    "Called getApplicableTactics on tactic node " + n.id)

  const g = nodeToLeanGoal(n)
  const tactics: LeanTactic[] = await rs.call("getApplicableTactics", g)
  const tsxTactics = tactics.map((t: LeanTactic) => leanTacticToNode(t))
  return { ...n, children: tsxTactics }
}

// given a tactic node, returns the same node with
// subgoals added as children
async function getSubgoals(n: Node, rs: RpcSessionAtPos): Promise<Node> {
  assert(n.kind == 'tactic',
    "Called getSubgoals on goal node " + n.id)

  const t = nodeToLeanTactic(n)
  const subgoals: LeanGoal[] = await rs.call("getSubgoals", t)
  const tsxGoals = subgoals.map((g: LeanGoal) => leanGoalToNode(g))
  return { ...n, children: tsxGoals }
}

// type MutableNode = {
//   kind: Kind, // tactic or goal
//   id: ID, // should be unique among all nodes; must have an immutable type
//   data: string, // Lean-recognizable description
//   completed: boolean, // a completed goal or tactic with all completed subgoals
//   children: Node[], // applicable tactics for a goal, subgoals for a tactic
//   status: Status, // display information
//   visible: boolean, // visibility in display
//   explored: boolean, // whether the node has been explored
//   cache: Node | undefined // previous version of the subtree rooted at this node
// }

type LeanGoal = {
  id: string
  data: string
  children: LeanTactic[]
}

type LeanTactic = {
  id: string
  data: string
  children: LeanGoal[]
}

function leanGoalToNode(g: LeanGoal): Node {
  return {
    kind: 'tactic',
    id: g.id,
    data: g.data,
    completed: false,
    status: 'unselected',
    visible: true,
    explored: false,
    cache: undefined,
    children: g.children.map((t: LeanTactic) => leanTacticToNode(t))
  }
}

function leanTacticToNode(t: LeanTactic): Node {
  return {
    kind: 'tactic',
    id: t.id,
    data: t.data,
    completed: false,
    status: 'unselected',
    visible: true,
    explored: false,
    cache: undefined,
    children: t.children.map((g: LeanGoal) => leanGoalToNode(g))
  }
}

function nodeToLeanGoal(g: Node): LeanGoal {
  assert(g.kind === 'goal', "Tried to convert tactic to Lean goal")
  return {
    id: g.id,
    data: g.data,
    children: g.children.map((t: Node) => nodeToLeanTactic(t))
  }
}

function nodeToLeanTactic(t: Node): LeanTactic {
  assert(t.kind === 'tactic', "Tried to convert goal to Lean tactic")
  return {
    id: t.id,
    data: t.data,
    children: t.children.map((g: Node) => nodeToLeanGoal(g))
  }
}



/* React */


function renderNode(n: Node, onClick: (clicked: Node) => Promise<void>): React.ReactNode {
  if (!n.visible) {
    return
  }

  return (
    <Fragment key={n.id}>
      <li onClick={() => onClick(n)}>{n.data} [{n.status}]</li>
      <ul> {n.children.map((child: Node) => renderNode(child, onClick))}</ul >
    </Fragment>)
}

function HoverflyTree({ root, onClick }: { root: Node, onClick: (n: Node) => Promise<void> },) {
  return (
    <>
      <ul>
        {renderNode(root, onClick)}
      </ul>
    </>
  )
}

function Hoverfly() {
  const [root, setRoot] = useState<Node | null>(null)
  const rs = useRpcSession()

  useEffect(() => {
    rs.call('getInitialState', "").then((st) => {
      const n = leanGoalToNode(st as LeanGoal)
      const selectedN: Node = { ...n, status: 'selected' }
      setRoot(selectedN)
    }
    )

  }, [rs, root])

  if (root !== null) {
    const onClick = async (n: Node) => {
      setRoot(await handleClick(root, n, rs))
    }
    return <><HoverflyTree root={root} onClick={onClick} /></>
  } else {
    return <p>Loading...</p>
  }
}

export default Hoverfly
