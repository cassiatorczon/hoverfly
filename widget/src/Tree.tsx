
type ID = number

type Kind = "tactic" | "goal"

type Status = "selected" | "semiselected" | "unselected"

type MutableNode = {
  kind: Kind, // tactic or goal
  id: ID, // should be unique among all nodes; must have an immutable type
  display: string, // display
  completed: boolean, // a completed goal or tactic with all completed subgoals
  children: Node[], // applicable tactics for a goal, subgoals for a tactic
  status: Status, // display information
  visible: boolean, // visibility in display
  explored: boolean, // whether the node has been explored
  cache: Node | undefined // previous version of the subtree rooted at this node
}

export type Node = Readonly<MutableNode>

/* Check tree invariants */

function checkUniqueIDs(n: Node, ids: Set<ID>): void {
  // assert(!ids.has(n.id), "Malformed tree: duplicate ID (" + n.id + ").")

  // // TODO does the state here persist correctly
  // var newIds = ids.add(n.id)
  // for (var c of n.children) {
  //   checkUniqueIDs(c, newIds)
  // }
}

function checkKinds(n: Node, expectedKind: Kind): void {
  // assert(n.kind === expectedKind, "Malformed tree: expected node " + n.id
  //   + " to have kind " + expectedKind + ", but found kind " + n.kind + ".")

  // const nextKind = expectedKind === 'goal' ? 'tactic' : 'goal'
  // n.children.forEach((c: Node) => checkKinds(c, nextKind))
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
  // // report errors at leaves first
  // n.children.forEach((c: Node) => checkCompletedness(c))

  // let shouldBeCompleted = n.kind === 'goal'
  //   ? n.children.some((c: Node) => c.completed)
  //   : n.children.every((c: Node) => c.completed)
  // assert(shouldBeCompleted === n.completed,
  //   "Incorrect 'completed' field for node " + n.id + "; expected "
  //   + shouldBeCompleted + " but found " + n.completed + ".")
}

export function checkTree(root: Node): void {
  // // root is a goal
  // // all goals have only tactic children
  // // all tactics have only goal children
  // checkKinds(root, 'goal')

  // // all IDs are unique
  // checkUniqueIDs(root, new Set<ID>())

  // // exactly one node is selected
  // // no grandchildren of selected node are visible
  // // no "cousins" of selected node are visible
  // // immediate children and all ancestors of selected goal
  // //   are visible (and selected goal itself)
  // // ancestor of selected goal iff 'semiselected'
  // checkStatusAndVisibility(root)

  // // a goal is completed iff at least one of its children is completed
  // // a tactic is completed iff it has no uncompleted children
  // checkCompletedness(root)
}

/* Update tree */

export async function updateNodes(
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

export async function changeStatusAtSelected(root: Node, newStatus: Status): Promise<Node> {
  const update = async (n: Node) => n.status === 'selected'
    ? { ...n, status: newStatus } : n
  const breakAfter = (n: Node) => n.status === 'selected'
  return updateNodes(root, update, breakAfter)
}

export function selectRoot(root: Node): Node {
  return { ...root, status: 'selected' }
}

export async function changeStatusAtId(root: Node, id: ID, newStatus: Status): Promise<Node> {
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

export function cacheChild(n: Node): Node {
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

export function nearestCommonAncestorWithSelected(n: Node, id: ID):
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
    // assert(n.status === 'selected',
    //   "Malformed tree: [" + n.display + "] is not selected and has no selected or"
    //   + " semiselected immediate children")
    return n
  }
}

/* Util */

export function assert(p: boolean, e: string): void {
  if (!p) {
    throw new Error(e)
  }
}