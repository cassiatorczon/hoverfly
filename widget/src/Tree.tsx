
type ID = number

type Kind = "tactic" | "goal" | "cluster"

type Status = "selected" | "semiselected" | "unselected"

type MutableNode = {
  kind: Kind, // tactic, goal, or cluster
  id: ID, // should be unique among all nodes; must have an immutable type
  display: string, // display
  tacticError: string | undefined, // for failing tactics: why it failed; undefined ⇒ succeeded (or goal)
  noop: boolean, // for tactics: succeeded but left the proof state unchanged
  originalId: ID | undefined, // the ID of the node this has been copied from, if applicable
  completed: boolean, // a completed goal or tactic with all completed subgoals
  children: Node[], // applicable tactics for a goal, clusters for a tactic, goals for a cluster
  status: Status, // display information
  visible: boolean, // visibility in display
  redirectTo: ID | undefined, // if this goal has been copied, what has it been copied to
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

export function navChildren(n: Node): Node[] {
  return n.children.flatMap((c: Node) =>
    c.kind === 'cluster' ? c.children : [c])
}

function selectedChild(n: Node): Node | undefined {
  return navChildren(n).find(
    (c: Node) => c.status === 'selected' || c.status === 'semiselected')
}

function cacheIfSelected(n: Node): Node {
  if (n.status === 'selected' || n.status === 'semiselected') {
    return { ...n, status: 'unselected', cache: n, children: [] }
  }
  return n
}

export function cacheChild(n: Node): Node {
  let newChildren = n.children.map((c: Node) =>
    c.kind === 'cluster'
      ? { ...c, children: c.children.map(cacheIfSelected) }
      : cacheIfSelected(c))
  return { ...n, children: newChildren }
}

export function isInactive(n: Node): boolean {
  return n.redirectTo !== undefined
}

// Recompute the `completed` flag for every node from the structure of the
// tree. Completion is derived rather than stored, to keep us from having to
// maintain it at every node separately.
export function recomputeCompleted(n: Node): Node {
  const children = n.children.map(recomputeCompleted)
  const cache = n.cache ? recomputeCompleted(n.cache) : undefined

  let completed: boolean
  if (n.kind === 'cluster') {
    // A cluster's goals must all be discharged (AND), like a tactic's subgoals.
    completed = children.every((c: Node) => c.completed)
  } else if (n.kind === 'goal' && isInactive(n)) {
    // An inactive goal has been superseded by a live copy under the driving
    // tactic; that copy carries the obligation and is gated by a sibling branch,
    // so this original counts as discharged here.
    completed = true
  } else if (children.length === 0 && cache) {
    // A cached goal is completed if the cached tree is completed; a cached
    // tactic is _never_ completed, since caching it means we've moved away
    // from it.
    completed = n.kind === 'goal' ? cache.completed : false
  } else if (n.kind === 'tactic') {
    completed = n.explored && children.every((c: Node) => c.completed)
  } else {
    completed = children.some((c: Node) => c.completed)
  }

  return { ...n, children, cache, completed }
}

// Recompute the `redirectTo` pointer (and hence `isInactive`)
// from structure, like `completed`. When a tactic assigns a metavariable shared
// across a cluster, the backend carries the still-open sibling goals as *copy*
// children of that tactic, each tagged with the `originalId` of the sibling it
// copies. On the active path the original sibling is then superseded: greyed,
// non-actionable, its obligation moved to the copy.
export function recomputeInactive(root: Node): Node {
  const redirect = new Map<ID, ID>()
  const collect = (n: Node): void => {
    for (const c of n.children) {
      if (c.originalId !== undefined) redirect.set(c.originalId, c.id)
      collect(c)
    }
  }
  collect(root)

  const annotate = (n: Node): Node => ({
    ...n,
    redirectTo: redirect.get(n.id),
    children: n.children.map(annotate)
  })
  return annotate(root)
}

// Recompute the `visible` flag for every node. Once a tactic is chosen (one of
// a goal's tactic children is on the active path), all of its siblings are
// hidden — including cached ones. To revisit a previously explored sibling you
// backtrack to the parent goal, which re-selects it and brings the whole tactic
// menu (with cache badges) back. Like `recomputeCompleted`, this is derived at
// render time rather than threaded through the click logic.
export function recomputeVisible(n: Node): Node {
  const hasActiveTactic = n.kind === 'goal' &&
    n.children.some((c: Node) =>
      c.status === 'selected' || c.status === 'semiselected')

  const children = n.children.map((c: Node) =>
    recomputeVisible({
      ...c,
      visible: !(hasActiveTactic && c.status === 'unselected')
    }))

  return { ...n, children }
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
  const selectedNonstrictAncestor = selectedChild(n)
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