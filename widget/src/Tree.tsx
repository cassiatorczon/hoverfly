
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
  leanOrder?: number, // for goals: position in Lean's goal order under the parent tactic
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
    // A cluster's completion state is a bit complicted, because it is neither
    // fully an AND node nor fully an OR node. Key facts include:
    // - A cluster with exactly one goal is complete when its goal is complete.
    // - A cluster with more than one goal is complete when one of those goals
    //   is complete and the others are inactive. If a goal is complete but its
    //   siblings are not inactive, then the goal was closed without instantiating
    //   the relevant mvars and the proof cannot be completed from that point.
    // The code below implements this logic.
    const active = children.filter((c: Node) => !isInactive(c))
    const resolved = children.some(isInactive)
    completed = active.every((c: Node) => c.completed)
      && (children.length < 2 || resolved)
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
    children: n.children.map(annotate),
    cache: n.cache ? recomputeInactive(n.cache) : undefined
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

/* Status badge selection */

export type BadgeKind =
  | 'done'          // ✓ committed completion
  | 'orphaned'      // ⚠ closes the goal without assigning the shared mvar
  | 'cached-done'   // ★ a completed proof is stashed off the active path
  | 'cached'        // ☆ progress stashed, no full proof yet
  | 'explored'      // • visited, nothing proven
  | 'none'          // no badge

export function badgeFor(n: Node, orphaned: boolean): BadgeKind {
  // A copied goal has no badge: any proof it holds is moot until backtracking reactivates it. The
  // greying and `↪` redirect already mark it.
  if (isInactive(n)) return 'none'

  if (n.cache) {
    if (!n.cache.completed) return 'cached'
    // A goal's stashed proof is a real completion (or orphaned in a cluster); a tactic's is off the
    // active path, so it reads as "stored, go finish".
    if (n.kind === 'goal') return orphaned ? 'orphaned' : 'done'
    return 'cached-done'
  }

  if (n.completed) return orphaned ? 'orphaned' : 'done'
  if (n.explored) return 'explored'
  return 'none'
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

export function findDescendant(n: Node, id: ID): Readonly<Node> | undefined {
  if (n.id == id) {
    return n
  }
  for (const c of n.children) {
    const found = findDescendant(c, id)
    if (found) {
      return found
    }
  }
}

export function succeedingChildren(n: Node): Readonly<Node>[] {
  return navChildren(n).filter((c) =>
    c.kind !== 'tactic' || (!c.noop && !c.tacticError))
}

/* Util */

export function assert(p: boolean, e: string): void {
  if (!p) {
    throw new Error(e)
  }
}