import type { RpcSessionAtPos, DocumentPosition } from '@leanprover/infoview';
import {
  Node,
  assert,
  cacheChild,
  changeStatusAtId,
  changeStatusAtSelected,
  getNavParent,
  navChildren,
  nearestCommonAncestorWithSelected,
  updateNodes
} from './Tree'

export type APIData = {
  p: string
}

export type APINode = {
  isGoal: boolean
  id: number
  display: string
  tacticError: string | null
  noop: boolean
  originalId?: number | null
  leanOrder?: number | null
  sharedMVars?: string[] | null
}

export type NodeAndStateRef = { node: Node, stateRef: APIData }

export function APINodeToNode(n: APINode): Node {
  if (n.isGoal) {
    return {
      kind: 'goal',
      id: n.id,
      display: n.display,
      tacticError: undefined,
      noop: false,
      originalId: n.originalId ?? undefined,
      leanOrder: n.leanOrder ?? undefined,
      completed: false,
      status: 'unselected',
      visible: true,
      redirectTo: undefined,
      explored: false,
      cache: undefined,
      children: []
    }
  } else {
    return {
      kind: 'tactic',
      id: n.id,
      display: n.display,
      tacticError: n.tacticError ?? undefined,
      noop: n.noop,
      originalId: undefined,
      completed: false,
      status: 'unselected',
      visible: true,
      redirectTo: undefined,
      explored: false,
      cache: undefined,
      children: []
    }
  }
}

function APIClusterToNode(goals: APINode[]): Node {
  const children = goals.map(APINodeToNode)
  const ids = children.map((c) => c.id)
  const shared = goals[0]?.sharedMVars ?? []
  return {
    kind: 'cluster',
    id: ids.length > 0 ? -1 - Math.min(...ids) : -1,
    display: shared.join(', '),
    tacticError: undefined,
    noop: false,
    originalId: undefined,
    completed: false,
    status: 'unselected',
    visible: true,
    redirectTo: undefined,
    explored: false,
    cache: undefined,
    children
  }
}

export async function getApplicableTactics(
  n: Node,
  stateRef: APIData,
  rs: RpcSessionAtPos,
  pos: DocumentPosition): Promise<NodeAndStateRef> {

  assert(n.kind == 'goal',
    "Called getApplicableTactics on tactic node " + n.id)

  // get tactic list
  const params = { id: n.id, stateRef: stateRef, pos: pos }
  const [tactics, newStateRef]: [APINode[], APIData] =
    await rs.call("Backend.getApplicableTactics", params)
  const tsxTactics = tactics.map(APINodeToNode)

  return { node: { ...n, children: tsxTactics }, stateRef: newStateRef }
}

// given a tactic node, returns the same node with subgoals added as children,
// plus the updated server state ref
export async function getSubgoals(
  n: Node,
  stateRef: APIData,
  rs: RpcSessionAtPos,
  pos: DocumentPosition): Promise<NodeAndStateRef> {

  assert(n.kind == 'tactic', "Called getSubgoals on goal node " + n.id)

  // get subgoal list, grouped into clusters (one inner list per cluster)
  const params = { id: n.id, stateRef: stateRef, pos: pos }
  const [clusters, newStateRef]: [APINode[][], APIData] =
    await rs.call("Backend.getSubgoals", params)
  const tsxClusters = clusters.map(APIClusterToNode)

  return { node: { ...n, children: tsxClusters }, stateRef: newStateRef }
}

export async function handleClick(
  root: Node,
  stateRef: APIData,
  clicked: Node,
  rs: RpcSessionAtPos,
  pos: DocumentPosition): Promise<NodeAndStateRef> {

  if (clicked.status === 'selected') {
    // User has clicked the already-selected node.

    // if the node was the root, do nothing
    if (clicked.id === root.id) {
      console.info("Node " + clicked.id + " was already selected.")
      return { node: root, stateRef }
    } else {
      // "unselect" a node on double click, i.e. select its parent
      const parentCand = getNavParent(root, clicked.id)
      if (parentCand) {
        return handleClick(root, stateRef, parentCand, rs, pos)
      } else {
        //TODO error: this could mean we somehow didn't find clicked.id in the tree, or we clicked a cluster node somehow
        return { node: root, stateRef }
      }
    }
  } else {
    console.debug("Clicked unselected node: " + clicked.id + ".")
  }

  const nca = nearestCommonAncestorWithSelected(root, clicked.id)

  if (nca.id === clicked.id) {
    console.debug("Clicked node " + clicked.id + " is an ancestor of " +
      "previously selected node.")

    // cache applicable subtree of clicked node
    const ncaPostCache = cacheChild(nca)

    // change clicked node status to 'selected'
    const ncaNewStatus: Node = { ...ncaPostCache, status: 'selected' }

    // update tree
    const update = async (n: Node) => n.id === nca.id ? ncaNewStatus : n
    const breakAfter = (n: Node) => n.id === nca.id
    return { node: await updateNodes(root, update, breakAfter), stateRef }

  } else if (nca.status === 'selected') {
    console.debug("Previously selected node " + nca.id + " is an ancestor of" +
      " clicked node " + clicked.id + ".")

    // if the previous node was a non-parent ancestor, the
    // current node should never have been clickable (navChildren sees through
    // cluster wrappers, so a goal nested in a cluster still counts as a child)
    assert(navChildren(nca).some((c: Node) => c.id === clicked.id),
      "Non-child descendant of selected node should not be clickable.")

    // change parent to semiselected
    const parentUpdated = await changeStatusAtSelected(root, 'semiselected')

    const breakAfter = (n: Node) => n.id === clicked.id
    if (clicked.explored) {
      console.debug("Restoring cache at node " + clicked.id + ".")

      if (!clicked.cache) {
        throw new
          Error("Attempted to restore nonexistent cache at node " + clicked.id)

      } else {
        const update = async (n: Node) =>
          n.id === clicked.id ? (clicked.cache as Node) : n
        return {
          node: await updateNodes(parentUpdated, update, breakAfter),
          stateRef
        }
      }

    } else {
      console.debug("Clicked node " + clicked.id + " was not previously " +
        "explored.")

      // change node status to selected
      const clickedUpdated =
        await changeStatusAtId(parentUpdated, clicked.id, 'selected')

      let newStateRef = stateRef
      const update = async (n: Node) => {
        if (n.id !== clicked.id) return n
        const expanded = n.kind === 'goal'
          ? await getApplicableTactics(n, stateRef, rs, pos)
          : await getSubgoals(n, stateRef, rs, pos)
        newStateRef = expanded.stateRef
        return { ...expanded.node, explored: true }
      }

      return {
        node: await updateNodes(clickedUpdated, update, breakAfter),
        stateRef: newStateRef
      }
    }
  } else {
    console.debug("Clicked node " + clicked.id + " is not an ancestor of " +
      "previously selected node and vice versa. Nearest common ancestor: " +
      nca.id + ".")

    // new node should be an immediate (navigational) child of nca
    assert(navChildren(nca).some((c: Node) => c.id === clicked.id),
      "Non-child descendant of nearest common ancestor of previously " +
      "selected node and newly clicked node node should not be clickable.")

    // cache the previously-selected branch under nca. nca itself stays
    // semiselected (it remains an ancestor of the newly selected node); only
    // its selected/semiselected child is collapsed into a cache.
    const newNca = cacheChild(nca)
    const updateNca = async (n: Node) => n.id === nca.id ? newNca : n
    const breakAfterNca = (n: Node) => n.id === nca.id
    const cached = await updateNodes(root, updateNca, breakAfterNca)

    // select the clicked sibling, restoring its cache if it was previously
    // explored or otherwise fetching its children (mirrors the descend case).
    const breakAfter = (n: Node) => n.id === clicked.id
    if (clicked.explored) {
      console.debug("Restoring cache at node " + clicked.id + ".")

      if (!clicked.cache) {
        throw new
          Error("Attempted to restore nonexistent cache at node " + clicked.id)
      }

      const update = async (n: Node) =>
        n.id === clicked.id ? (clicked.cache as Node) : n
      return { node: await updateNodes(cached, update, breakAfter), stateRef }

    } else {
      console.debug("Clicked node " + clicked.id + " was not previously " +
        "explored.")

      // change node status to selected
      const clickedUpdated =
        await changeStatusAtId(cached, clicked.id, 'selected')

      let newStateRef = stateRef
      const update = async (n: Node) => {
        if (n.id !== clicked.id) return n
        const expanded = n.kind === 'goal'
          ? await getApplicableTactics(n, stateRef, rs, pos)
          : await getSubgoals(n, stateRef, rs, pos)
        newStateRef = expanded.stateRef
        return { ...expanded.node, explored: true }
      }

      return {
        node: await updateNodes(clickedUpdated, update, breakAfter),
        stateRef: newStateRef
      }
    }
  }
}
