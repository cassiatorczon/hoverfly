import { Fragment, useState, useContext } from 'react'
import {
  useRpcSession,
  useAsync,
  mapRpcError,
  RpcSessionAtPos,
  EditorContext,
  PanelWidgetProps,
  EditorConnection, DocumentPosition
} from '@leanprover/infoview';
import {
  DocumentUri,
  Position,
  Range,
  TextDocumentEdit,
  TextDocumentIdentifier,
  TextEdit
} from "vscode-languageserver-protocol";
import {
  Node,
  assert,
  nearestCommonAncestorWithSelected,
  cacheChild,
  updateNodes,
  changeStatusAtSelected,
  changeStatusAtId,
  selectRoot
} from './Tree'
// import './App.css'

/* Handler */

async function handleClick(
  root: Node,
  stateRef: APIData,
  clicked: Node,
  rs: RpcSessionAtPos,
  pos: DocumentPosition): Promise<NodeAndStateRef> {

  if (clicked.status === 'selected') {
    // User has clicked the already-selected node. Do nothing.
    console.info("Node " + clicked.id + " was already selected.")
    return { node: root, stateRef }
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
    // current node should never have been clickable
    assert(nca.children.some((c: Node) => c.id === clicked.id),
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
        return n.kind === 'goal'
          ? { ...expanded.node, explored: true }
          : expanded.node
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
    return {
      node: await updateNodes(root, updateClicked, breakAfterClicked),
      stateRef
    }
  }
}

/* External */

type APIData = {
  p: string
}

type APINode = {
  isGoal: boolean
  id: number
  display: string
}


function APINodeToNode(n: APINode): Node {
  if (n.isGoal) {
    return {
      kind: 'goal',
      id: n.id,
      display: n.display,
      completed: false,
      status: 'unselected',
      visible: true,
      explored: false,
      cache: undefined,
      children: []
    }
  } else {
    return {
      kind: 'tactic',
      id: n.id,
      display: n.display,
      completed: false,
      status: 'unselected',
      visible: true,
      explored: false,
      cache: undefined,
      children: []
    }
  }
}

type NodeAndStateRef = { node: Node, stateRef: APIData }

async function getApplicableTactics(
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
async function getSubgoals(
  n: Node,
  stateRef: APIData,
  rs: RpcSessionAtPos,
  pos: DocumentPosition): Promise<NodeAndStateRef> {

  assert(n.kind == 'tactic', "Called getSubgoals on goal node " + n.id)

  // get subgoal list
  const params = { id: n.id, stateRef: stateRef, pos: pos }
  const [subgoals, newStateRef]: [APINode[], APIData] =
    await rs.call("Backend.getSubgoals", params)
  const tsxGoals = subgoals.map(APINodeToNode)

  return { node: { ...n, children: tsxGoals }, stateRef: newStateRef }
}

/* React */

function renderNode(n: Node, onClick: (clicked: Node) => Promise<void>)
  : React.ReactNode {
  console.info("Rendering node" + n.id)
  if (!n.visible) {
    return
  }

  return (
    <Fragment key={n.id}>
      <li onClick={() => onClick(n)}>
        {n.display} [{n.status}, {n.explored}, {n.id}, {n.kind}]</li>
      <ul> {n.children.map((child: Node) => renderNode(child, onClick))}</ul >
    </Fragment>)
}

function HoverflyTree({ root, onClick }: {
  root: Node, onClick: (n: Node) =>
    Promise<void>
},) {
  return (
    <>
      <ul>
        {renderNode(root, onClick)}
      </ul>
    </>
  )
}

type HoverflyProps = PanelWidgetProps & {
  root: APINode;
  apiData: APIData;
}

// TODO -- Docs for WithRpcRef say:
// All RPC requests are relative to an open file and an RPC session for that
// file.
// The client must first connect to the session using $/lean/rpc/connect
function Hoverfly(props: HoverflyProps) {
  const rs = useRpcSession()

  const loaded = useAsync(
    () => getApplicableTactics(
      selectRoot(APINodeToNode(props.root)), props.apiData, rs, props.pos),
    [props.root, props.apiData, rs, props.pos])

  // NOTE: Once set, this overrides the root from async. That's intended (async
  // is for initialization), but could be annoying later if it isn't.
  const [saved, setSaved] = useState<NodeAndStateRef | null>(null)
  const current = saved ?? (loaded.state === 'resolved' ? loaded.value : null)

  if (current === null) {
    if (loaded.state === 'rejected') {
      console.error("Call for children of root node failed: ",
        mapRpcError(loaded.error))
      return <>Failed to load.</>
    }
    return <>Loading...</>
  }

  const onClick = async (n: Node) => {
    console.info("Clicked node " + n.id)
    setSaved(
      await handleClick(current.node, current.stateRef, n, rs, props.pos))
  }
  return <><HoverflyTree root={current.node} onClick={onClick} /></>
}

export default Hoverfly
