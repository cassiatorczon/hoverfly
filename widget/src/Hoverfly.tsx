import { Fragment, useState, useEffect, useContext } from 'react'
import { useRpcSession, useAsync, mapRpcError, RpcSessionAtPos, EditorContext, PanelWidgetProps, EditorConnection, DocumentPosition } from '@leanprover/infoview';
import { DocumentUri, Position, Range, TextDocumentEdit, TextDocumentIdentifier, TextEdit } from "vscode-languageserver-protocol";
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
  apiData: APIData,
  clicked: Node,
  rs: RpcSessionAtPos,
  pos: DocumentPosition): Promise<Node> {

  if (clicked.status === 'selected') {
    // User has clicked the already-selected node. Do nothing.
    console.info("Node " + clicked.id + " was already selected.")
    return root
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
    return updateNodes(root, update, breakAfter)

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
        return updateNodes(parentUpdated, update, breakAfter)
      }

    } else {
      console.debug("Clicked node " + clicked.id + " was not previously " +
        "explored.")

      // change node status to selected
      const clickedUpdated =
        changeStatusAtId(parentUpdated, clicked.id, 'selected')

      const update = async (n: Node) => n.id === clicked.id
        ? n.kind === 'goal'
          ? { ...await getApplicableTactics(n, apiData, rs, pos), explored: true }
          : await getSubgoals(n, apiData, rs, pos)
        : n

      return updateNodes(await clickedUpdated, update, breakAfter)
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
    return updateNodes(root, updateClicked, breakAfterClicked)
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

// given a goal node, returns the same node with
// applicable tactics added as children
async function getApplicableTactics(
  n: Node,
  apiData: APIData,
  rs: RpcSessionAtPos,
  pos: DocumentPosition): Promise<Node> {

  assert(n.kind == 'goal',
    "Called getApplicableTactics on tactic node " + n.id)

  // get tactic list
  const params = { id: n.id, apiData: apiData, pos: pos }
  const tactics: APINode[] =
    await rs.call("Backend.getApplicableTactics", params)
  const tsxTactics = tactics.map(APINodeToNode)

  return { ...n, children: tsxTactics }
}

// given a tactic node, returns the same node with
// subgoals added as children
async function getSubgoals(
  n: Node,
  apiData: APIData,
  rs: RpcSessionAtPos,
  pos: DocumentPosition): Promise<Node> {

  assert(n.kind == 'tactic', "Called getSubgoals on goal node " + n.id)

  // get subgoal list
  const params = { id: n.id, apiData: apiData, pos: pos }
  const subgoals: APINode[] = await rs.call("Backend.getSubgoals", params)
  const tsxGoals = subgoals.map(APINodeToNode)

  return { ...n, children: tsxGoals }
}

/* React */

function renderNode(n: Node, onClick: (clicked: Node) => Promise<void>): React.ReactNode {
  console.info("Rendering node" + n.id)
  if (!n.visible) {
    return
  }

  return (
    <Fragment key={n.id}>
      <li onClick={() => onClick(n)}>{n.display} [{n.status}, {n.explored}, {n.id}, {n.kind}]</li>
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

type HoverflyProps = PanelWidgetProps & {
  root: APINode;
  apiData: APIData;
}

// TODO -- Docs for WithRpcRef say:
// All RPC requests are relative to an open file and an RPC session for that file.
// The client must first connect to the session using $/lean/rpc/connect
function Hoverfly(props: HoverflyProps) {
  const [root, setRoot] = useState<Node | null>(null)
  // const [apiData, setAPIData] = useState<APIData>(props.apiData)

  const rs = useRpcSession()

  if (root === null) {
    // update root selected status
    const selectedRoot = selectRoot(APINodeToNode(props.root))

    // update root children
    const rootWithChildren = useAsync(() =>
      getApplicableTactics(selectedRoot,
        props.apiData, rs, props.pos))

    if (rootWithChildren.state === 'resolved') {

      setRoot(rootWithChildren.value)
    } else {
      console.error("Call for children of root node not resolved.")
      // TODO: error behavior?
    }
  } else {
    const onClick = async (n: Node) => {
      console.info("Clicked node " + n.id)

      setRoot(await handleClick(root, props.apiData, n, rs, props.pos))
    }
    return <><HoverflyTree root={root} onClick={onClick} /></>
  }

}

export default Hoverfly
