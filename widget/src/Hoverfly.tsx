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
  changeStatusAtId
} from './Tree'
// import './App.css'

/* Handler */

async function handleClick(root: Node, apiData: APIData, clicked: Node, rs: RpcSessionAtPos): Promise<Node> {

  if (clicked.status === 'selected') {
    console.log("Node " + clicked.id + " was already selected.")
    // User has clicked the already-selected node. Do nothing.
    return root
  }

  const nca = nearestCommonAncestorWithSelected(root, clicked.id)

  if (nca.id === clicked.id) {
    console.log("Case 1: nca " + nca.id + " clicked " + clicked.id)
    // previously selected node was a descendant of clicked node
    // cache applicable subtree of clicked node
    // change clicked node status to 'selected
    const ncaPostCache = cacheChild(nca)
    const ncaNewStatus: Node = { ...ncaPostCache, status: 'selected' }

    const update = async (n: Node) => n.id === nca.id ? ncaNewStatus : n
    const breakAfter = (n: Node) => n.id === nca.id
    return updateNodes(root, update, breakAfter)
  } else if (nca.status === 'selected') {
    console.log("Case 2: nca " + nca.id + " clicked " + clicked.id)
    // previously selected node was an ancestor of clicked node

    // if the previous node was a non-parent ancestor, the
    // current node should never have been clickable
    assert(nca.children.some((c: Node) => c.id === clicked.id),
      "Non-child descendant of selected node should not be clickable.")

    // change parent to semiselected
    const parentUpdated = await changeStatusAtSelected(root, 'semiselected')

    const breakAfter = (n: Node) => n.id === clicked.id
    if (clicked.explored) {
      console.log("Restoring cache.")
      // restore cache at clicked node

      if (!clicked.cache) {
        throw new
          Error("Attempted to restore nonexistent cache at node " + clicked.id)
      } else {
        const update = async (n: Node) => n.id === clicked.id ? (clicked.cache as Node) : n
        return updateNodes(parentUpdated, update, breakAfter)
      }
    } else {
      console.log("Unexplored node " + clicked.id)
      // change node status to selected
      const clickedUpdated = changeStatusAtId(parentUpdated, clicked.id, 'selected')

      const update = async (n: Node) => n.id === clicked.id
        ? n.kind === 'goal'
          ? { ...await getApplicableTactics(n, apiData, rs), explored: true }
          : await getSubgoals(n, apiData, rs)
        : n
      return updateNodes(await clickedUpdated, update, breakAfter)
    }
  } else {
    console.log("Case 3: nca " + nca.id + " clicked " + clicked.id)
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

type APIData = unknown

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
async function getApplicableTactics(n: Node, apiData: APIData, rs: RpcSessionAtPos): Promise<Node> {
  assert(n.kind == 'goal',
    "Called getApplicableTactics on tactic node " + n.id)

  const params = { id: n.id, apiData: apiData }
  const tactics: APINode[] = await rs.call("Backend.getApplicableTactics", params)
  const tsxTactics = tactics.map(APINodeToNode)
  return { ...n, children: tsxTactics }
}

// given a tactic node, returns the same node with
// subgoals added as children
async function getSubgoals(n: Node, apiData: APIData, rs: RpcSessionAtPos): Promise<Node> {
  assert(n.kind == 'tactic',
    "Called getSubgoals on goal node " + n.id)

  const params = { id: n.id, apiData: apiData }
  const subgoals: APINode[] = await rs.call("Backend.getSubgoals", params)
  const tsxGoals = subgoals.map(APINodeToNode)
  return { ...n, children: tsxGoals }
}

/* React */

function renderNode(n: Node, onClick: (clicked: Node) => Promise<void>): React.ReactNode {
  console.log("Rendering " + n.id)
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

// async function insertSkip(ec: EditorConnection, uri: DocumentUri, tacticRange: Range) {
//   // NOTE: We could use `insertText` instead here.
//   await ec.api.applyEdit({
//     documentChanges:
//       [TextDocumentEdit.create({ uri: uri, version: null },
//         [TextEdit.replace(tacticRange, `skip\n${" ".repeat(tacticRange.start.character)}myWidgetTactic`)])]
//   })
//   await ec.revealPosition({ line: tacticRange.start.line + 1, character: tacticRange.end.character, uri: uri })
// }


// async function insertTactic(ec: EditorConnection, uri: DocumentUri, tacticRange: Range) {
//   // TODO: could also use the case names instead of bullets
//   await ec.api.applyEdit({
//     documentChanges:
//       [TextDocumentEdit.create({ uri: uri, version: null },
//         [TextEdit.replace(tacticRange, `skip\n${" ".repeat(tacticRange.start.character)}myWidgetTactic`)])]
//   })
//   await ec.revealPosition({ line: tacticRange.start.line + 1, character: tacticRange.end.character, uri: uri })
// }

// TODO -- Docs for WithRpcRef say:
// All RPC requests are relative to an open file and an RPC session for that file.
// The client must first connect to the session using $/lean/rpc/connect
function Hoverfly(props: HoverflyProps) {
  const [root, setRoot] = useState<Node | null>(null)
  // TODO : make this APIData | string | error to model error all in one?
  const [apiData, setAPIData] = useState<APIData | null>(null)
  const [error, setError] = useState<string | null>(null);
  const rs = useRpcSession()
  const ec = useContext(EditorContext)

  useEffect(() => {
    rs.call('Backend.getInitialState', { goals: props.goals, pos: props.pos }).then(async st => {
      const [state, apiData] = st as [APINode, APIData]
      const root = APINodeToNode(state)
      const selectedRoot: Node = { ...root, status: 'selected' }
      const rootWithChildren = await getApplicableTactics(selectedRoot, apiData, rs)
      setRoot(rootWithChildren)
      setAPIData(apiData)
    }).catch((reason) => {
      console.error(reason)
      setError(reason?.message ?? String(reason))
    })

  }, [rs])

  if (root !== null && apiData !== null) {
    const onClick = async (n: Node) => {
      console.log("Clicked " + n.id)

      setRoot(await handleClick(root, apiData, n, rs))
    }
    return <><HoverflyTree root={root} onClick={onClick} /></>
  } else {
    if (error == null) {
      return <p>Loading...</p>
    } else {
      return <p>{error}</p>
    }
  }
}

export default Hoverfly
