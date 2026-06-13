import { useState, useEffect, useContext } from 'react'
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
  selectRoot,
  recomputeCompleted
} from './Tree'
import {
  APIData,
  APINode,
  NodeAndStateRef,
  APINodeToNode,
  getApplicableTactics,
  handleClick
} from './Handler'
import hoverflyStyles from './styles.css'

/* React */

function renderNode(n: Node, onClick: (clicked: Node) => Promise<void>)
  : React.ReactNode {
  if (!n.visible) {
    return null
  }

  const marker = n.kind === 'goal' ? '⊢' : '▸'

  return (
    <li key={n.id}>
      <div className={`rowA ${n.kind} ${n.status}`} onClick={() => onClick(n)}>
        <span className="marker">{marker}</span>
        <span className="disp">{n.display}</span>
        {n.completed && <span className="badge-done">✓</span>}
        <span className="id">#{n.id}</span>
      </div>
      {n.children.length > 0 &&
        <ul className="kids">
          {n.children.map((child: Node) => renderNode(child, onClick))}
        </ul>}
    </li>
  )
}

function HoverflyTree({ root, onClick }: {
  root: Node, onClick: (n: Node) =>
    Promise<void>
},) {
  return (
    <div className="hf">
      <style>{hoverflyStyles}</style>
      {root.completed &&
        <div className="banner-done">
          ✓ Proof complete — a closing tactic sequence has been found.
        </div>}
      <div className="treeA">
        <ul>
          {renderNode(root, onClick)}
        </ul>
      </div>
    </div>
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

  const [saved, setSaved] = useState<NodeAndStateRef | null>(null)

  // Drop cached state on re-elaboration
  useEffect(() => { setSaved(null) }, [props.apiData, props.pos, rs])

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

  // `completed` is derived from tree structure, so compute a fresh display
  // copy here rather than threading it through every click. Click logic still
  // operates on `current.node` (the source of truth) above.
  const displayRoot = recomputeCompleted(current.node)
  return <><HoverflyTree root={displayRoot} onClick={onClick} /></>
}

export default Hoverfly
