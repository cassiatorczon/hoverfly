import { useState, useEffect, useContext, useRef } from 'react'
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
  recomputeCompleted,
  recomputeVisible
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

function HoverError({ message, children }: {
  message: string, children: React.ReactNode
}) {
  const [show, setShow] = useState(false)
  const timer = useRef<ReturnType<typeof setTimeout> | null>(null)

  const clear = () => {
    if (timer.current !== null) {
      clearTimeout(timer.current)
      timer.current = null
    }
  }
  const onEnter = () => {
    clear()
    timer.current = setTimeout(() => setShow(true), 500)
  }
  const onLeave = () => {
    clear()
    setShow(false)
  }

  return (
    <div className="err-wrap" onMouseEnter={onEnter} onMouseLeave={onLeave}>
      {children}
      {show && <div className="err-tooltip">{message}</div>}
    </div>
  )
}

function renderNode(n: Node, onClick: (clicked: Node) => Promise<void>)
  : React.ReactNode {
  if (!n.visible) {
    return null
  }

  const marker = n.kind === 'goal' ? '⊢' : '▸'
  const failed = n.kind === 'tactic' && n.tacticError !== undefined
  const successClass = n.kind === 'tactic'
    ? (n.tacticError === undefined ? 'succeeds' : 'fails') : ''

  const isFailingTactic = (c: Node) =>
    c.kind === 'tactic' && c.tacticError !== undefined
  const mainChildren = n.children.filter((c: Node) => !isFailingTactic(c))
  const failingChildren =
    n.children.filter((c: Node) => isFailingTactic(c) && c.visible)

  const row = (
    <div className={`rowA ${n.kind} ${n.status} ${successClass}`}
      onClick={failed ? undefined : () => onClick(n)}>
      <span className="marker">{marker}</span>
      <span className="disp">{n.display}</span>
      {n.cache
        ? (n.cache.completed
          ? (n.kind === 'goal'
            ? <span className="badge-done" title="Completed">✓</span>
            : <span className="badge-cached-done"
              title="A completed proof is stored here — go back to finish">★</span>)
          : <span className="badge-cached"
            title="Cached — progress stored, no full proof yet">☆</span>)
        : n.completed
          ? <span className="badge-done" title="Completed">✓</span>
          : n.explored
            ? <span className="badge-explored" title="Already explored">•</span>
            : null}
      <span className="id">#{n.id}</span>
    </div>
  )

  return (
    <li key={n.id}>
      {failed && n.tacticError
        ? <HoverError message={n.tacticError}>{row}</HoverError>
        : row}
      {n.children.length > 0 &&
        <ul className="failing-children">
          {mainChildren.map((child: Node) => renderNode(child, onClick))}
          {failingChildren.length > 0 &&
            <li>
              <details className="failing-group">
                <summary>
                  {failingChildren.length} failing{' '}
                  {failingChildren.length === 1 ? 'tactic' : 'tactics'}
                </summary>
                <ul className="failing-children">
                  {failingChildren.map((child: Node) =>
                    renderNode(child, onClick))}
                </ul>
              </details>
            </li>}
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
  } else {
    const onClick = async (n: Node) => {
      console.info("Clicked node " + n.id)
      setSaved(
        await handleClick(current.node, current.stateRef, n, rs, props.pos))
    }

    // `completed` and `visible` are derived from tree structure, so compute a
    // fresh display copy here rather than threading them through every click.
    // Click logic still operates on `current.node` (the source of truth) above.
    const displayRoot = recomputeVisible(recomputeCompleted(current.node))
    return <><HoverflyTree root={displayRoot} onClick={onClick} /></>
  }
}

export default Hoverfly
