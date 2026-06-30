import { useState, useEffect, useContext, useRef, Fragment } from 'react'
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
  isInactive,
  recomputeCompleted,
  recomputeVisible,
  recomputeInactive
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

function renderChildren(n: Node, onClick: (clicked: Node) => Promise<void>)
  : React.ReactNode {
  if (n.children.length === 0) return null

  if (n.kind !== 'goal') {
    return (
      <ul className="failing-children">
        {n.children.map((child: Node) => renderNode(child, onClick))}
      </ul>
    )
  }

  const isFailingTactic = (c: Node) =>
    c.kind === 'tactic' && c.tacticError !== undefined
  const isNoopTactic = (c: Node) =>
    c.kind === 'tactic' && c.tacticError === undefined && c.noop
  const mainChildren = n.children.filter(
    (c: Node) => !isFailingTactic(c) && !isNoopTactic(c))
  const noopChildren =
    n.children.filter((c: Node) => isNoopTactic(c) && c.visible)
  const failingChildren =
    n.children.filter((c: Node) => isFailingTactic(c) && c.visible)

  return (
    <ul className="failing-children">
      {mainChildren.map((child: Node) => renderNode(child, onClick))}
      {noopChildren.length > 0 &&
        <li>
          <details className="failing-group">
            <summary>
              {noopChildren.length} no-op{' '}
              {noopChildren.length === 1 ? 'tactic' : 'tactics'}
            </summary>
            <ul className="failing-children">
              {noopChildren.map((child: Node) => renderNode(child, onClick))}
            </ul>
          </details>
        </li>}
      {failingChildren.length > 0 &&
        <li>
          <details className="failing-group">
            <summary>
              {failingChildren.length} failing{' '}
              {failingChildren.length === 1 ? 'tactic' : 'tactics'}
            </summary>
            <ul className="failing-children">
              {failingChildren.map((child: Node) => renderNode(child, onClick))}
            </ul>
          </details>
        </li>}
    </ul>
  )
}

function renderNode(n: Node, onClick: (clicked: Node) => Promise<void>)
  : React.ReactNode {
  if (!n.visible) {
    return null
  }

  // A cluster is a visual grouping of sibling goals linked by a shared
  // metavariable. Singletons render transparently (just the goal); a real
  // cluster (≥2 goals) gets a labelled box.
  if (n.kind === 'cluster') {
    if (n.children.length <= 1) {
      return (
        <Fragment key={n.id}>
          {n.children.map((child: Node) => renderNode(child, onClick))}
        </Fragment>
      )
    }
    return (
      <li key={n.id}>
        <div className="cluster">
          <div className="cluster-label">
            linked goals — share a metavariable
          </div>
          <ul className="failing-children">
            {n.children.map((child: Node) => renderNode(child, onClick))}
          </ul>
        </div>
      </li>
    )
  }

  const marker = n.kind === 'goal' ? '⊢' : '▸'
  const failed = n.kind === 'tactic' && n.tacticError !== undefined
  const successClass = n.kind === 'tactic'
    ? (n.tacticError === undefined ? 'succeeds' : 'fails') : ''
  const inactive = isInactive(n)
  const clickable = !failed && !inactive

  const row = (
    <div className={`rowA ${n.kind} ${n.status} ${successClass}`
      + (inactive ? ' inactive' : '')}
      onClick={clickable ? () => onClick(n) : undefined}>
      <span className="marker">{marker}</span>
      <span className="disp">{n.display}</span>
      {n.redirectTo !== undefined &&
        <span className="redirect"
          title={"This goal continues as #" + n.redirectTo + ", carried under "
            + "the tactic that fixed the shared metavariable."}>
          ↪ #{n.redirectTo}
        </span>}
      {n.kind === 'goal' && n.originalId !== undefined &&
        <span className="redirect"
          title={"Copied from #" + n.originalId + ", the goal superseded when "
            + "the tactic that fixed the shared metavariable was applied."}>
          ↩ #{n.originalId}
        </span>}
      {n.cache
        ? (n.cache.completed
          ? (n.kind === 'goal'
            ? <span className="badge-done" title="Completed">✓</span>
            : <span className="badge-cached-done"
              title="A completed proof is stored here — go back to finish">★</span>)
          : <span className="badge-cached"
            title="Cached — progress stored, no full proof yet">☆</span>)
        : n.completed && !inactive
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
      {renderChildren(n, onClick)}
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

    // `inactive`, `completed`, and `visible` are all derived from tree
    // structure, so compute a fresh display copy here rather than threading them
    // through every click. Order matters: `recomputeCompleted` reads `inactive`
    // (an inactive original counts as discharged). Click logic still operates on
    // `current.node` (the source of truth) above.
    const displayRoot =
      recomputeVisible(recomputeCompleted(recomputeInactive(current.node)))
    return <><HoverflyTree root={displayRoot} onClick={onClick} /></>
  }
}

export default Hoverfly
