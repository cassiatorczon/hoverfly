import {
  useState,
  useEffect,
  useRef,
  useContext,
  Fragment
} from 'react'
import {
  useRpcSession,
  useAsync,
  mapRpcError,
  EditorContext,
  PanelWidgetProps
} from '@leanprover/infoview';
import {
  Range,
  TextDocumentEdit,
  TextEdit
} from "vscode-languageserver-protocol";
import {
  Node,
  BadgeKind,
  badgeFor,
  MarkerKind,
  markerFor,
  selectRoot,
  findDescendant,
  isInactive,
  isFrontier,
  recomputeCompleted,
  recomputeVisible,
  recomputeInactive,
  succeedingChildren,
  groupLabel,
  groupTactics
} from './Tree'
import { serializeTree } from './Serialize'
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

function renderChildren(n: Node, ctx: RenderCtx): React.ReactNode {
  if (n.children.length === 0) return null

  if (n.kind !== 'goal') {
    return (
      <ul className="kids nested">
        {n.children.map((child: Node) => renderNode(child, ctx))}
      </ul>
    )
  }

  const isFailingTactic = (c: Node) =>
    c.kind === 'tactic' && c.tacticError !== undefined
  const isNoopTactic = (c: Node) =>
    c.kind === 'tactic' && c.tacticError === undefined && c.noop
  const isSolvesGoalTactic = (c: Node) =>
    c.kind === 'tactic' && c.solvesGoal
  const mainChildren = n.children.filter(
    (c: Node) => !isFailingTactic(c) && !isNoopTactic(c) && !isSolvesGoalTactic(c)
      && c.visible)
  const solvesGoalChildren =
    n.children.filter((c: Node) => isSolvesGoalTactic(c) && c.visible)
  const noopChildren =
    n.children.filter((c: Node) => isNoopTactic(c) && c.visible)
  const failingChildren =
    n.children.filter((c: Node) => isFailingTactic(c) && c.visible)

  return (
    <ul className="kids nested">
      {solvesGoalChildren.map((child: Node) => renderNode(child, ctx))}
      {renderTacticBucket(mainChildren, ctx)}
      {noopChildren.length > 0 &&
        <li>
          <details className="failing-group">
            <summary>
              {noopChildren.length} no-op{' '}
              {noopChildren.length === 1 ? 'tactic' : 'tactics'}
            </summary>
            <ul className="kids nested">
              {renderTacticBucket(noopChildren, ctx)}
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
            <ul className="kids nested">
              {renderTacticBucket(failingChildren, ctx)}
            </ul>
          </details>
        </li>}
    </ul>
  )
}

// Render one bucket, collapsing each prototactic's instantiations.
function renderTacticBucket(children: Node[], ctx: RenderCtx): React.ReactNode[] {
  return groupTactics(children).map((entry: Node | Node[]) => {
    if (!Array.isArray(entry)) return renderNode(entry, ctx)

    // A collapsed member's badge would otherwise be invisible, hiding stashed progress.
    const badges = entry.map((c: Node) => badgeFor(c, false))
      .filter((b: BadgeKind) => b !== 'none')

    return (
      <li key={'group-' + entry[0].id}>
        <details className="tactic-group">
          <summary>
            <div className="rowA tactic group-row">
              <span className="marker"><span className="caret">▸</span></span>
              <span className="disp">{groupLabel(entry)}</span>
              <span className="group-count">{entry.length} options</span>
              {badges.length > 0 &&
                <span className="group-badges">
                  {badges.map((b: BadgeKind, i: number) =>
                    <Fragment key={i}>{renderBadge(b)}</Fragment>)}
                </span>}
            </div>
          </summary>
          <ul className="kids nested">
            {entry.map((child: Node) => renderNode(child, ctx))}
          </ul>
        </details>
      </li>
    )
  })
}

function renderBadge(kind: BadgeKind): React.ReactNode {
  switch (kind) {
    case 'done':
      return <span className="badge-done" title="Completed">✓</span>
    case 'orphaned':
      return <span className="badge-orphaned"
        title={"This proof does not assign all reachable metavariables; it will "
          + "be discarded when this goal is copied into a branch that does assign "
          + "the metavariables."}>⚠</span> // TODO: clearer error message
    case 'cached-done':
      return <span className="badge-cached-done"
        title="A completed proof is stored here — go back to finish">★</span>
    case 'cached':
      return <span className="badge-cached"
        title="Cached — progress stored, no full proof yet">◕</span>
    case 'explored':
      return <span className="badge-explored" title="Already explored">•</span> // TODO: maybe we should highlight or sth instead
    case 'none':
      return null
  }
}

function renderMarker(kind: MarkerKind): React.ReactNode {
  switch (kind) {
    case 'goal':
      return '⏹'
    case 'run':
      return <span className="marker-badge"
        title="Apply the tactic">Run</span>
    case 'undo':
      return <span className="marker-badge"
        title="Return to this point (your progress will be saved)">Undo</span>
    case 'redo':
      return <span className="marker-badge"
        title="Restore your saved progress">Redo</span>
    case 'dot':
      return '⚫︎'
  }
}

type RenderCtx = {
  onClick: (clicked: Node) => Promise<void>,
  linkedId: number | undefined,
  setLinkedId: (id: number | undefined) => void
}

function scrollToNode(from: Element, id: number): void {
  const target = from.closest('.hf')?.querySelector(`[data-node-id="${id}"]`)
  target?.scrollIntoView({ block: 'nearest', behavior: 'smooth' })
}

function RedirectStub({ dir, target, title, ctx }: {
  dir: 'out' | 'in', target: number, title: string, ctx: RenderCtx
}) {
  return (
    <span className="redirect" title={title}
      onMouseEnter={() => ctx.setLinkedId(target)}
      onMouseLeave={() => ctx.setLinkedId(undefined)}
      onClick={(e) => {
        e.stopPropagation()
        scrollToNode(e.currentTarget, target)
      }}>
      {dir === 'out' ? `↗ moved to #${target}` : `↘ copy of #${target}`}
    </span>
  )
}

function renderNode(n: Node, ctx: RenderCtx, orphaned = false)
  : React.ReactNode {
  if (!n.visible) {
    return null
  }

  if (n.kind === 'cluster') {
    if (n.children.length <= 1) {
      return (
        <Fragment key={n.id}>
          {n.children.map((child: Node) => renderNode(child, ctx))}
        </Fragment>
      )
    }
    const unresolved = !n.children.some(isInactive)
    const shared = n.display
    return (
      <li key={n.id}>
        <div className="cluster">
          <div className="cluster-label">
            these goals share the following metavariables: {shared}
          </div>
          <ul className="kids nested">
            {n.children.map((child: Node) =>
              renderNode(child, ctx, unresolved /* → orphaned */))}
          </ul>
        </div>
      </li>
    )
  }

  const failed = n.kind === 'tactic' && n.tacticError !== undefined
  const solvesGoal = n.kind === 'tactic' && n.solvesGoal
  const successClass = n.kind === 'tactic'
    ? (failed ? 'fails' : n.noop ? 'noop' : 'succeeds') : ''
  const inactive = isInactive(n)
  const clickable = !failed && !inactive
  const onPath = n.status === 'selected' || n.status === 'semiselected'

  const frontier = n.kind === 'goal'
    ? isFrontier(n)
    : !failed && !n.noop && !onPath
  const stateClass =
    n.completed ? 'settled'
      : frontier ? 'frontier'
        : onPath ? 'chosen'
          : ''
  const marker = renderMarker(markerFor(n))

  const row = (
    <div className={`rowA ${n.kind} ${n.status} ${successClass} ${stateClass}`
      + (inactive ? ' inactive' : '')
      + (ctx.linkedId === n.id ? ' linked' : '')}
      data-node-id={n.id}
      onClick={clickable ? () => ctx.onClick(n) : undefined}>
      <span className="marker"
        title={stateClass === 'frontier' && n.kind === 'goal'
          ? "Still open — this goal needs a proof" : undefined}>
        {marker}
      </span>
      <span className={solvesGoal ? "disp solves-goal" : "disp"}>
        {n.display}
        {solvesGoal &&
          <span> [Solves the current goal.]</span>}
      </span>
      {n.redirectTo !== undefined &&
        <RedirectStub dir="out" target={n.redirectTo} ctx={ctx}
          title={"This goal continues as #" + n.redirectTo + ", carried under "
            + "the tactic that fixed the shared metavariable."} />}
      {n.kind === 'goal' && n.originalId !== undefined &&
        <RedirectStub dir="in" target={n.originalId} ctx={ctx}
          title={"Copied from #" + n.originalId + ", the goal superseded when "
            + "the tactic that fixed the shared metavariable was applied."} />}
      {renderBadge(badgeFor(n, orphaned))}
    </div>
  )

  return (
    <li key={n.id}>
      {failed && n.tacticError
        ? <HoverError message={n.tacticError}>{row}</HoverError>
        : row}
      {renderChildren(n, ctx)}
    </li>
  )
}

function HoverflyTree({ root, onClick, onWrite, scriptHasSorry }: {
  root: Node,
  onClick: (n: Node) => Promise<void>,
  onWrite: (() => Promise<void>) | undefined,
  scriptHasSorry: boolean
},) {
  const [linkedId, setLinkedId] = useState<number | undefined>(undefined)
  const [confirming, setConfirming] = useState(false)

  return (
    <div className="hf">
      <style>{hoverflyStyles}</style>
      {root.completed &&
        <div className="banner-done">
          ✓ Proof complete — a closing tactic sequence has been found.
        </div>}
      <div className="treeA">
        <ul className="kids flush">
          {renderNode(root, { onClick, linkedId, setLinkedId })}
        </ul>
      </div>
      <div className="toolbar">
        {confirming
          ? <span className="confirm">
              This will end your Hoverfly session. Are you sure you want to proceed?
              <button className="write-btn" onClick={onWrite}>Yes</button>
              <button className="write-btn incomplete" onClick={() => setConfirming(false)}>Cancel</button>
            </span>
          : <button className={scriptHasSorry ? "write-btn incomplete" : "write-btn"}
              disabled={!onWrite}
              title={onWrite
                ? "Replace `hoverfly` with the selected proof"
                : "No source range available to write into"}
              onClick={scriptHasSorry ? () => setConfirming(true) : onWrite}>
              {scriptHasSorry
                ? "Copy Incomplete Proof To File"
                : "Copy Proof to File"}
            </button>}
      </div>
    </div>
  )
}

type HoverflyProps = PanelWidgetProps & {
  root: APINode;
  apiData: APIData;
  range: Range | null; // span of the literal `hoverfly` tactic
}

// TODO -- Docs for WithRpcRef say:
// All RPC requests are relative to an open file and an RPC session for that
// file.
// The client must first connect to the session using $/lean/rpc/connect
function Hoverfly(props: HoverflyProps) {
  const numAutoclicks = 10 // TODO: make this a prop with a default value
  const rs = useRpcSession()
  const ec = useContext(EditorContext)

  // TODO this appears to be throwing an error
  // initialize state from root goal
  const loadedInit = useAsync(
    () => getApplicableTactics(
      selectRoot(APINodeToNode(props.root)), props.apiData, rs, props.pos),
    [props.root, props.apiData, rs, props.pos])

  let loaded = loadedInit;
  if (loadedInit.state === 'resolved') {
    let sChildren = succeedingChildren(loadedInit.value.node)
    if (sChildren.length == 1) {
      // TODO
      // loaded = await handleClick(loadedInit.value.node, loadedInit.value.stateRef,
      //   sChildren[0], rs, props.pos)
    }
  }


  // current tree state: a root node and a ref to backend state
  const [saved, setSaved] = useState<NodeAndStateRef | null>(null)

  // Drop cached state on re-elaboration
  useEffect(() => { setSaved(null) }, [props.apiData, props.pos, rs])

  // if there is a saved state, use that
  // otherwise use initialized state if resolved
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

      const wasExplored = n.explored

      const newRoot = await handleClick(current.node, current.stateRef, n, rs, props.pos)
      setSaved(newRoot)

      if (newRoot) {
        let newNode = findDescendant(newRoot.node, n.id)

        if (newNode) {
          let sChildren = succeedingChildren(newNode)
          if (!wasExplored && sChildren.length == 1) {
            let child = sChildren[0]
            console.info("Auto-clicking " + child.id)

            setSaved(
              await handleClick(newRoot.node, newRoot.stateRef, child, rs, props.pos)
            )
          } else {
            console.debug(newNode.id + " had " + (wasExplored ? "" : "not ") +
              "been previously explored and has " + newNode.children.length +
              " total children and " + succeedingChildren.length +
              " successful children. No auto-clicking will occur.")
            console.debug("Is explored " + newNode.explored)
          }
        } else {
          // TODO is this the error behavior we want
          console.error("No new node found with id " + n.id)
        }
      } else {
        // TODO is this the error behavior we want
        console.error("No new root found after clicking " + n.id)
      }

    }

    // `inactive`, `completed`, and `visible` are all derived from tree
    // structure, so compute a fresh display copy here rather than threading them
    // through every click. Order matters: `recomputeCompleted` reads `inactive`
    // (an inactive original counts as discharged). Click logic still operates on
    // `current.node` (the source of truth) above.
    const displayRoot =
      recomputeVisible(recomputeCompleted(recomputeInactive(current.node)))

    // Serialize the selected sub-tree into a tactic script and replace the
    // `hoverfly` token with it. Disabled when the elaborator gave us no range.
    const scriptHasSorry = /\bsorry\b/.test(serializeTree(displayRoot))
    const range = props.range
    const onWrite = range === null ? undefined : async () => {
      // Indent continuation lines to the column of the `hoverfly` token so the
      // spliced-in block stays aligned inside the `by` block.
      const newText =
        serializeTree(displayRoot, ' '.repeat(range.start.character))
      const edit: TextDocumentEdit = {
        textDocument: { uri: props.pos.uri, version: null },
        edits: [{ range, newText } as TextEdit]
      }
      await ec.api.applyEdit({ documentChanges: [edit] })
    }

    return <><HoverflyTree root={displayRoot} onClick={onClick}
      onWrite={onWrite} scriptHasSorry={scriptHasSorry} /></>
  }
}

export default Hoverfly
