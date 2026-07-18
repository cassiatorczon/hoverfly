import {
  useState,
  useEffect,
  useLayoutEffect,
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
  selectRoot,
  findDescendant,
  navChildren,
  isInactive,
  recomputeCompleted,
  recomputeVisible,
  recomputeInactive,
  succeedingChildren
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
      return <span className="badge-explored" title="Already explored">•</span> // todo: maybe we should highlight or sth instead
    case 'none':
      return null
  }
}

const PAIR_STROKE = 'var(--vscode-textLink-foreground)'

type PairLink = { from: number, to: number, key: number }
function collectPairs(n: Node, acc: PairLink[] = []): PairLink[] {
  if (n.redirectTo !== undefined) {
    acc.push({ from: n.id, to: n.redirectTo, key: n.id })
  }
  n.children.forEach((c: Node) => collectPairs(c, acc))
  return acc
}

function renderNode(
  n: Node, onClick: (clicked: Node) => Promise<void>, orphaned = false)
  : React.ReactNode {
  if (!n.visible) {
    return null
  }

  if (n.kind === 'cluster') {
    if (n.children.length <= 1) {
      return (
        <Fragment key={n.id}>
          {n.children.map((child: Node) => renderNode(child, onClick))}
        </Fragment>
      )
    }
    const unresolved = !n.children.some(isInactive)
    return (
      <li key={n.id}>
        <div className="cluster">
          <div className="cluster-label">
            linked goals — share a metavariable
          </div>
          <ul className="failing-children">
            {n.children.map((child: Node) =>
              renderNode(child, onClick, unresolved /* → orphaned */))}
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
      data-node-id={n.id}
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
      <span className="id">#{n.id}</span>
      {renderBadge(badgeFor(n, orphaned))}
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

type DrawnLink = { d: string, head: string, color: string }

function HoverflyTree({ root, onClick, onWrite, scriptHasSorry }: {
  root: Node,
  onClick: (n: Node) => Promise<void>,
  onWrite: (() => Promise<void>) | undefined,
  scriptHasSorry: boolean
},) {
  const treeRef = useRef<HTMLDivElement>(null)
  const [links, setLinks] = useState<DrawnLink[]>([])
  const [size, setSize] = useState<{ w: number, h: number }>({ w: 0, h: 0 })

  // Layout effect to render arrows connecting copied goals
  useLayoutEffect(() => {
    const container = treeRef.current
    if (!container) return

    const compute = () => {
      const cRect = container.getBoundingClientRect()
      const rel = (el: Element) => {
        const r = el.getBoundingClientRect()
        return {
          left: r.left - cRect.left + container.scrollLeft,
          top: r.top - cRect.top + container.scrollTop,
          height: r.height
        }
      }

      const drawn: DrawnLink[] = []
      collectPairs(root).forEach((p: PairLink, i: number) => {
        const a = container.querySelector(`[data-node-id="${p.from}"]`)
        const b = container.querySelector(`[data-node-id="${p.to}"]`)
        if (!a || !b) return
        const ra = rel(a), rb = rel(b)
        const startX = ra.left, startY = ra.top + ra.height / 2
        const endX = rb.left, endY = rb.top + rb.height / 2
        // Each pair gets its own channel so multiple connectors don't overlap.
        const channelX = Math.max(2, Math.min(ra.left, rb.left) - 10 - i * 6)
        drawn.push({
          d: `M ${startX} ${startY} H ${channelX} V ${endY} H ${endX}`,
          head: `M ${endX} ${endY} L ${endX - 6} ${endY - 3} `
            + `L ${endX - 6} ${endY + 3} Z`,
          color: PAIR_STROKE
        })
      })

      setLinks(drawn)
      const w = container.scrollWidth, h = container.scrollHeight
      setSize((prev) => prev.w === w && prev.h === h ? prev : { w, h })
    }

    compute()
    const ro = new ResizeObserver(compute)
    ro.observe(container)
    container.addEventListener('scroll', compute)
    window.addEventListener('resize', compute)
    return () => {
      ro.disconnect()
      container.removeEventListener('scroll', compute)
      window.removeEventListener('resize', compute)
    }
  }, [root])

  return (
    <div className="hf">
      <style>{hoverflyStyles}</style>
      {root.completed &&
        <div className="banner-done">
          ✓ Proof complete — a closing tactic sequence has been found.
        </div>}
      <div className="toolbar">
        <button className="write-btn" disabled={!onWrite}
          title={onWrite
            ? "Replace `hoverfly` with the selected proof"
            : "No source range available to write into"}
          onClick={onWrite}>
          {scriptHasSorry
            ? "Write proof (with sorry)"
            : "Write proof to file"}
        </button>
      </div>
      <div className="treeA" ref={treeRef}>
        <svg className="pair-arrows" width={size.w} height={size.h}>
          {links.map((l: DrawnLink, i: number) =>
            <g key={i} stroke={l.color} fill="none">
              <path d={l.d} strokeWidth={1.5} />
              <path d={l.head} fill={l.color} stroke="none" />
            </g>)}
        </svg>
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
          // todo error
          console.error("No new node found with id " + n.id)
        }
      } else {
        // todo error
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
