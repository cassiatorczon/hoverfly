import { Node, navChildren, isInactive } from './Tree'

/* Serialize the *selected* sub-tree into a Lean tactic script.
 *
 * We follow each goal's active tactic. An *abandoned* tactic that was replaced by selecting a
 * different tactic on the same goal is skipped. A goal with no work at all becomes `sorry`. */

const INDENT = '  '

// Collapse a pretty-printed tactic (which may wrap across several lines) into a single line so it
// sits cleanly inside a `·` / `on_goal` block.
function normalizeTactic(display: string): string {
  return display.replace(/\s+/g, ' ').trim()
}

// The tactic on the active (selected/semiselected) path out of a goal, if any.
function activeTactic(goal: Node): Node | undefined {
  return navChildren(goal).find(
    (c) => c.kind === 'tactic' &&
      (c.status === 'selected' || c.status === 'semiselected'))
}

// Maps copied goal ids to the nodes that holds their proofs.
function buildCopyMap(root: Node): Map<number, Node> {
  const m = new Map<number, Node>()
  const walk = (n: Node): void => {
    if (n.originalId !== undefined) m.set(n.originalId, n)
    n.children.forEach(walk)
  }
  walk(root)
  return m
}

function subtreeContains(n: Node, id: number): boolean {
  return n.id === id || n.children.some((c) => subtreeContains(c, id))
}

// Wrap a child block under a `·` focus bullet: first line after the bullet, the rest indented to
// line up under it.
// NOTE: Do we think people will want to be able configure this behavior?
function focusBlock(block: string): string {
  const [first, ...rest] = block.split('\n')
  return ['· ' + first, ...rest.map((l) => INDENT + l)].join('\n')
}

// Wrap a child block under `on_goal n =>`, used when a goal must be proved out of Lean's
// front-to-back order (see `serializeSubgoals`).
function onGoalBlock(n: number, block: string): string {
  return ['on_goal ' + n + ' =>', ...block.split('\n').map((l) => INDENT + l)]
    .join('\n')
}

// A tactic's real subgoals, in Lean's goal order. Carried copies (`originalId` set) are excluded
// here — they belong to an ancestor cluster sibling and are spliced in there via the copy map, not
// proved as this tactic's own subgoals.
function realSubgoals(tactic: Node): Node[] {
  const subs = navChildren(tactic).filter(
    (c) => c.kind === 'goal' && c.originalId === undefined)
  return [...subs].sort((a, b) => (a.leanOrder ?? 0) - (b.leanOrder ?? 0))
}

function serializeGoal(goal: Node, copyMap: Map<number, Node>): string {
  const active = activeTactic(goal)

  // If the goal is active, serialize its tactic.
  if (active) return serializeTactic(active, copyMap)

  // If the goal is inactive but cached (i.e., a sibling of the current active goal that has been
  // worked on), look it up in the cache and serialize it.
  if (goal.cache) return serializeGoal(goal.cache, copyMap)

  // Otherwise, the goal hasn't been worked on and should be `sorry`d.
  return 'sorry'
}

// The proof of a subgoal, resolving a copied (inactive) goal to its copy.
function serializeSubgoal(sub: Node, copyMap: Map<number, Node>): string {
  if (isInactive(sub)) {
    const copy = copyMap.get(sub.id)
    return copy ? serializeGoal(copy, copyMap) : 'sorry'
  }
  return serializeGoal(sub, copyMap)
}

// Order subgoals so every copied goal is emitted *after* the sibling whose
// tactic assigns the shared metavariable.
function emissionOrder(subs: Node[], copyMap: Map<number, Node>): Node[] {
  const resolverOf = new Map<number, number>()
  for (const sub of subs) {
    if (!isInactive(sub)) continue
    const copy = copyMap.get(sub.id)
    if (!copy) continue
    const resolver = subs.find(
      (s) => s.id !== sub.id && subtreeContains(s, copy.id))
    if (resolver) resolverOf.set(sub.id, resolver.id)
  }

  const emitted = new Set<number>()
  const result: Node[] = []
  while (result.length < subs.length) {
    const next = subs.find((s) => !emitted.has(s.id) &&
      (!resolverOf.has(s.id) || emitted.has(resolverOf.get(s.id) as number)))
    if (!next) {
      // Unreachable: a resolver is always a non-copied sibling with no dependency of its own, so
      // some goal is always emittable; the `resolverOf` edges can't form a cycle. Reaching here
      // means a tree invariant broke.
      throw new Error('serializeTree: cyclic subgoal dependency in ' +
        `[${subs.map((s) => s.id).join(', ')}]`)
    }
    result.push(next)
    emitted.add(next.id)
  }
  return result
}

function serializeSubgoals(subs: Node[], copyMap: Map<number, Node>): string[] {
  if (subs.length === 1) return [serializeSubgoal(subs[0], copyMap)]

  const emission = emissionOrder(subs, copyMap)
  const inLeanOrder = emission.every((s, i) => s.id === subs[i].id)

  if (inLeanOrder) {
    // Front-to-back: `·` bullets bind to goals positionally.
    return subs.map((s) => focusBlock(serializeSubgoal(s, copyMap)))
  }

  // Out of order: target each goal by its current index with `on_goal`. Each block fully closes its
  // goal, so remaining goals keep their relative order.
  const remaining = subs.map((s) => s.id)
  return emission.map((s) => {
    const pos = remaining.indexOf(s.id)
    remaining.splice(pos, 1)
    return onGoalBlock(pos + 1, serializeSubgoal(s, copyMap))
  })
}

function serializeTactic(tactic: Node, copyMap: Map<number, Node>): string {
  const line = normalizeTactic(tactic.display)
  const subs = realSubgoals(tactic)
  if (subs.length === 0) return line

  const blocks = serializeSubgoals(subs, copyMap)
  if (subs.length === 1) return line + '\n' + blocks[0]
  return [line, ...blocks].join('\n')
}

// Serialize the selected sub-tree rooted at `root` (a goal) into a tactic script. Incomplete
// branches become `sorry`.
export function serializeTree(root: Node, baseIndent = ''): string {
  const block = serializeGoal(root, buildCopyMap(root))
  if (baseIndent === '') return block
  return block.split('\n')
    .map((l, i) => i === 0 ? l : baseIndent + l)
    .join('\n')
}
