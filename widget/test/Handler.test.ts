import { test } from 'node:test'
import assert from 'node:assert/strict'

import {
  recomputeCompleted, recomputeInactive, isInactive, selectRoot, navChildren, Node
} from '../src/Tree'
import {
  handleClick,
  getApplicableTactics,
  APINodeToNode,
  APIData,
  APINode
} from '../src/Handler'
import {
  mockRpc, Responder, dummyPos, findById, countSelected, selectedIds
} from './testUtils'

// handleClick is chatty on console.debug/info; keep test output readable.
console.debug = () => { }
console.info = () => { }

// Models the `foobar : 1 = 1 /\ 2 = 2` proof:
//   goal 0  --(apply And.intro: tactic 1)-->  goals 2 (1=1) and 3 (2=2)
//   goal 2  --(rfl: tactic 4)-->  closes (no subgoals)
//   goal 3  --(rfl: tactic 5)-->  closes (no subgoals)
const foobarResponder: Responder = (method, id) => {
  if (method === 'Backend.getApplicableTactics') {
    if (id === 0) return [{ isGoal: false, id: 1, display: 'apply And.intro' }]
    if (id === 2) return [{ isGoal: false, id: 4, display: 'rfl' }]
    if (id === 3) return [{ isGoal: false, id: 5, display: 'rfl' }]
    return []
  }
  // Backend.getSubgoals returns clusters (one inner list per cluster). The two
  // conjuncts share no metavariable, so they form two singleton clusters.
  if (id === 1) {
    return [
      [{ isGoal: true, id: 2, display: '1 = 1' }],
      [{ isGoal: true, id: 3, display: '2 = 2' }]
    ]
  }
  if (id === 4) return [] // rfl closes goal 2
  if (id === 5) return [] // rfl closes goal 3
  return []
}

// A small driver that mirrors how the component loads and dispatches clicks.
async function makeSession(responder: Responder) {
  const { rs, calls } = mockRpc(responder)
  const rootApi: APINode = { isGoal: true, id: 0, display: '1 = 1 /\\ 2 = 2' }
  const loaded = await getApplicableTactics(
    selectRoot(APINodeToNode(rootApi)), { p: 'init' }, rs as any, dummyPos)

  let tree: Node = loaded.node
  let stateRef: APIData = loaded.stateRef

  async function click(id: number) {
    const target = findById(tree, id)
    assert.ok(target, 'click target ' + id + ' must exist in the tree')
    const res = await handleClick(tree, stateRef, target!, rs as any, dummyPos)
    tree = res.node
    stateRef = res.stateRef
  }

  return { click, get: () => tree, calls }
}

test('descend: clicking a tactic expands its subgoals and marks it explored',
  async () => {
    const s = await makeSession(foobarResponder)
    await s.click(1) // apply And.intro

    const tactic1 = findById(s.get(), 1)!
    assert.equal(tactic1.status, 'selected')
    assert.equal(tactic1.explored, true,
      'expanded tactic must be marked explored so completion is detectable')
    // subgoals are wrapped in (singleton) cluster nodes; navChildren sees through
    assert.deepEqual(navChildren(tactic1).map((c) => c.id), [2, 3])
    assert.equal(s.get().status, 'semiselected') // root demoted
    assert.equal(countSelected(s.get()), 1)
  })

test('sibling switch: moving between subgoals keeps exactly one selection ' +
  '(regression: foobar conjuncts)', async () => {
    const s = await makeSession(foobarResponder)
    await s.click(1) // apply And.intro
    await s.click(2) // select first conjunct 1=1
    await s.click(3) // switch to second conjunct 2=2  (branch 3)

    const tree = s.get()
    // The previously selected sibling must be deselected, not left selected.
    assert.deepEqual(selectedIds(tree), [3],
      'after switching siblings, only the newly clicked goal is selected')
    assert.equal(countSelected(tree), 1)

    const goal2 = findById(tree, 2)!
    assert.equal(goal2.status, 'unselected')
    assert.ok(goal2.cache, 'old branch should be collapsed into a cache')

    const goal3 = findById(tree, 3)!
    assert.equal(goal3.status, 'selected')
    assert.equal(goal3.explored, true)
    assert.deepEqual(goal3.children.map((c) => c.id), [5],
      'newly selected sibling has its applicable tactics fetched')
  })

test('sibling switch is reversible: switching back restores the cached branch',
  async () => {
    const s = await makeSession(foobarResponder)
    await s.click(1)
    await s.click(2) // explore 1=1 (fetches tactic 4)
    await s.click(3) // switch away -> 1=1 collapses
    await s.click(2) // switch back -> should restore from cache

    const tree = s.get()
    assert.deepEqual(selectedIds(tree), [2])
    const goal2 = findById(tree, 2)!
    assert.deepEqual(goal2.children.map((c) => c.id), [4],
      'cached subtree (tactic 4) is restored rather than refetched')

    // Switching back must reuse the cache, not call the backend again for it.
    const refetchedGoal2 =
      s.calls.filter((c) =>
        c.method === 'Backend.getApplicableTactics' && c.id === 2)
    assert.equal(refetchedGoal2.length, 1,
      'goal 2 tactics fetched exactly once (first visit), not on restore')
  })

test('clicking the already-selected node backtracks to its parent', async () => {
  const s = await makeSession(foobarResponder)
  await s.click(1)
  const callsBefore = s.calls.length
  await s.click(1) // tactic 1 is already selected: "double click" unselects it

  const tree = s.get()
  assert.equal(tree.status, 'selected', 'selection moves up to the root')
  assert.equal(countSelected(tree), 1)
  const tactic1 = findById(tree, 1)!
  assert.equal(tactic1.status, 'unselected')
  assert.deepEqual(tactic1.children, [], 'abandoned branch is collapsed')
  assert.ok(tactic1.cache, 'collapsed branch is cached for later restore')
  assert.equal(s.calls.length, callsBefore,
    'backtracking is pure tree surgery, no backend calls')
})

test('clicking the already-selected root is a no-op', async () => {
  const s = await makeSession(foobarResponder)
  const before = s.get()
  const callsBefore = s.calls.length
  await s.click(0) // the root is selected from the start
  assert.equal(s.get(), before, 'tree reference unchanged')
  assert.equal(s.calls.length, callsBefore, 'no backend calls made')
})

test('proof completion propagates to the root, including across collapsed ' +
  'branches', async () => {
    const s = await makeSession(foobarResponder)
    await s.click(1) // apply And.intro
    await s.click(2) // 1=1
    await s.click(4) // rfl closes 1=1

    // One conjunct closed: the goal/tactic are completed but the proof is not.
    let derived = recomputeCompleted(s.get())
    assert.equal(findById(derived, 2)!.completed, true)
    assert.equal(findById(derived, 4)!.completed, true)
    assert.equal(derived.completed, false, 'proof not complete with 2=2 open')

    await s.click(3) // switch to 2=2 (collapses the completed 1=1 branch)
    await s.click(5) // rfl closes 2=2

    derived = recomputeCompleted(s.get())
    assert.equal(derived.completed, true,
      'root (proof) is complete once both conjuncts are closed')
    // completion survived collapsing the first conjunct into its cache
    assert.equal(findById(derived, 2)!.completed, true)
  })

/* Metavariable clusters (design/metavariable-clusters.md worked example) */

// goal 0 (w ≤ z) --apply le_trans--> cluster { goal 2 (w ≤ ?b), goal 3 (?b ≤ z) }
// sharing ?b. Driving goal 2 with `exact h5` assigns ?b := 5 and carries the
// still-open sibling goal 3 as a copy (id 6, `5 ≤ z`, originalId 3). Driving
// goal 3 instead with `exact h7` carries goal 2 as a copy (id 9, originalId 2).
const transResponder: Responder = (method, id) => {
  if (method === 'Backend.getApplicableTactics') {
    if (id === 0) return [{ isGoal: false, id: 1, display: 'apply le_trans' }]
    if (id === 2) return [{ isGoal: false, id: 5, display: 'exact h5' }]
    if (id === 3) return [{ isGoal: false, id: 8, display: 'exact h7' }]
    if (id === 6) return [{ isGoal: false, id: 7, display: 'le_refl' }]
    if (id === 9) return [{ isGoal: false, id: 10, display: 'le_refl' }]
    return []
  }
  // Backend.getSubgoals
  if (id === 1) {
    return [[
      { isGoal: true, id: 2, display: 'w ≤ ?b' },
      { isGoal: true, id: 3, display: '?b ≤ z' }
    ]]
  }
  if (id === 5) return [[{ isGoal: true, id: 6, display: '5 ≤ z', originalId: 3 }]]
  if (id === 8) return [[{ isGoal: true, id: 9, display: 'w ≤ 7', originalId: 2 }]]
  if (id === 7) return [] // closes the copy 5 ≤ z
  if (id === 10) return [] // closes the copy w ≤ 7
  return []
}

// Mirror the component's display derivation.
const display = (n: Node) => recomputeCompleted(recomputeInactive(n))

test('cluster: driving one goal inactivates its sibling and redirects', async () => {
  const s = await makeSession(transResponder)
  await s.click(1) // apply le_trans -> cluster { 2, 3 }
  await s.click(2) // descend into w ≤ ?b
  await s.click(5) // exact h5: assigns ?b := 5, carries copy 6 of sibling 3

  const d = display(s.get())
  const sibling = findById(d, 3)!
  assert.equal(isInactive(sibling), true, 'the still-open sibling is inactivated')
  assert.equal(sibling.redirectTo, 6, 'and points at the carried copy')
  assert.equal(isInactive(findById(d, 6)!), false, 'the copy itself stays active')
})

test('cluster: completion is gated by the carried copy, not the original',
  async () => {
    const s = await makeSession(transResponder)
    await s.click(1)
    await s.click(2)
    await s.click(5) // copy 6 (5 ≤ z) appears, still open

    assert.equal(display(s.get()).completed, false,
      'not complete while the carried copy is open')

    await s.click(6) // descend into the copy
    await s.click(7) // close it

    assert.equal(display(s.get()).completed, true,
      'closing the copy (a child of the driving tactic) completes the proof')
  })

test('cluster: backtracking off the driving tactic reactivates the sibling',
  async () => {
    const s = await makeSession(transResponder)
    await s.click(1)
    await s.click(2)
    await s.click(5) // sibling 3 inactivated
    assert.equal(isInactive(findById(display(s.get()), 3)!), true)

    await s.click(5) // back out of the driving tactic to w ≤ ?b (caches +copy)

    assert.equal(isInactive(findById(display(s.get()), 3)!), false,
      'with the copy stashed in cache, the sibling is active again')
  })

test('cluster: roles flip when the other sibling drives the assignment',
  async () => {
    const s = await makeSession(transResponder)
    await s.click(1)
    await s.click(2)
    await s.click(5) // drive from goal 2 -> goal 3 inactive
    await s.click(5) // back out of the driving tactic to goal 2
    await s.click(3) // switch to the sibling ?b ≤ z
    await s.click(8) // exact h7: assigns ?b := 7, carries copy 9 of goal 2

    const d = display(s.get())
    assert.equal(isInactive(findById(d, 2)!), true, 'now the first goal is inactive')
    assert.equal(findById(d, 2)!.redirectTo, 9)
    assert.equal(isInactive(findById(d, 3)!), false, 'and the driver is active')
  })

test('cluster: after a role-flip, closing the copy still completes the proof',
  async () => {
    // Regression: driving goal 2 first explores/caches its branch; after the
    // flip, goal 2 is inactive and cached. Closing the flipped copy must
    // complete the proof, with the inactive cached original not blocking it.
    const s = await makeSession(transResponder)
    await s.click(1)
    await s.click(2)
    await s.click(5) // drive from goal 2 (explores goal 2's subtree)
    await s.click(5) // back out of the driving tactic to goal 2
    await s.click(3) // switch to the sibling
    await s.click(8) // drive from goal 3 -> goal 2 inactive + cached

    assert.equal(display(s.get()).completed, false, 'not complete while copy open')

    await s.click(9)
    await s.click(10) // close the copy of goal 2

    const d = display(s.get())
    assert.equal(d.completed, true, 'proof completes via the flipped driver')
    // The inactive cached original carries no truth of its own — it is excluded
    // from its cluster, not counted as discharged — yet it must not block the
    // proof, which completes through the active flipped driver (asserted above).
    assert.equal(findById(d, 2)!.completed, false,
      'the inactive original is excluded, not self-completed')
  })

test('cluster: flip back to the first driver and finish through its cache',
  async () => {
    const s = await makeSession(transResponder)
    await s.click(1)
    await s.click(2)
    await s.click(5) // drive goal 2
    await s.click(5) // click the selected tactic again to back out to goal 2
    await s.click(3) // switch to sibling goal 3
    await s.click(8) // drive goal 3 -> goal 2 branch cached
    await s.click(8) // back out of goal 3's tactic to goal 3
    await s.click(2) // back to goal 2: reactivates and restores its cache

    assert.equal(isInactive(findById(display(s.get()), 2)!), false,
      'goal 2 reactivated after backtracking off goal 3')

    await s.click(5) // re-drive goal 2 -> goal 3 inactive again
    await s.click(6)
    await s.click(7)
    assert.equal(display(s.get()).completed, true,
      'proof completes after flipping back to the first driver')
  })
