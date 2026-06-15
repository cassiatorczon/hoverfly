import { test } from 'node:test'
import assert from 'node:assert/strict'

import { recomputeCompleted, selectRoot, Node } from '../src/Tree'
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
  // Backend.getSubgoals
  if (id === 1) {
    return [
      { isGoal: true, id: 2, display: '1 = 1' },
      { isGoal: true, id: 3, display: '2 = 2' }
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
    assert.deepEqual(tactic1.children.map((c) => c.id), [2, 3])
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

test('clicking the already-selected node is a no-op', async () => {
  const s = await makeSession(foobarResponder)
  await s.click(1)
  const before = s.get()
  const callsBefore = s.calls.length
  await s.click(1) // tactic 1 is already selected
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
