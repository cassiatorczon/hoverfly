import { test } from 'node:test'
import assert from 'node:assert/strict'

import {
  recomputeCompleted,
  recomputeVisible,
  recomputeInactive,
  isInactive,
  cacheChild,
  nearestCommonAncestorWithSelected,
  navChildren,
  updateNodes,
  changeStatusAtId,
  changeStatusAtSelected,
  selectRoot
} from '../src/Tree'
import { goal, tactic, cluster, findById } from './testUtils'

/* recomputeCompleted */

test('recomputeCompleted: unexplored tactic leaf is not completed', () => {
  const t = tactic(1, 't', { explored: false })
  assert.equal(recomputeCompleted(t).completed, false)
})

test('recomputeCompleted: explored tactic with no subgoals closes the goal',
  () => {
    // a tactic that was explored and produced zero subgoals has vacuously
    // "all subgoals completed", so it is completed
    const t = tactic(1, 'rfl', { explored: true })
    assert.equal(recomputeCompleted(t).completed, true)
  })

test('recomputeCompleted: goal is completed iff some tactic child completes',
  () => {
    const incomplete = goal(0, 'g', {
      children: [tactic(1, 'bad', { explored: true, children: [goal(2)] })]
    })
    assert.equal(recomputeCompleted(incomplete).completed, false)

    const complete = goal(0, 'g', {
      children: [tactic(1, 'rfl', { explored: true })]
    })
    assert.equal(recomputeCompleted(complete).completed, true)
  })

test('recomputeCompleted: tactic needs ALL subgoals completed', () => {
  const oneOpen = tactic(1, 'apply And.intro', {
    explored: true,
    children: [
      goal(2, 'done', { children: [tactic(3, 'rfl', { explored: true })] }),
      goal(4, 'open') // no completing child
    ]
  })
  assert.equal(recomputeCompleted(oneOpen).completed, false)

  const bothClosed = tactic(1, 'apply And.intro', {
    explored: true,
    children: [
      goal(2, 'a', { children: [tactic(3, 'rfl', { explored: true })] }),
      goal(4, 'b', { children: [tactic(5, 'rfl', { explored: true })] })
    ]
  })
  assert.equal(recomputeCompleted(bothClosed).completed, true)
})

test('recomputeCompleted: collapsed node inherits completion from its cache',
  () => {
    // a goal that was explored to completion and then collapsed (children
    // moved into `cache`) must still report completed
    const completedSubtree = goal(2, 'g', {
      children: [tactic(3, 'rfl', { explored: true })]
    })
    const collapsed = goal(2, 'g', {
      children: [], cache: completedSubtree, explored: true
    })
    assert.equal(recomputeCompleted(collapsed).completed, true)
  })

test('recomputeCompleted: proof completes through a collapsed sibling', () => {
  // root -> And.intro -> [ collapsed+completed goal , freshly completed goal ]
  const collapsedDone = goal(2, '1=1', {
    children: [], explored: true,
    cache: goal(2, '1=1', { children: [tactic(4, 'rfl', { explored: true })] })
  })
  const liveDone = goal(3, '2=2', {
    children: [tactic(5, 'rfl', { explored: true })]
  })
  const root = goal(0, 'conj', {
    status: 'semiselected',
    children: [tactic(1, 'apply And.intro', {
      explored: true, status: 'semiselected', children: [collapsedDone, liveDone]
    })]
  })
  assert.equal(recomputeCompleted(root).completed, true)
})

test('recomputeCompleted: a collapsed tactic alternative does not count', () => {
  // goal -> [ collapsed+completed tactic (an abandoned alternative), live tactic ]
  // Moving away from a completing tactic collapses it into its cache; it should
  // no longer keep the goal (and thus the root) completed.
  const collapsedAlt = tactic(1, 'rfl', {
    explored: true, children: [],
    cache: tactic(1, 'rfl', { explored: true, children: [] })
  })
  const liveAlt = tactic(2, 'simp', { explored: false })
  const root = goal(0, 'g', {
    status: 'selected', children: [collapsedAlt, liveAlt]
  })
  assert.equal(recomputeCompleted(root).completed, false)
})

/* recomputeInactive */

// The worked example:
//   goal0 -le_trans-> cluster{ goal2 (w ≤ ?b), goal3 (?b ≤ z) }
// Driving goal2 with a tactic that assigns ?b carries goal3 as a copy (id 6,
// originalId 3) under that tactic.
function transTree(copyUnderCache = false): ReturnType<typeof goal> {
  const copy = goal(6, '5 ≤ z', { originalId: 3 })
  const drivingTactic = tactic(5, 'exact h5', {
    explored: true, children: [cluster(-7, [copy])]
  })
  const goal2 = copyUnderCache
    ? goal(2, 'w ≤ ?b', {
      explored: true, children: [],
      cache: goal(2, 'w ≤ ?b', { children: [drivingTactic] })
    })
    : goal(2, 'w ≤ ?b', { children: [drivingTactic] })
  return goal(0, 'w ≤ z', {
    children: [tactic(1, 'apply le_trans', {
      explored: true, children: [cluster(-3, [goal2, goal3()])]
    })]
  })
}
function goal3() { return goal(3, '?b ≤ z') }

test('recomputeInactive: a live copy inactivates its original and redirects',
  () => {
    const r = recomputeInactive(transTree())
    const original = findById(r, 3)!
    assert.equal(isInactive(original), true)
    assert.equal(original.redirectTo, 6, 'original points at the copy')
    // the copy itself stays active, as do unrelated goals
    assert.equal(isInactive(findById(r, 6)!), false)
    assert.equal(isInactive(findById(r, 2)!), false)
  })

test('recomputeInactive: an inactive original counts as completed', () => {
  // its obligation has moved to the copy, so it must not block its parent
  const r = recomputeCompleted(recomputeInactive(transTree()))
  assert.equal(findById(r, 3)!.completed, true)
})

test('recomputeInactive: a copy stashed in a cache does not inactivate (backtrack)',
  () => {
    // Backtracking collapses the copy-bearing branch into a `cache`; the copy is
    // then off the live tree, so its original reactivates — no stored state.
    const r = recomputeInactive(transTree(true))
    assert.equal(isInactive(findById(r, 3)!), false)
  })

/* navChildren */

test('navChildren: sees goals nested in clusters as a tactic\'s children', () => {
  const t = tactic(1, 'apply le_trans', {
    children: [cluster(-2, [goal(2), goal(3)]), cluster(-4, [goal(4)])]
  })
  assert.deepEqual(navChildren(t).map((c) => c.id), [2, 3, 4])
  // a goal's children (tactics) are returned as-is
  const g = goal(0, 'g', { children: [tactic(1), tactic(2)] })
  assert.deepEqual(navChildren(g).map((c) => c.id), [1, 2])
})

/* recomputeVisible */

test('recomputeVisible: all tactics stay visible before one is chosen', () => {
  // The goal is selected and no tactic child is on the active path yet, so
  // every applicable tactic should remain visible.
  const root = goal(0, 'root', {
    status: 'selected',
    children: [tactic(1, 'a'), tactic(2, 'b'), tactic(3, 'c')]
  })
  const vis = recomputeVisible(root)
  assert.deepEqual(vis.children.map((c) => c.visible), [true, true, true])
})

test('recomputeVisible: a semiselected tactic also hides its siblings', () => {
  // Even when the chosen tactic is only semiselected (we descended into one of
  // its subgoals), its uncached siblings are still hidden.
  const root = goal(0, 'root', {
    status: 'semiselected',
    children: [
      tactic(1, 'chosen', { status: 'semiselected', children: [goal(4)] }),
      tactic(2, 'untried', { status: 'unselected' })
    ]
  })
  const vis = recomputeVisible(root)
  assert.equal(findById(vis, 1)!.visible, true)
  assert.equal(findById(vis, 2)!.visible, false)
})

test('recomputeVisible: sibling goals are never hidden', () => {
  // A tactic's children are subgoals that must all be proved, not alternatives
  // to choose between, so none of them are hidden even when one is active.
  const root = tactic(0, 'root', {
    status: 'semiselected',
    children: [
      goal(1, 'g1', { status: 'selected' }),
      goal(2, 'g2', { status: 'unselected' })
    ]
  })
  const vis = recomputeVisible(root)
  assert.deepEqual(vis.children.map((c) => c.visible), [true, true])
})

/* cacheChild / cacheIfSelected */

test('cacheChild: collapses selected and semiselected children only', () => {
  const n = goal(0, 'root', {
    children: [
      tactic(1, 'sel', { status: 'selected', children: [goal(2)] }),
      tactic(3, 'semi', { status: 'semiselected', children: [goal(4)] }),
      tactic(5, 'plain', { status: 'unselected', children: [goal(6)] })
    ]
  })
  const cached = cacheChild(n)
  const [sel, semi, plain] = cached.children

  // selected -> unselected, children emptied, subtree stashed in cache
  assert.equal(sel.status, 'unselected')
  assert.equal(sel.children.length, 0)
  assert.ok(sel.cache, 'selected child should have a cache')
  assert.equal(sel.cache!.children.length, 1)

  // semiselected collapsed the same way
  assert.equal(semi.status, 'unselected')
  assert.ok(semi.cache)

  // unselected child untouched
  assert.equal(plain.status, 'unselected')
  assert.equal(plain.children.length, 1)
  assert.equal(plain.cache, undefined)
})

/* nearestCommonAncestorWithSelected */

test('NCA: descending into a child of the selected node returns the selected ' +
  'node itself', () => {
    // root selected, child unselected -> nca is root (the "descend" case)
    const root = goal(0, 'root', {
      status: 'selected', children: [tactic(1, 't')]
    })
    const nca = nearestCommonAncestorWithSelected(root, 1)
    assert.equal(nca.id, 0)
    assert.equal(nca.status, 'selected')
  })

test('NCA: switching between sibling goals returns their semiselected parent',
  () => {
    // root -> tactic(semiselected) -> [goalA selected, goalB unselected]
    // clicking goalB: nca is the tactic, and it is *not* selected -> branch 3
    const root = goal(0, 'root', {
      status: 'semiselected',
      children: [tactic(1, 't', {
        status: 'semiselected',
        children: [goal(2, 'a', { status: 'selected' }), goal(3, 'b')]
      })]
    })
    const nca = nearestCommonAncestorWithSelected(root, 3)
    assert.equal(nca.id, 1)
    assert.equal(nca.status, 'semiselected')
  })

test('NCA: clicking an ancestor of the selection returns that ancestor', () => {
  // root semiselected -> tactic selected; clicking root -> nca.id === root.id
  const root = goal(0, 'root', {
    status: 'semiselected',
    children: [tactic(1, 't', { status: 'selected' })]
  })
  const nca = nearestCommonAncestorWithSelected(root, 0)
  assert.equal(nca.id, 0)
})

/* updateNodes */

test('updateNodes: applies update across the tree and stops descent at ' +
  'breakAfter', async () => {
    const visited: number[] = []
    const root = goal(0, 'root', {
      children: [
        goal(1, 'a', { children: [goal(11, 'a1')] }),
        goal(2, 'b')
      ]
    })
    const update = async (n: typeof root) => { visited.push(n.id); return n }
    const breakAfter = (n: typeof root) => n.id === 1
    await updateNodes(root, update, breakAfter)

    // root, a and its sibling b are visited; a's child is NOT (break at a)
    assert.deepEqual(visited.sort((x, y) => x - y), [0, 1, 2])
  })

/* status helpers */

test('changeStatusAtId only changes the matching node', async () => {
  const root = goal(0, 'root', { children: [tactic(1), tactic(2)] })
  const updated = await changeStatusAtId(root, 1, 'selected')
  assert.equal(findById(updated, 1)!.status, 'selected')
  assert.equal(findById(updated, 2)!.status, 'unselected')
  assert.equal(updated.status, 'unselected')
})

test('changeStatusAtSelected retargets the currently selected node', async () => {
  const root = goal(0, 'root', {
    status: 'selected', children: [tactic(1)]
  })
  const updated = await changeStatusAtSelected(root, 'semiselected')
  assert.equal(updated.status, 'semiselected')
})

test('selectRoot marks the root selected', () => {
  assert.equal(selectRoot(goal(0)).status, 'selected')
})
