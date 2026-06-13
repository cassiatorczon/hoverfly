import { test } from 'node:test'
import assert from 'node:assert/strict'

import {
  recomputeCompleted,
  cacheChild,
  nearestCommonAncestorWithSelected,
  updateNodes,
  changeStatusAtId,
  changeStatusAtSelected,
  selectRoot
} from '../src/Tree'
import { goal, tactic, findById } from './testUtils'

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
