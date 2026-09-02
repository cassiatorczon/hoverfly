import { test } from 'node:test'
import assert from 'node:assert/strict'

import {
  recomputeCompleted,
  recomputeVisible,
  recomputeInactive,
  isInactive,
  badgeFor,
  markerFor,
  cacheChild,
  nearestCommonAncestorWithSelected,
  navChildren,
  updateNodes,
  changeStatusAtId,
  changeStatusAtSelected,
  selectRoot,
  groupLabel,
  groupTactics,
  compactGoal,
  nextOpenGoal,
  Node
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

test('recomputeInactive: an inactive original is excluded from its cluster, not blocking it', () => {
  // The original's obligation has moved to the copy under the driver, so the
  // original itself carries no truth here (it is NOT marked completed) but must
  // not block its cluster: the cluster is discharged once the active driver is.
  //   goal0 -le_trans-> cluster{ driver (w ≤ ?b), original (?b ≤ z)[inactive] }
  //   driver -exact h5-> cluster{ copyOf3 (closed) }
  const copy = goal(6, '5 ≤ z', {
    originalId: 3,
    children: [tactic(7, 'exact hz', { explored: true, children: [] })]
  })
  const driver = goal(2, 'w ≤ ?b', {
    children: [tactic(5, 'exact h5', {
      explored: true, children: [cluster(-7, [copy])]
    })]
  })
  const tree = goal(0, 'w ≤ z', {
    children: [tactic(1, 'apply le_trans', {
      explored: true, children: [cluster(-3, [driver, goal3()])]
    })]
  })
  const r = recomputeCompleted(recomputeInactive(tree))
  // the inactive original carries no truth of its own...
  assert.equal(findById(r, 3)!.completed, false)
  // ...yet the whole proof completes through the active driver + its copy
  assert.equal(r.completed, true)
})

test('recomputeCompleted: an unresolved cluster with every member closed is NOT completed', () => {
  // The double-solve trap: both members of a real cluster get closed independently
  // in their own states, but NEITHER drove the shared metavariable — so no sibling
  // was carried down and nothing is inactive. The shared mvar is still free, hence
  // the proof is broken; the cluster must not read as completed just because every
  // member individually did.
  //   goal0 -split-> cluster{ m2 (closed, no assign), m3 (closed, no assign) }
  const closed = (id: number, disp: string) => goal(id, disp, {
    children: [tactic(id * 10, 'close', { explored: true, children: [] })]
  })
  const tree = goal(0, 'g', {
    children: [tactic(1, 'split', {
      explored: true,
      children: [cluster(-3, [closed(2, 'a ≤ ?m'), closed(3, '?m ≤ c')])]
    })]
  })
  const r = recomputeCompleted(recomputeInactive(tree))
  // both members individually complete...
  assert.equal(findById(r, 2)!.completed, true)
  assert.equal(findById(r, 3)!.completed, true)
  // ...but the cluster (and the proof) is not, since the mvar was never assigned
  assert.equal(findById(r, -3)!.completed, false)
  assert.equal(r.completed, false, 'unresolved cluster does not complete the proof')
})

test('recomputeCompleted: a singleton cluster completes with its lone goal', () => {
  // A single-goal cluster shares no metavariable with siblings, so the resolution
  // requirement does not apply: it completes as soon as its goal does.
  const tree = goal(0, 'g', {
    children: [tactic(1, 't', {
      explored: true,
      children: [cluster(-2, [goal(2, 'sub', {
        children: [tactic(3, 'close', { explored: true, children: [] })]
      })])]
    })]
  })
  const r = recomputeCompleted(recomputeInactive(tree))
  assert.equal(findById(r, -2)!.completed, true)
  assert.equal(r.completed, true)
})

test('recomputeInactive: a copy stashed in a cache does not inactivate (backtrack)',
  () => {
    // Backtracking collapses the copy-bearing branch into a `cache`; the copy is
    // then off the live tree, so its original reactivates — no stored state.
    const r = recomputeInactive(transTree(true))
    assert.equal(isInactive(findById(r, 3)!), false)
  })

test('recomputeInactive: inactivation is derived INSIDE a cache (self-contained)',
  () => {
    // A completed cluster proof (copy discharges an inactivated original) that
    // gets collapsed into a `cache` must still read as completed: recompute
    // descends into caches for `completed`, so it must for `inactive` too, else
    // the cached original looks unproven and the branch wrongly reads incomplete.
    //   S -> split -> cluster { driver, X }
    //   driver -> assign -> cluster { copyOfX (closed) }   (X inactivated by copy)
    const cachedSubtree = () => {
      const copyOfX = goal(6, 'copy of X', {
        originalId: 3,
        children: [tactic(7, 'close', { explored: true, children: [] })]
      })
      const driver = goal(2, 'driver', {
        children: [tactic(5, 'assign', {
          explored: true, children: [cluster(-7, [copyOfX])]
        })]
      })
      const originalX = goal(3, 'X') // open, no proof of its own
      return goal(100, 'S', {
        children: [tactic(101, 'split', {
          explored: true, children: [cluster(-3, [driver, originalX])]
        })]
      })
    }

    // live: X inactivated by its copy, cluster/proof completes
    assert.equal(
      recomputeCompleted(recomputeInactive(cachedSubtree())).completed, true)

    // collapsed into a cache: must still report completed through the cache
    const collapsed = goal(100, 'S', {
      children: [], explored: true, cache: cachedSubtree()
    })
    assert.equal(
      recomputeCompleted(recomputeInactive(collapsed)).completed, true,
      'cached completed cluster proof stays completed')
  })

/* badgeFor */

test('badgeFor: a live completed goal is committed (done), or orphaned in a cluster', () => {
  const done = goal(1, 'g', { completed: true, children: [tactic(2)] })
  assert.equal(badgeFor(done, false), 'done')
  // Same node, but it's a member of an unresolved cluster: it closed without
  // assigning the shared mvar, so its proof will be discarded when a sibling
  // drives — it earns the warning.
  assert.equal(badgeFor(done, true), 'orphaned')
})

test('badgeFor: a goal\'s completed proof stashed in cache stays done / orphaned', () => {
  // After backtracking to the parent, the solved subtree lives in `cache` with
  // empty children — the badge must not change just because of where the proof
  // is stored.
  const cached = goal(1, 'g', {
    explored: true, children: [],
    cache: goal(1, 'g', { completed: true, children: [tactic(2)] })
  })
  assert.equal(badgeFor(cached, false), 'done')
  assert.equal(badgeFor(cached, true), 'orphaned')
})

test('badgeFor: a superseded (inactive) goal advertises nothing, even when solved', () => {
  // The double-solve fix: an inactivated original whose obligation moved to a
  // copy must show no badge, whether its proof is live or stashed in cache.
  const liveInactive = goal(30, '?w = ?w', {
    redirectTo: 60, completed: true, explored: true, children: [tactic(2)]
  })
  const cachedInactive = goal(30, '?w = ?w', {
    redirectTo: 60, explored: true, children: [],
    cache: goal(30, '?w = ?w', { completed: true, children: [tactic(2)] })
  })
  assert.equal(isInactive(liveInactive), true)
  assert.equal(badgeFor(liveInactive, false), 'none')
  assert.equal(badgeFor(cachedInactive, false), 'none')
  // the orphaned flag never overrides inactivity
  assert.equal(badgeFor(cachedInactive, true), 'none')
})

test('badgeFor: a cached tactic reads as cached-done (complete) or cached (partial)', () => {
  const completeTac = tactic(1, 't', {
    explored: true, children: [],
    cache: tactic(1, 't', { completed: true, children: [goal(2)] })
  })
  const partialTac = tactic(1, 't', {
    explored: true, children: [],
    cache: tactic(1, 't', { completed: false, children: [goal(2)] })
  })
  assert.equal(badgeFor(completeTac, false), 'cached-done')
  assert.equal(badgeFor(partialTac, false), 'cached')
})

test('badgeFor: an explored-but-unproven node shows the explored dot, else nothing', () => {
  assert.equal(badgeFor(goal(1, 'g', { explored: true }), false), 'explored')
  assert.equal(badgeFor(goal(1, 'g', { explored: false }), false), 'none')
})

/* markerFor */

test('markerFor: goals get the goal glyph', () => {
  assert.equal(markerFor(goal(1, 'g')), 'goal')
  assert.equal(markerFor(goal(1, 'g', { status: 'selected' })), 'goal')
})

test('markerFor: a succeeding tactic off the active path offers Run', () => {
  assert.equal(markerFor(tactic(1, 't')), 'run')
})

test('markerFor: a tactic on the active path offers Undo', () => {
  assert.equal(markerFor(tactic(1, 't', { status: 'selected' })), 'undo')
  assert.equal(
    markerFor(tactic(1, 't', { status: 'semiselected' })), 'undo')
})

test('markerFor: an off-path tactic with a cache offers Redo', () => {
  assert.equal(
    markerFor(tactic(1, 't', { cache: tactic(1, 't') })), 'redo')
})

test('markerFor: failing and no-op tactics advertise no action', () => {
  assert.equal(markerFor(tactic(1, 't', { tacticError: 'nope' })), 'dot')
  assert.equal(markerFor(tactic(1, 't', { noop: true })), 'dot')
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

/* prototactic grouping */

test('groupLabel names the group by the shared token prefix', () => {
  assert.equal(
    groupLabel([tactic(1, 'induction a'), tactic(2, 'induction hab')]),
    'induction')
  assert.equal(
    groupLabel([tactic(1, 'rewrite [h] at a'), tactic(2, 'rewrite [h] at b')]),
    'rewrite [h] at')
})

test('groupLabel falls back to a count when nothing is shared', () => {
  assert.equal(groupLabel([tactic(1, 'simp'), tactic(2, 'omega')]), '2 variants')
})

test('groupLabel compares whole tokens, not characters', () => {
  // 'ind' is a character prefix of 'induction' but not a shared token
  assert.equal(groupLabel([tactic(1, 'ind a'), tactic(2, 'induction a')]),
    '2 variants')
})

test('groupTactics coalesces runs sharing a groupId', () => {
  const kids = [
    tactic(1, 't1'),
    tactic(2, 't2', { groupId: 0 }),
    tactic(3, 't3', { groupId: 0 }),
    tactic(4, 't4', { groupId: 1 }),
    tactic(5, 't5')
  ]
  const grouped = groupTactics(kids)
  assert.equal(grouped.length, 4)
  assert.equal((grouped[0] as Node).id, 1, 'untagged nodes pass through bare')
  assert.deepEqual((grouped[1] as Node[]).map((n) => n.id), [2, 3])
  assert.equal((grouped[2] as Node).id, 4, 'a run of one comes back bare')
  assert.equal((grouped[3] as Node).id, 5)
})

test('groupTactics preserves order and never merges separated runs', () => {
  const kids = [
    tactic(1, 't1', { groupId: 0 }),
    tactic(2, 't2', { groupId: 0 }),
    tactic(3, 't3', { groupId: 1 }),
    tactic(4, 't4', { groupId: 1 }),
    tactic(5, 't5', { groupId: 0 }),
    tactic(6, 't6', { groupId: 0 })
  ]
  const grouped = groupTactics(kids)
  assert.deepEqual(
    grouped.map((e) => (Array.isArray(e) ? e.map((n) => n.id) : e.id)),
    [[1, 2], [3, 4], [5, 6]])
})

test('groupTactics on an empty list is empty', () => {
  assert.deepEqual(groupTactics([]), [])
})

/* compactGoal */

test('compactGoal replaces hypotheses with an ellipsis, keeping case and target', () => {
  assert.equal(compactGoal('case inl\nx : Nat\nh : x > 0\n⊢ x ≠ 0'),
    'case inl … ⊢ x ≠ 0')
  assert.equal(compactGoal('⊢ True'), '⊢ True')
  assert.equal(compactGoal('h : P\n⊢ P ∧\n  Q'), '… ⊢ P ∧\n  Q')
  assert.equal(compactGoal('not a goal'), 'not a goal')
})

/* nextOpenGoal */

test('nextOpenGoal picks the next open goal in tree order, wrapping around', () => {
  // t0 -> [g1 (done), g2 (open), g3 (open)]; g1 holds the selection.
  const root = tactic(0, 't', {
    status: 'semiselected',
    children: [
      goal(1, 'g1', {
        status: 'semiselected',
        children: [tactic(4, 'rfl', { status: 'selected', explored: true })]
      }),
      goal(2, 'g2'),
      goal(3, 'g3')
    ]
  })
  const r = recomputeCompleted(root)
  assert.equal(nextOpenGoal(r, 4)?.id, 2)
  assert.equal(nextOpenGoal(r, 2)?.id, 3)
  assert.equal(nextOpenGoal(r, 3)?.id, 2)
})

test('nextOpenGoal is undefined when nothing is open', () => {
  const root = goal(0, 'g', {
    status: 'selected',
    children: [tactic(1, 'rfl', { status: 'selected', explored: true })]
  })
  assert.equal(nextOpenGoal(recomputeCompleted(root), 1), undefined)
})
