import { test } from 'node:test'
import assert from 'node:assert/strict'

import { serializeTree } from '../src/Serialize'
import { goal, tactic, cluster } from './testUtils'

const semi = { status: 'semiselected' as const }
const sel = { status: 'selected' as const }

/* Basic shapes */

test('unexplored goal serializes to sorry', () => {
  assert.equal(serializeTree(goal(0)), 'sorry')
})

test('a goal whose tactics are fetched but none chosen is sorry', () => {
  // getApplicableTactics ran, but the user hasn't selected a tactic yet
  const root = goal(0, 'g', {
    ...sel, children: [tactic(1, 'rfl'), tactic(2, 'simp')]
  })
  assert.equal(serializeTree(root), 'sorry')
})

test('a selected closing tactic serializes to just that tactic', () => {
  const root = goal(0, 'g', {
    ...sel, children: [tactic(1, 'rfl', { ...sel, explored: true })]
  })
  assert.equal(serializeTree(root), 'rfl')
})

test('a linear proof is newline-separated with no bullets', () => {
  // g -intro-> g1 -rfl-> (closed)
  const root = goal(0, 'g', {
    ...semi, children: [tactic(1, 'intro', {
      ...semi, explored: true, children: [cluster(-2, [goal(2, 'g1', {
        ...sel, children: [tactic(3, 'rfl', { ...sel, explored: true })]
      })])]
    })]
  })
  assert.equal(serializeTree(root), 'intro\nrfl')
})

test('unfinished frontier of a linear proof is sorry', () => {
  const root = goal(0, 'g', {
    ...semi, children: [tactic(1, 'intro', {
      ...sel, explored: true, children: [cluster(-2, [goal(2, 'g1', sel)])]
    })]
  })
  assert.equal(serializeTree(root), 'intro\nsorry')
})

/* Whitespace normalization */

test('a tactic that pretty-prints across lines is collapsed to one line', () => {
  const root = goal(0, 'g', {
    ...sel, children: [tactic(1, 'apply\n  (foo\n   bar)', { ...sel, explored: true })]
  })
  assert.equal(serializeTree(root), 'apply (foo bar)')
})

/* Branching with focus bullets */

test('multiple independent subgoals get `·` focus bullets', () => {
  // g -And.intro-> [g1 -rfl->, g2 -rfl->]
  const root = goal(0, 'g', {
    ...semi, children: [tactic(1, 'apply And.intro', {
      ...semi, explored: true, children: [cluster(-10, [
        goal(2, 'g1', {
          ...sel, leanOrder: 0,
          children: [tactic(3, 'rfl', { ...sel, explored: true })]
        }),
        goal(4, 'g2', {
          ...semi, leanOrder: 1,
          children: [tactic(5, 'trivial', { ...semi, explored: true })]
        })
      ])]
    })]
  })
  assert.equal(serializeTree(root),
    'apply And.intro\n· rfl\n· trivial')
})

test('bullet bodies are indented under the bullet', () => {
  // g -T-> [g1 -a-> g1' -b->(closed), g2 -c->(closed)]
  const root = goal(0, 'g', {
    ...semi, children: [tactic(1, 'T', {
      ...semi, explored: true, children: [cluster(-10, [
        goal(2, 'g1', {
          ...semi, leanOrder: 0, children: [tactic(3, 'a', {
            ...semi, explored: true, children: [cluster(-4, [goal(4, "g1'", {
              ...sel, children: [tactic(5, 'b', { ...sel, explored: true })]
            })])]
          })]
        }),
        goal(6, 'g2', {
          ...semi, leanOrder: 1,
          children: [tactic(7, 'c', { ...semi, explored: true })]
        })
      ])]
    })]
  })
  assert.equal(serializeTree(root),
    'T\n· a\n  b\n· c')
})

test('subgoals are emitted in Lean order, not tree/cluster order', () => {
  // Tree order puts g2 before g1, but leanOrder says g1 (0) precedes g2 (1).
  const root = goal(0, 'g', {
    ...semi, children: [tactic(1, 'T', {
      ...semi, explored: true, children: [cluster(-10, [
        goal(4, 'g2', {
          ...semi, leanOrder: 1,
          children: [tactic(5, 'second', { ...semi, explored: true })]
        }),
        goal(2, 'g1', {
          ...sel, leanOrder: 0,
          children: [tactic(3, 'first', { ...sel, explored: true })]
        })
      ])]
    })]
  })
  assert.equal(serializeTree(root),
    'T\n· first\n· second')
})

/* Completed sibling subgoals stashed in a cache */

test('a completed sibling subgoal is filled from its cache, not left as sorry',
  () => {
    // apply s_pick -> [caseY, caseX]. caseY was finished first, so navigating to
    // caseX cached its proof (children:[], cache:<proof>, unselected). caseX is
    // still on the active path. Neither should serialize to `sorry`.
    const caseYCache = goal(2, 'caseY', {
      completed: true, status: 'semiselected', children: [
        tactic(30, 'apply s_pure', {
          ...sel, explored: true, completed: true
        })]
    })
    const caseY = goal(2, 'caseY', {
      status: 'unselected', completed: true, leanOrder: 0,
      children: [], cache: caseYCache
    })
    const caseX = goal(4, 'caseX', {
      ...semi, completed: true, leanOrder: 1, children: [
        tactic(5, 'apply s_pure', { ...sel, explored: true, completed: true })]
    })
    const root = goal(0, 'g', {
      ...semi, children: [tactic(1, 'apply s_pick', {
        ...semi, explored: true, children: [cluster(-10, [caseY, caseX])]
      })]
    })
    assert.equal(serializeTree(root),
      'apply s_pick\n· apply s_pure\n· apply s_pure')
  })

test('an off-path *partially* worked goal keeps its work, sorry at the frontier',
  () => {
    // caseY was worked on (`intro`, leaving an unproven subgoal) then navigated
    // away from, so its subtree is stashed in a cache. We keep `intro` and put
    // `sorry` at the unfinished frontier rather than discarding the work.
    const caseYCache = goal(2, 'caseY', {
      status: 'semiselected', children: [
        tactic(30, 'intro', {
          ...semi, explored: true, children: [cluster(-31, [
            goal(32, 'caseY1', sel)])]  // unproven frontier
        })]
    })
    const caseY = goal(2, 'caseY', {
      status: 'unselected', leanOrder: 0, children: [], cache: caseYCache
    })
    const caseX = goal(4, 'caseX', {
      ...semi, leanOrder: 1, children: [
        tactic(5, 'rfl', { ...sel, explored: true, completed: true })]
    })
    const root = goal(0, 'g', {
      ...semi, children: [tactic(1, 'T', {
        ...semi, explored: true, children: [cluster(-10, [caseY, caseX])]
      })]
    })
    assert.equal(serializeTree(root), 'T\n· intro\n  sorry\n· rfl')
  })

test('backing up to a tactic drops its subgoals\' cached work to sorry', () => {
  // We proved caseX (a clustered subgoal) then clicked back to the parent
  // tactic T. `cacheChild` stashed caseX's proof in its cache and left T
  // selected with no subgoal on the active path. Backing up sets that work
  // aside, so every subgoal must serialize to `sorry`, not the cached proof.
  const caseXCache = goal(4, 'caseX', {
    ...sel, completed: true, children: [
      tactic(5, 'apply s_pure', { ...sel, explored: true, completed: true })]
  })
  const caseX = goal(4, 'caseX', {
    status: 'unselected', completed: true, leanOrder: 0,
    children: [], cache: caseXCache
  })
  const caseY = goal(6, 'caseY', { status: 'unselected', leanOrder: 1 })
  const root = goal(0, 'g', {
    ...semi, children: [tactic(1, 'apply s_pick', {
      ...sel, explored: true, children: [cluster(-10, [caseX, caseY])]
    })]
  })
  assert.equal(serializeTree(root), 'apply s_pick\n· sorry\n· sorry')
})

test('backing up to a single-subgoal tactic drops cached work to sorry', () => {
  const g1Cache = goal(2, 'g1', {
    ...sel, completed: true, children: [
      tactic(3, 'rfl', { ...sel, explored: true, completed: true })]
  })
  const g1 = goal(2, 'g1', {
    status: 'unselected', completed: true, children: [], cache: g1Cache
  })
  const root = goal(0, 'g', {
    ...semi, children: [tactic(1, 'intro', {
      ...sel, explored: true, children: [cluster(-10, [g1])]
    })]
  })
  assert.equal(serializeTree(root), 'intro\nsorry')
})

test('an abandoned tactic (replaced by another on the same goal) is ignored',
  () => {
    // At goal g we tried `wrong` (cached, even completed) then selected `right`
    // instead. `right` is g's active tactic, so `wrong` must not appear.
    const wrongCache = tactic(1, 'wrong', {
      ...sel, explored: true, completed: true
    })
    const root = goal(0, 'g', {
      ...semi, children: [
        tactic(1, 'wrong', {
          status: 'unselected', completed: true, children: [], cache: wrongCache
        }),
        tactic(2, 'right', { ...sel, explored: true })
      ]
    })
    assert.equal(serializeTree(root), 'right')
  })

/* Base indentation for splicing into the file */

test('baseIndent left-pads every line after the first', () => {
  const root = goal(0, 'g', {
    ...semi, children: [tactic(1, 'apply And.intro', {
      ...semi, explored: true, children: [cluster(-10, [
        goal(2, 'g1', {
          ...sel, leanOrder: 0,
          children: [tactic(3, 'rfl', { ...sel, explored: true })]
        }),
        goal(4, 'g2', {
          ...semi, leanOrder: 1,
          children: [tactic(5, 'trivial', { ...semi, explored: true })]
        })
      ])]
    })]
  })
  assert.equal(serializeTree(root, '  '),
    'apply And.intro\n  · rfl\n  · trivial')
})

/* Metavariable-linked clusters */

// Build a tactic T that produces a 2-goal linked cluster [A, B] (A resolves the
// shared mvar) plus, optionally, an independent goal. Solving A carries B as a
// copy; the original B is inactive (redirectTo set) and B' holds B's proof.
//
//   A (leanOrder aOrder) -TA-> [A's real subgoal (closed by 'a1'), B' (copy)]
//   B (leanOrder bOrder) inactive, redirectTo = copyId
function linkedClusterRoot(aOrder: number, bOrder: number,
  extra: ReturnType<typeof goal>[] = []): ReturnType<typeof goal> {
  const copyId = 100 // B' : proof of B lives here
  const bCopy = goal(copyId, "B'", {
    ...semi, originalId: 20, leanOrder: 0,
    children: [tactic(101, 'b1', { ...semi, explored: true })]
  })
  const aReal = goal(11, 'A-sub', {
    ...sel, leanOrder: 0,
    children: [tactic(12, 'a1', { ...sel, explored: true })]
  })
  const A = goal(10, 'A', {
    ...semi, leanOrder: aOrder,
    children: [tactic(13, 'TA', {
      ...semi, explored: true, children: [cluster(-14, [aReal, bCopy])]
    })]
  })
  const B = goal(20, 'B', { ...semi, leanOrder: bOrder, redirectTo: copyId })
  return goal(0, 'g', {
    ...semi, children: [tactic(1, 'T', {
      ...semi, explored: true, children: [cluster(-30, [A, B, ...extra])]
    })]
  })
}

test('linked cluster, resolver already first: bullets, sibling via its copy',
  () => {
    // Lean order [A=0, B=1]: A precedes B, so plain bullets work. B's bullet
    // comes from B' (b1). A's bullet is TA then its own subgoal (a1); the copy
    // is NOT proved inside A.
    const root = linkedClusterRoot(0, 1)
    assert.equal(serializeTree(root),
      'T\n· TA\n  a1\n· b1')
  })

test('linked cluster, resolver after sibling: on_goal targets the resolver first',
  () => {
    // Lean order [B=0, A=1]: B is presented first but depends on A's mvar
    // assignment, so we must run A first via `on_goal 2`, then B is goal 1.
    const root = linkedClusterRoot(1, 0)
    assert.equal(serializeTree(root),
      'T\n' +
      'on_goal 2 =>\n' +
      '  TA\n' +
      '  a1\n' +
      'on_goal 1 =>\n' +
      '  b1')
  })

test('linked cluster with a trailing independent goal keeps on_goal indices',
  () => {
    // Lean order [B=0, A=1, D=2]. Emit A (on_goal 2), then B (on_goal 1),
    // then D (on_goal 1, since B and A are gone D is the only goal left).
    const D = goal(40, 'D', {
      ...semi, leanOrder: 2,
      children: [tactic(41, 'd1', { ...semi, explored: true })]
    })
    const root = linkedClusterRoot(1, 0, [D])
    assert.equal(serializeTree(root),
      'T\n' +
      'on_goal 2 =>\n' +
      '  TA\n' +
      '  a1\n' +
      'on_goal 1 =>\n' +
      '  b1\n' +
      'on_goal 1 =>\n' +
      '  d1')
  })
