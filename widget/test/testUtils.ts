// Shared helpers for the TypeScript unit tests. Lives outside src/ so it is
// never picked up by the tsc/rollup build; only ever loaded by `tsx` when
// running tests.

import type { Node } from '../src/Tree'
import type { APINode, APIData } from '../src/Handler'

/* Node builders */

export function goal(id: number, display = 'g' + id,
  overrides: Partial<Node> = {}): Node {
  return {
    kind: 'goal', id, display, completed: false, status: 'unselected',
    visible: true, explored: false, cache: undefined, children: [], ...overrides
  }
}

export function tactic(id: number, display = 't' + id,
  overrides: Partial<Node> = {}): Node {
  return {
    kind: 'tactic', id, display, completed: false, status: 'unselected',
    visible: true, explored: false, cache: undefined, children: [], ...overrides
  }
}

export function cluster(id: number, children: Node[],
  overrides: Partial<Node> = {}): Node {
  return {
    kind: 'cluster', id, display: '', completed: false, status: 'unselected',
    visible: true, explored: false, cache: undefined, children, ...overrides
  }
}

/* Tree queries */

export function allNodes(n: Node): Node[] {
  return [n, ...n.children.flatMap(allNodes)]
}

export function findById(n: Node, id: number): Node | undefined {
  return allNodes(n).find((x) => x.id === id)
}

export function countSelected(n: Node): number {
  return allNodes(n).filter((x) => x.status === 'selected').length
}

export function selectedIds(n: Node): number[] {
  return allNodes(n).filter((x) => x.status === 'selected').map((x) => x.id)
}

/* Mock RPC session */

// `responder(method, id)` returns the children the backend would produce for a
// call on node `id`: a flat `APINode[]` of tactics for `getApplicableTactics`,
// or a clustered `APINode[][]` of subgoals for `getSubgoals`.
export type Responder = (method: string, id: number) => APINode[] | APINode[][]

export type MockRpc = {
  // Loosely typed so it can stand in for RpcSessionAtPos in tests.
  rs: { call: (method: string, params: any) => Promise<any> }
  calls: { method: string, id: number }[]
}

export function mockRpc(responder: Responder): MockRpc {
  const calls: { method: string, id: number }[] = []
  let counter = 0
  const rs = {
    async call(method: string, params: { id: number }) {
      calls.push({ method, id: params.id })
      const children = responder(method, params.id)
      const stateRef: APIData = { p: 'state-' + (counter++) }
      return [children, stateRef]
    }
  }
  return { rs, calls }
}

// A dummy editor position; the pure logic never inspects it.
export const dummyPos: any = { line: 0, character: 0 }
