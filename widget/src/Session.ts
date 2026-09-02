import type { NodeAndStateRef } from './Handler'

/* Session abstraction for saving state when the user clicks away. */

const MAX_SESSIONS = 4

const store = new Map<string, NodeAndStateRef>()

export function sessionKey(uri: string, sessionId: number): string {
  return `${uri}#${sessionId}`
}

export function loadSession(key: string): NodeAndStateRef | null {
  const value = store.get(key)
  if (value === undefined) return null
  store.delete(key) // reinsert, so that `key` is the most recently used
  store.set(key, value)
  return value
}

export function saveSession(key: string, value: NodeAndStateRef): void {
  store.delete(key)
  store.set(key, value)
  for (const oldest of store.keys()) {
    if (store.size <= MAX_SESSIONS) break
    store.delete(oldest)
  }
}

export function clearSession(key: string): void {
  store.delete(key)
}
