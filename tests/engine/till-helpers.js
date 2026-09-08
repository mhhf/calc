/**
 * Shared till test helpers — canonical state/trace views and loaders used
 * across the till suites (till-settle, till-woplus, till-fuzz, till-lint,
 * settle-meta, settle-determinism). One definition; the copies these files
 * carried drifted in key format (n vs n/d) — this module is the single
 * source of truth (short stamp form: 'wood@0', 'plank@1/2').
 */

import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import convert from '../../lib/engine/convert.js';
import tillConfig from '../../calculus/till/calculus-config.js';
import { ratParts } from '../../lib/kernel/rat-term.js';

export const SPEC = (f) => path.join(import.meta.dirname, '../../calculus/till/tests/forward', f);
export const FIX = (f) => path.join(import.meta.dirname, '../fixtures', f);
export const GAME = (f) => path.join(import.meta.dirname, '../../calculus/till/game', f);

export const loadTill = (p, cfg = tillConfig) => mde.load(p, { calculusConfig: cfg, cache: false });
// Strict sort checking OFF — for fixtures whose POINT is an ill-sorted shape
// the engine must still handle (e.g. bare literal facts, till-litfact.ill).
export const loadTillPermissive = (p, cfg = tillConfig) =>
  mde.load(p, { calculusConfig: cfg, cache: false, strictTypes: false });
export const initQuery = (calc, kind) => convert.decomposeQuery(calc.splitQueries.get(kind).lhsHash);
export const atom = (n) => Store.put('atom', [n]);

const innerName = (h) =>
  (Store.tag(h) === 'atom' ? Store.child(h, 0) : Store.tag(h));

/** Multiset view of a timed state: { 'inner@stamp': count } (stamp short
 *  form: integer 'n', otherwise 'n/d'; unstamped facts read as @0). */
export function stamped(state) {
  const out = {};
  for (const [hStr, c] of Object.entries(state.linear)) {
    const h = Number(hStr);
    const isAt = Store.tag(h) === 'at';
    const inner = isAt ? Store.child(h, 0) : h;
    const [n, d] = isAt ? ratParts(Store.child(h, 1)) : [0n, 1n];
    const key = `${innerName(inner)}@${d === 1n ? n : `${n}/${d}`}`;
    out[key] = (out[key] || 0) + c;
  }
  return out;
}

/** stamped() as a canonical sorted string — 'key'x'count' comma-joined. */
export const stampedStr = (state) =>
  Object.entries(stamped(state)).sort().map(([k, v]) => `${k}x${v}`).join(',');

/** Stamp-blind multiset of inner heads: { name: count }. */
export function bag(state) {
  const out = {};
  for (const [hStr, c] of Object.entries(state.linear)) {
    let h = Number(hStr);
    if (Store.tag(h) === 'at') h = Store.child(h, 0);
    const k = innerName(h);
    out[k] = (out[k] || 0) + c;
  }
  return out;
}

/** bag() as a canonical sorted string. */
export const bagStr = (state) =>
  Object.entries(bag(state)).sort().map(([k, v]) => `${k}x${v}`).join(',');

/** Canonical event-trace string: 'rule@n/d:alt' space-joined. */
export const traceKey = (events) =>
  events.map(e => `${e.rule}@${ratParts(e.activation).join('/')}:${e.alt ?? ''}`).join(' ');
