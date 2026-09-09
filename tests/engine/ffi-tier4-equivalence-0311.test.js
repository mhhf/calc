/**
 * TODO_0311 — proveWithFFI (FFI-on) ≡ proveNaive (FFI-off) on persistent goals
 * that fall through to Tier-4 clause resolution.
 *
 * The audit's premise: every fast path standing in for clause resolution must
 * AGREE with it on every goal shape. proveWithFFI (opt/ffi.js, the FFI-on
 * persistent prover) and proveNaive (family/lnl/lib/persistent.js, the FFI-off
 * reference) are DIFFERENT code, so an asymmetry in either hides until a goal
 * shape exercises it.
 *
 * The witnessed asymmetry (fixed): proveWithFFI's Tier-4 backchain call omitted
 * `allBuckets`, so the backchainer defaulted it to `!useFFI = false`. A
 * persistent goal with an UNBOUND first argument (fa='_') whose clauses are
 * keyed under a SPECIFIC first-arg (an atom / constructor) then had its clause
 * bucket silently skipped — the goal was unprovable under FFI-on though FFI-off
 * (proveNaive forces `allBuckets: true`) proved it. Below, `!p X` with the sole
 * clause `p a` is exactly that shape: under the bug FFI-on left `trig`
 * unconsumed, FFI-off produced `got(a)`.
 *
 * A second asymmetry aligned in the same fix (not separately witnessed here):
 * proveWithFFI's Tier-4 output binding did not canonicalize, while proveNaive
 * does — bin.ill's `plus` clauses resolve to non-canonical i/o/e numerals, so a
 * raw Tier-4 output could desync a later FFI tier keyed on the canonical tag.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { show } from '../../lib/engine/show.js';

// `!p X` with X unbound; the only clause `p a` is keyed under atom `a`, so the
// goal's fa='_' must search all buckets to find it.
const PROG =
  'thing : type.\n' +
  'a : thing.\n' +
  'p : thing -> type.\n' +
  'pa : p a.\n' +
  'trig : type.\n' +
  'got : thing -> type.\n' +
  'r : trig * !p X -o { got X }.\n' +
  '#symex trig.\n';

function finalFacts(ffi) {
  Store.clear();
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'ffi-tier4-'));
  const file = path.join(dir, 'prog.ill');
  fs.writeFileSync(file, PROG);
  try {
    const calc = mde.load(file, { cache: false });
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    const res = calc.exec(state, { maxSteps: 10, dangerouslyUseFFI: ffi });
    return Object.keys(res.state.linear).map(h => show(Number(h))).sort();
  } finally {
    for (const f of fs.readdirSync(dir)) fs.unlinkSync(path.join(dir, f));
    fs.rmdirSync(dir);
  }
}

describe('TODO_0311 — FFI-on Tier-4 ≡ FFI-off on unbound-first-arg persistent goals', () => {
  it('proves `!p X` from an atom-keyed clause under both FFI modes', () => {
    const off = finalFacts(false);
    const on = finalFacts(true);
    assert.deepEqual(off, ['got(a)'], 'FFI-off resolves !p X to p a');
    assert.deepEqual(on, off, 'FFI-on must reach the same result (allBuckets Tier-4 fix)');
  });
});
