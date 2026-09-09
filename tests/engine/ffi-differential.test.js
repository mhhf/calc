/**
 * FFI differential oracle — the general shield for the FFI principle.
 *
 * "FFI is optimization, clause resolution is the semantics." Every predicate
 * with an FFI implementation MUST also be provable by clause resolution, and
 * the two must agree. This oracle pins that at the whole-program level: for
 * each symbolic-execution program in the corpus, `explore` under FFI must reach
 * the SAME leaf classes as `explore` under clause-only resolution.
 *
 * Why this exists (TODO_0307 Track 2): two FFI-off-only divergences hid for a
 * long time because FFI-on and FFI-off run DIFFERENT code (proveWithFFI vs
 * proveNaive + the backward cache), and no test compared them across the symex
 * corpus. `profile-differential.test.js` covers the opt-on/off axis; this covers
 * the orthogonal FFI-on/off axis. Together they fence the fast paths to the
 * semantics — a divergence in any layer (FFI, compiled dispatch, backward cache,
 * clause resolution) shows up here as a leaf-class mismatch, without anyone
 * having to audit each fast path by hand.
 *
 * A new program with a `#symex` query should be added to CORPUS — the marginal
 * cost is one line and it extends the shield for free.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { classifyLeaf } from '../../calculus/ill/index.js';

const PROGRAMS = path.join(import.meta.dirname, '../../calculus/ill/programs');
const CORPUS = [
  'noffi_tiny',
  'toy-branch',
  'pure_linear',
  'multisig_nocall',
  'multisig',
  'multisig_nocall_solc',
  'multisig_nocall_solc_symbolic',
];

function leafClasses(file, ffi) {
  Store.clear();
  const calc = mde.load(file, { cache: false });
  const q = calc.queries.get('symex');
  assert.ok(q, `${file}: has a #symex query`);
  const tree = calc.explore(mde.normalizeQuery(q), { maxDepth: 500, dangerouslyUseFFI: ffi });
  const c = {};
  for (const l of getAllLeaves(tree)) { const k = classifyLeaf(l.state); c[k] = (c[k] || 0) + 1; }
  return c;
}

describe('FFI differential — explore(FFI) ≡ explore(clause-only) on the symex corpus', { timeout: 60000, concurrency: 1 }, () => {
  for (const name of CORPUS) {
    it(`${name}: FFI-on and FFI-off reach the same leaf classes`, () => {
      const file = path.join(PROGRAMS, `${name}.ill`);
      assert.deepStrictEqual(leafClasses(file, false), leafClasses(file, true),
        `${name}: FFI-off diverged from FFI-on — a fast path disagrees with clause resolution`);
    });
  }
});
