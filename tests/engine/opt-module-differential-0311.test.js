/**
 * TODO_0311 — per-opt-module differential over the symex corpus.
 *
 * `profile-differential.test.js` pins bare (ALL opts off) ≡ full (all on).
 * `ffi-differential.test.js` pins FFI-on ≡ FFI-off. This third axis toggles
 * each individually-gated optimization module OFF ON ITS OWN, leaving the rest
 * on, and requires the explore leaf classes to be unchanged across the corpus.
 *
 * Why: bare-vs-full can mask a per-module bug whose effect is cancelled by
 * another module also being off. Isolating one module at a time makes each
 * `opt/` checkbox mechanical — a divergence names the exact module.
 *
 * Only the four profile flags actually consumed to gate a module are toggled
 * here (optimizer.js `PROFILES`): `fingerprint`, `prediction`, `discTree`,
 * `deltaBypass`. The remaining flags in the profile schema are not currently
 * read to gate their module (FFI is toggled via `dangerouslyUseFFI` at call
 * time — covered by ffi-differential; the rest always run and are covered by
 * the FFI and profile differentials). New gated modules should be added here.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
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

const FULL = {
  ffi: true, discTree: true, deltaBypass: true, preserved: true,
  compiledSub: true, fingerprint: true, loliDrain: true,
  structuralMemo: true, prediction: true, solver: true,
};
const TOGGLES = ['fingerprint', 'prediction', 'discTree', 'deltaBypass'];

function leafClasses(file, profile) {
  Store.clear();
  const calc = mde.load(file, { cache: false, profile });
  const q = calc.queries.get('symex');
  assert.ok(q, `${file}: has a #symex query`);
  const tree = calc.explore(mde.normalizeQuery(q), { maxDepth: 500 });
  const c = {};
  for (const l of getAllLeaves(tree)) { const k = classifyLeaf(l.state); c[k] = (c[k] || 0) + 1; }
  return c;
}

describe('TODO_0311 — each gated opt module off individually ≡ full', { timeout: 120000, concurrency: 1 }, () => {
  for (const name of CORPUS) {
    it(`${name}: disabling any single opt module preserves the leaf classes`, () => {
      const file = path.join(PROGRAMS, `${name}.ill`);
      const base = leafClasses(file, FULL);
      for (const flag of TOGGLES) {
        const c = leafClasses(file, { ...FULL, [flag]: false });
        assert.deepEqual(c, base,
          `${name}: disabling '${flag}' diverged from full — that module disagrees with the rest`);
      }
    });
  }
});
