/**
 * TODO_0307 Track 2 — FFI-off ≡ FFI-on on every symbolic-execution config.
 *
 * The FFI principle: FFI is optimization, clause resolution is the semantics.
 * A run with `dangerouslyUseFFI` off must reach the SAME leaf classes as the
 * FFI-accelerated run — for the plain program, for grade-0-fact specialization,
 * and for specialization + basic-block fusion + SROA.
 *
 * Two independent holes made FFI-off diverge before this pin:
 *
 *   1. bytecode→trie conversion (index.js explore boundary) ran unconditionally
 *      under FFI-off, but grade-0-fact-specialized rules PRESERVE the bytecode
 *      as `bytecode(arrlit …)` (arr_get already resolved at compile). Converting
 *      the live fact to a trie made that pattern un-matchable → the whole run
 *      stalled at the first instruction (1 RUNNING leaf). Fixed by gating the
 *      conversion on the absence of grade-0 specialization.
 *
 *   2. the backward proof cache (opt/backward-cache.js, the FFI-off tier) bound
 *      an output position only when it was a BARE metavar, else compared it to
 *      the cached value by exact hash. A fused rule carries a partial output
 *      pattern — `arr_set(A, I, V, acons(H, T))` — so the compound '-' position
 *      was rejected as a mismatch (return null → cached_failure) even though the
 *      proof succeeded, poisoning every later step into a symbolic stall. Fixed
 *      by UNIFYING each output position with the computed value.
 *
 * Both bit only FFI-off (the cache and the trie conversion are FFI-off-only
 * paths), so FFI-on never regressed and never revealed them.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import fs from 'fs';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { loadBytecode, bytecodeArrGetGuard } from '../../calculus/ill/lib/bytecode-loader.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { classifyLeaf } from '../../calculus/ill/index.js';
import { ILL_SROA_CONFIG } from '../../calculus/ill/lib/compose-config.js';

const DIR = import.meta.dirname;
const CODE = path.join(DIR, '../../calculus/ill/programs/multisig_nocall_solc_code.ill');
const SYMEX = path.join(DIR, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill');
const HEX = fs.readFileSync(CODE, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];
const GOLDEN = { STOP: 18, REVERT: 13 };

function classes(loadExtra, ffi) {
  Store.clear();
  const bc = loadBytecode(HEX);
  const opts = {
    cache: false, extraGrade0Facts: bc.facts, scopeGuard: bytecodeArrGetGuard,
    fusionBarriers: bc.barrierRefs, ...loadExtra,
  };
  const calc = mde.load(SYMEX, opts);
  const state = mde.normalizeQuery(calc.queries.get('symex'));
  const tree = calc.explore(state, { maxDepth: 500, dangerouslyUseFFI: ffi });
  const c = {};
  for (const l of getAllLeaves(tree)) { const k = classifyLeaf(l.state); c[k] = (c[k] || 0) + 1; }
  return c;
}

const SPECIALIZE = { fuseBasicBlocks: false, sroaConfig: { ...ILL_SROA_CONFIG, arrayPreds: [] } };
const FUSED = { fuseBasicBlocks: true };

describe('TODO_0307 Track 2 — FFI-off ≡ FFI-on on every symex config', { timeout: 60000, concurrency: 1 }, () => {
  it('no-facts (plain program): FFI-off explore matches the golden', () => {
    Store.clear();
    const calc = mde.load(SYMEX, { cache: false });
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    const c = {};
    for (const l of getAllLeaves(calc.explore(state, { maxDepth: 500 }))) {
      const k = classifyLeaf(l.state); c[k] = (c[k] || 0) + 1;
    }
    assert.deepStrictEqual(c, GOLDEN);
  });

  it('specialize-only: FFI-off === FFI-on === golden (hole #1: bytecode→trie gate)', () => {
    assert.deepStrictEqual(classes(SPECIALIZE, true), GOLDEN, 'FFI-on');
    assert.deepStrictEqual(classes(SPECIALIZE, false), GOLDEN, 'FFI-off');
  });

  it('fusion + SROA: FFI-off === FFI-on === golden (hole #2: cache output unification)', () => {
    assert.deepStrictEqual(classes(FUSED, true), GOLDEN, 'FFI-on');
    assert.deepStrictEqual(classes(FUSED, false), GOLDEN, 'FFI-off');
  });
});
