/**
 * TODO_0312 / THY_0040 — array representation independence, executable pins.
 *
 * arr_get/arr_set compute one relation across three presentations of an array:
 *   - flat arrlit   (FFI O(1) / clause arr_idx O(N))
 *   - bit-indexed trie tn(L,V,R)  (FFI trieNav / clause trie_get, O(log N))
 *   - acons list [V|T]            (clause arr_idx O(N))
 * The choice of presentation is a pure optimization (the FFI principle): it
 * cannot change any result. Two consequences this file pins:
 *
 *  1. arrToTrie(arrlit) denotes EXACTLY the arrlit — equal in-bounds, both fail
 *     out-of-bounds. The zero-fill placed at intermediate trie nodes by
 *     _trieInsert sits at non-terminal positions and is never navigated to, so
 *     the trie introduces no spurious out-of-domain entries (the crux of the
 *     representation-independence theorem, THY_0040 Lemma 1).
 *
 *  2. End-to-end: on a deterministic bytecode program, all FOUR presentation ×
 *     resolver combinations — exec/FFI-off (arrlit+arr_idx), exec/FFI-on
 *     (arrlit+FFI), explore/FFI-off (trie+trie_get, via bytecodeToTrie),
 *     explore/FFI-on (arrlit+FFI) — reach the SAME final state. This is the
 *     standing gate that the exec/explore representation asymmetry is benign.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { arrToTrie, trieNav } from '../../calculus/ill/lib/ffi/array.js';
import { show } from '../../lib/engine/show.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { toObject } from '../../lib/engine/fact-set.js';

// ── 1. arrlit ≡ trie on every index, including out-of-bounds ──────────────
describe('THY_0040 Lemma 1 — arrToTrie denotes exactly the arrlit (incl OOB)', () => {
  it('trieNav agrees with flat indexing on in-bounds AND out-of-bounds indices', () => {
    Store.clear();
    // Deterministic LCG — Math.random is unavailable in this codebase's spirit
    // and we want a reproducible corpus.
    let seed = 0x9e3779b9 >>> 0;
    const rnd = () => { seed = (seed * 1664525 + 1013904223) >>> 0; return seed / 0x100000000; };

    let checks = 0;
    for (let trial = 0; trial < 400; trial++) {
      const n = 1 + Math.floor(rnd() * 40);
      const elems = new Uint32Array(n);
      for (let i = 0; i < n; i++) elems[i] = Store.put('binlit', [BigInt(Math.floor(rnd() * 512))]);
      const arrlit = Store.put('arrlit', [elems]);
      const trie = arrToTrie(arrlit);
      for (let i = 0; i < n + 8; i++) {          // n+8 reaches past the end
        const arrlitVal = (i < n) ? elems[i] : null;   // flat: value or OOB-fail
        const trieVal = trieNav(trie, BigInt(i));       // trie: value or miss
        assert.equal(trieVal, arrlitVal,
          `index ${i} of ${n}: trie ${trieVal === null ? 'miss' : show(trieVal)} ` +
          `vs arrlit ${arrlitVal === null ? 'OOB' : show(arrlitVal)}`);
        checks++;
      }
    }
    assert.ok(checks > 10000, 'exercised a substantial corpus');
  });
});

// ── 2. All four presentation × resolver combinations agree, end-to-end ────
const PROGRAMS = path.join(import.meta.dirname, '../../calculus/ill/programs');
// Deterministic bytecode program: a single execution path, one leaf.
const DET = path.join(PROGRAMS, 'multisig_nocall_solc.ill');

// A leaf/exec state as sorted fact strings. The bytecode fact is the ONE fact
// whose presentation legitimately differs (arrlit under exec / FFI, trie under
// explore-clause via bytecodeToTrie) — denotationally identical by Lemma 1, so
// we split it out: everything else must match exactly, and each run must carry
// exactly one bytecode fact (whatever its presentation).
function factsSplit(state) {
  const o = (state && state.linear && typeof state.linear.group === 'function') ? toObject(state) : state;
  const all = Object.keys(o.linear).map(h => show(Number(h)));
  const bytecode = all.filter(s => s.startsWith('bytecode(')).sort();
  const rest = all.filter(s => !s.startsWith('bytecode(')).sort();
  return { bytecode, rest };
}

describe('THY_0040 Cor. — exec/explore × FFI-on/off agree modulo array presentation', () => {
  it('arrlit+arr_idx, arrlit+FFI, trie+trie_get reach one state (bytecode aside)', () => {
    const run = (kind, ffi) => {
      Store.clear();
      const calc = mde.load(DET, { cache: false });
      const st = mde.normalizeQuery(calc.queries.get('symex'));
      if (kind === 'exec') return factsSplit(calc.exec(st, { maxSteps: 5000, dangerouslyUseFFI: ffi }).state);
      const leaves = getAllLeaves(calc.explore(st, { maxDepth: 5000, dangerouslyUseFFI: ffi }));
      assert.equal(leaves.length, 1, 'the program is deterministic (one leaf)');
      return factsSplit(leaves[0].state);
    };

    const execOff = run('exec', false);   // arrlit + clause arr_idx (O(N))
    const execOn = run('exec', true);    // arrlit + FFI (O(1))
    const explOff = run('explore', false); // trie + clause trie_get (via bytecodeToTrie)
    const explOn = run('explore', true);  // arrlit/trie + FFI

    // Everything except the array presentation is identical across all four.
    assert.deepEqual(execOn.rest, execOff.rest, 'exec: FFI ≡ clause');
    assert.deepEqual(explOff.rest, execOff.rest, 'explore-clause (trie) ≡ exec-clause (arrlit) — the benign asymmetry');
    assert.deepEqual(explOn.rest, execOff.rest, 'explore-FFI ≡ exec-clause');

    // Each run carries exactly one bytecode fact; exec keeps arrlit, explore-off
    // is the trie — different presentation, one denotation (Lemma 1).
    for (const r of [execOff, execOn, explOff, explOn]) assert.equal(r.bytecode.length, 1);
    assert.ok(execOff.bytecode[0].includes('[0x'), 'exec keeps the flat arrlit');
    assert.ok(explOff.bytecode[0].includes('tn('), 'explore-clause swaps to the trie');
  });
});
