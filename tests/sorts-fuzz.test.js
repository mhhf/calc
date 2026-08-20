/**
 * Sort-order fuzz (TODO_0011 rung 1 + §4 materialized closure) — the FFI
 * principle one level up: "the sort table is optimization, membership
 * proof is semantics."
 *
 * Random subsort DAGs are loaded end-to-end (declaration surface → sedge
 * fact harvest → compiled ancestor index → CLOSURE MATERIALIZATION: the
 * loader injects every strict pair as a ground `subsort a b` fact), then
 * EVERY pair (a, b) is checked three ways: the compiled table, a REAL
 * backward-prover query `subsort a b` over the loaded clause set (facts +
 * subsort/refl — no recursive closure clause, so committed choice cannot
 * lose paths), and an independent reachability closure computed here from
 * the raw edge list. All three must agree exactly. lub results are
 * verified minimal upper bounds by enumeration.
 *
 * The query face being COMPLETE is the point of §4: before
 * materialization, a recursive `step` clause under the committed-choice
 * backchainer silently lost paths through multi-out-edge nodes (first
 * `sedge a T` candidate commitment) — the certifyLeq certificate
 * workaround existed for exactly that. A deterministic regression for the
 * old failing shape (a→b, a→c, c→d ⇒ a ≤ d) is asserted explicitly.
 *
 * (Classifier ≤ 'type' and sort-hood are definitional, not clausal — they
 * are outside the deductive fragment and not fuzzed here.)
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../lib/kernel/store.js';
import mde from '../lib/engine/index.js';
import tillConfig from '../calculus/till/calculus-config.js';
import { SORT_PREDS } from '../lib/engine/sorts.js';
import { backchain } from '../lib/engine/backchain.js';

const SORTS = path.join(import.meta.dirname, '../calculus/till/prelude/sorts.till');

// Deterministic PRNG (mulberry32) — reproducible trials.
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

let dir;
before(() => { dir = fs.mkdtempSync(path.join(os.tmpdir(), 'sorts-fuzz-')); });
after(() => { fs.rmSync(dir, { recursive: true, force: true }); });

function randomProgram(rand, k) {
  const sorts = Array.from({ length: k }, (_, i) => `fz${i}`);
  const edges = [];
  for (let i = 0; i < k; i++) {
    for (let j = i + 1; j < k; j++) {
      if (rand() < 0.35) edges.push([sorts[i], sorts[j]]); // i<j ⇒ acyclic
    }
  }
  const src = [`#import(${SORTS})`]
    .concat(sorts.map(s => `${s}: type.`))
    .concat(edges.map(([a, b]) => `${a} <: ${b}.`))
    .join('\n') + '\n';
  return { sorts, edges, src };
}

/** Backward-prover query `subsort a b` over the loaded clause set. */
function querySubsort(calc, a, b) {
  const atom = (n) => Store.put('atom', [n]);
  const goal = Store.put(SORT_PREDS.SUB, [atom(a), atom(b)]);
  const res = backchain(goal, calc.clauses, calc.definitions, { maxDepth: 16 });
  return !!(res && res.success);
}

describe('compiled sort index ≡ backward-prover membership (fuzz)', () => {
  it('table ≡ prover query ≡ independent reachability, every pair, 40 random DAGs', () => {
    let pairs = 0;
    for (let trial = 0; trial < 40; trial++) {
      const rand = rng(0xC0FFEE + trial);
      const { sorts, edges, src } = randomProgram(rand, 3 + Math.floor(rand() * 4));
      if (edges.length === 0) continue; // presence-gated: no system builds
      const p = path.join(dir, `t${trial}.ill`);
      fs.writeFileSync(p, src);
      const calc = mde.load(p, { calculusConfig: tillConfig, cache: false });
      assert.ok(calc.sorts, `trial ${trial}: system present`);
      // Independent reachability (test-local closure over the raw edge list)
      const reach = new Map(sorts.map(s => [s, new Set([s])]));
      let changed = true;
      while (changed) {
        changed = false;
        for (const [x, y] of edges) {
          for (const z of reach.get(y)) {
            if (!reach.get(x).has(z)) { reach.get(x).add(z); changed = true; }
          }
        }
      }
      for (const a of sorts) {
        for (const b of sorts) {
          const expected = reach.get(a).has(b);
          const table = calc.sorts.subsort(a, b);
          const proved = querySubsort(calc, a, b);
          assert.equal(table, expected,
            `trial ${trial}: table subsort(${a}, ${b})=${table}, reachability says ${expected}; edges=${JSON.stringify(edges)}`);
          assert.equal(proved, expected,
            `trial ${trial}: prover subsort(${a}, ${b})=${proved}, reachability says ${expected}; edges=${JSON.stringify(edges)}`);
          pairs++;
        }
      }
    }
    assert.ok(pairs > 100, `exercised ${pairs} pairs`);
  });

  it('multi-out-edge transitivity proves via query (the pre-§4 failing shape)', () => {
    // a→b, a→c, c→d: under a recursive closure clause, committed choice
    // could commit `sedge a T` to T=b and lose the a→c→d path. With
    // materialized facts the query is a direct lookup — must prove.
    const src = [
      `#import(${SORTS})`,
      'ma: type.', 'mb: type.', 'mc: type.', 'md: type.',
      'ma <: mb.', 'ma <: mc.', 'mc <: md.',
    ].join('\n') + '\n';
    const p = path.join(dir, 'multi-edge.ill');
    fs.writeFileSync(p, src);
    const calc = mde.load(p, { calculusConfig: tillConfig, cache: false });
    assert.ok(querySubsort(calc, 'ma', 'md'), 'a ≤ d through the second out-edge');
    assert.ok(querySubsort(calc, 'ma', 'ma'), 'reflexive base (subsort/refl)');
    assert.ok(!querySubsort(calc, 'md', 'ma'), 'no flip');
    assert.ok(!querySubsort(calc, 'mb', 'mc'), 'no cross-branch order');
  });

  it('lub is a minimal upper bound (verified by enumeration) across 25 DAGs', () => {
    for (let trial = 0; trial < 25; trial++) {
      const rand = rng(0xBEEF00 + trial);
      const { sorts, edges, src } = randomProgram(rand, 4 + Math.floor(rand() * 3));
      if (edges.length === 0) continue;
      const p = path.join(dir, `l${trial}.ill`);
      fs.writeFileSync(p, src);
      const calc = mde.load(p, { calculusConfig: tillConfig, cache: false });
      const sys = calc.sorts;
      // Only names actually used as sorts enter the universe — a declared-
      // but-unused `fzN: type.` is a token, not a sort.
      const inUniverse = sorts.filter(s => sys.isSort(s));
      for (const a of inUniverse) {
        for (const b of inUniverse) {
          const uppers = inUniverse.filter(u => sys.subsort(a, u) && sys.subsort(b, u));
          const r = sys.lub([a, b]);
          if (r.error) {
            // Correct iff no unique minimal common upper bound exists
            const minimals = uppers.filter(u => !uppers.some(v => v !== u && sys.subsort(v, u)));
            assert.notEqual(minimals.length, 1,
              `trial ${trial}: lub(${a}, ${b}) errored but ${minimals[0]} is the unique minimal upper bound`);
          } else {
            assert.ok(uppers.includes(r.sort), `trial ${trial}: lub(${a}, ${b})=${r.sort} not an upper bound`);
            assert.ok(!uppers.some(u => u !== r.sort && sys.subsort(u, r.sort)),
              `trial ${trial}: lub(${a}, ${b})=${r.sort} not minimal`);
          }
        }
      }
    }
  });
});
