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

  it('diamond DAG: lub(b,c)=d and transitive closure', () => {
    // a <: b, a <: c, b <: d, c <: d — diamond shape.
    // Closure must reach dd from da via BOTH paths; lub of the two branches
    // is the unique minimal common ancestor dd.
    const src = [
      `#import(${SORTS})`,
      'da: type.', 'db: type.', 'dc: type.', 'dd: type.',
      'da <: db.', 'da <: dc.', 'db <: dd.', 'dc <: dd.',
    ].join('\n') + '\n';
    const p = path.join(dir, 'diamond.ill');
    fs.writeFileSync(p, src);
    const calc = mde.load(p, { calculusConfig: tillConfig, cache: false });
    assert.ok(calc.sorts, 'system present');
    // Transitive closure: a reaches d through both b and c
    assert.ok(calc.sorts.subsort('da', 'dd'), 'table: a ≤ d (transitive)');
    assert.ok(querySubsort(calc, 'da', 'dd'), 'prover: a ≤ d');
    // Least upper bound of the two branches is d
    const r = calc.sorts.lub(['db', 'dc']);
    assert.ok(!r.error, `lub(b,c) should succeed: ${r.error}`);
    assert.equal(r.sort, 'dd', 'lub(b, c) = d');
    // Reflexivity for every node
    for (const s of ['da', 'db', 'dc', 'dd']) {
      assert.ok(calc.sorts.subsort(s, s), `reflexive: ${s} ≤ ${s}`);
    }
    // b and c are incomparable (no cross-branch subsort)
    assert.ok(!calc.sorts.subsort('db', 'dc'), 'b ≤ c should not hold');
    assert.ok(!calc.sorts.subsort('dc', 'db'), 'c ≤ b should not hold');
  });

  it('isolated sort: not in sort universe, reflexivity only', () => {
    // iz is declared as `type` but has no edges — it does not enter the sort
    // universe (presence-gated: only sorts that appear as edge operands are
    // tracked). The compiled table's a===b shortcut still gives
    // subsort(iz,iz)=true; subsort/refl makes the prover query succeed too.
    const src = [
      `#import(${SORTS})`,
      'ea: type.', 'eb: type.', 'iz: type.',
      'ea <: eb.',
    ].join('\n') + '\n';
    const p = path.join(dir, 'isolated.ill');
    fs.writeFileSync(p, src);
    const calc = mde.load(p, { calculusConfig: tillConfig, cache: false });
    assert.ok(calc.sorts, 'system present');
    assert.ok(!calc.sorts.isSort('iz'), 'iz not in sort universe (no edges)');
    // Compiled: a===b shortcut holds even outside the universe
    assert.ok(calc.sorts.subsort('iz', 'iz'), 'compiled: iz ≤ iz (reflexive shortcut)');
    // Prover: subsort/refl makes iz ≤ iz provable
    assert.ok(querySubsort(calc, 'iz', 'iz'), 'prover: iz ≤ iz via subsort/refl');
    // No non-reflexive ancestors or descendants
    assert.ok(!calc.sorts.subsort('iz', 'ea'), 'iz ≰ ea');
    assert.ok(!calc.sorts.subsort('ea', 'iz'), 'ea ≰ iz');
    assert.ok(!querySubsort(calc, 'iz', 'ea'), 'prover: iz ≰ ea');
  });

  it('underscore-named sorts: separator regression (MINOR 1)', () => {
    // Edges `foo <: bar_x` and `foo_bar <: x`. With the OLD underscore clause-
    // key separator, both materialized facts would have key "foo_bar_x" and
    // one would overwrite the other. The current "/" separator keeps them
    // distinct ("foo/bar_x" vs "foo_bar/x"). Verifies both facts survive.
    const src = [
      `#import(${SORTS})`,
      'foo: type.', 'bar_x: type.', 'foo_bar: type.', 'sx: type.',
      'foo <: bar_x.', 'foo_bar <: sx.',
    ].join('\n') + '\n';
    const p = path.join(dir, 'underscore-sep.ill');
    fs.writeFileSync(p, src);
    const calc = mde.load(p, { calculusConfig: tillConfig, cache: false });
    assert.ok(calc.sorts, 'system present');
    // Both edges must survive as distinct materialized facts
    assert.ok(querySubsort(calc, 'foo', 'bar_x'), 'prover: foo ≤ bar_x');
    assert.ok(querySubsort(calc, 'foo_bar', 'sx'), 'prover: foo_bar ≤ sx');
    // Compiled table agrees
    assert.ok(calc.sorts.subsort('foo', 'bar_x'), 'table: foo ≤ bar_x');
    assert.ok(calc.sorts.subsort('foo_bar', 'sx'), 'table: foo_bar ≤ sx');
    // No cross-contamination between the two disconnected components
    assert.ok(!calc.sorts.subsort('foo', 'sx'), 'no cross: foo ≰ sx');
    assert.ok(!calc.sorts.subsort('foo_bar', 'bar_x'), 'no cross: foo_bar ≰ bar_x');
    assert.ok(!querySubsort(calc, 'foo', 'sx'), 'prover: no cross foo ≰ sx');
    assert.ok(!querySubsort(calc, 'foo_bar', 'bar_x'), 'prover: no cross foo_bar ≰ bar_x');
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
