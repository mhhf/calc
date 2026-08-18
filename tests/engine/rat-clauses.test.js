/**
 * Rational clause resolution vs FFI — TODO_0265 Phase 1 (FFI principle).
 *
 * FFI is optimization, theory is semantics: with FFI off, the q-operation
 * clauses in calculus/till/prelude/rat.ill must derive exactly what the
 * rational FFI computes, hash-for-hash after canonicalization. This is the
 * per-case counterpart of the fuzz walker's §3.12 rational trials.
 *
 * Split namespaces (D8.1 revised): the bin family (plus, mul, …) and the
 * q-family (qplus, qsub, …) never share a predicate. The contract tests at
 * the end pin that down: bin predicates on rational arguments fail on both
 * paths, and bin×bin behavior is untouched.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import backward from '../../lib/engine/backchain.js';
import { makeILLBackchainOpts } from '../../lib/engine/ill/backchain-ill.js';
import { binlitTheory } from '../../lib/engine/ill/binlit-theory.js';
import { ratlitTheory, putRat, installRatlitTheory } from '../../lib/engine/theories/ratlit-theory.js';
import { defaultTheories, buildCanonicalizer } from '../../lib/kernel/eq-theory.js';
import { apply } from '../../lib/kernel/substitute.js';

const RAT_ILL = path.join(import.meta.dirname, '../../calculus/till/prelude/rat.ill');

const bin = (n) => Store.put1('binlit', n);
const mv = (name) => Store.put('metavar', [name]);

let ec, canonicalize, baseOpts;

function prove(goal, useFFI) {
  return backward.prove(goal, ec.clauses, ec.definitions, {
    ...baseOpts, maxDepth: 20000, allBuckets: true, useFFI,
  });
}

/** Prove with and without FFI; both must succeed and agree canonically. */
function agree(pred, inputs, expected) {
  const out = mv('R');
  const goal = Store.put(pred, [...inputs, out]);
  for (const useFFI of [true, false]) {
    const res = prove(goal, useFFI);
    assert.ok(res.success, `${pred} ${useFFI ? 'FFI' : 'clause'} path succeeds`);
    let val = out;
    for (let i = 0; i < 500; i++) { const n = apply(val, res.theta); if (n === val) break; val = n; }
    assert.equal(canonicalize(val), expected,
      `${pred} ${useFFI ? 'FFI' : 'clause'} result canonical`);
  }
}

/** Boolean predicate: FFI and clause paths agree on provability. */
function agreeBool(pred, inputs, expected) {
  const goal = Store.put(pred, inputs);
  for (const useFFI of [true, false]) {
    const res = prove(goal, useFFI);
    assert.equal(res.success, expected,
      `${pred} ${useFFI ? 'FFI' : 'clause'} provability = ${expected}`);
  }
}

before(() => {
  Store.clear();
  installRatlitTheory();
  ec = mde.load(RAT_ILL);
  const theories = [...defaultTheories, binlitTheory, ratlitTheory];
  canonicalize = buildCanonicalizer(theories);
  baseOpts = makeILLBackchainOpts({ theories, normalize: canonicalize });
});

describe('q-operations: clauses vs FFI', () => {
  it('qplus: rat×rat, reduction, den collapse', () => {
    agree('qplus', [putRat(1n, 2n), putRat(1n, 3n)], putRat(5n, 6n));
    agree('qplus', [putRat(1n, 6n), putRat(1n, 3n)], putRat(1n, 2n)); // reduction
    agree('qplus', [putRat(1n, 2n), putRat(1n, 2n)], bin(1n));        // den collapse
  });

  it('qplus: bins coerce (both argument orders, zero included)', () => {
    agree('qplus', [bin(3n), putRat(1n, 2n)], putRat(7n, 2n));
    agree('qplus', [putRat(1n, 2n), bin(3n)], putRat(7n, 2n));
    agree('qplus', [bin(0n), putRat(1n, 2n)], putRat(1n, 2n));
    agree('qplus', [bin(3n), bin(4n)], bin(7n)); // pure integers work too
  });

  it('qsub: exact, checked (fails on negative)', () => {
    agree('qsub', [putRat(1n, 2n), putRat(1n, 3n)], putRat(1n, 6n));
    agree('qsub', [bin(2n), putRat(1n, 2n)], putRat(3n, 2n));
    agree('qsub', [putRat(1n, 2n), putRat(1n, 2n)], bin(0n));
    const goal = Store.put('qsub', [putRat(1n, 3n), putRat(1n, 2n), mv('R')]);
    for (const useFFI of [true, false]) {
      assert.ok(!prove(goal, useFFI).success, `qsub negative fails (useFFI=${useFFI})`);
    }
  });

  it('qmul: rat×rat and coerced', () => {
    agree('qmul', [putRat(2n, 3n), putRat(3n, 4n)], putRat(1n, 2n));
    agree('qmul', [bin(4n), putRat(3n, 4n)], bin(3n));
    agree('qmul', [putRat(3n, 4n), bin(4n)], bin(3n));
    agree('qmul', [putRat(1n, 2n), bin(0n)], bin(0n));
  });

  it('qdiv: exact field division', () => {
    agree('qdiv', [putRat(1n, 2n), bin(3n)], putRat(1n, 6n));
    agree('qdiv', [bin(3n), putRat(1n, 2n)], bin(6n));
    agree('qdiv', [putRat(3n, 2n), putRat(3n, 4n)], bin(2n));
    agree('qdiv', [bin(7n), bin(2n)], putRat(7n, 2n)); // exact, unlike Euclidean div
  });

  it('qdiv by zero fails on both paths', () => {
    const goal = Store.put('qdiv', [putRat(1n, 2n), bin(0n), mv('R')]);
    for (const useFFI of [true, false]) {
      assert.ok(!prove(goal, useFFI).success, `qdiv/0 fails (useFFI=${useFFI})`);
    }
  });

  it('qlt/qle by value, across representations', () => {
    agreeBool('qlt', [putRat(1n, 3n), putRat(1n, 2n)], true);
    agreeBool('qlt', [putRat(1n, 2n), putRat(1n, 3n)], false);
    agreeBool('qlt', [putRat(1n, 3n), bin(1n)], true);
    agreeBool('qlt', [bin(1n), putRat(1n, 3n)], false);
    agreeBool('qle', [putRat(1n, 2n), putRat(1n, 2n)], true);
    agreeBool('qle', [bin(0n), putRat(1n, 2n)], true);
  });

  it('qeq/qneq/qeq_bool', () => {
    agreeBool('qeq', [putRat(2n, 4n), putRat(1n, 2n)], true);
    agreeBool('qeq', [putRat(1n, 2n), putRat(1n, 3n)], false);
    agreeBool('qeq', [bin(3n), bin(3n)], true);
    agreeBool('qneq', [putRat(1n, 2n), putRat(1n, 3n)], true);
    agreeBool('qneq', [putRat(1n, 2n), putRat(2n, 4n)], false);
    agreeBool('qneq', [bin(1n), putRat(1n, 2n)], true);
    agree('qeq_bool', [putRat(1n, 2n), putRat(1n, 3n)], bin(0n));
    agree('qeq_bool', [putRat(1n, 2n), putRat(2n, 4n)], bin(1n));
  });
});

describe('split-namespace contract', () => {
  it('bin predicates on rational arguments fail on both paths', () => {
    for (const [pred, args] of [
      ['plus', [putRat(1n, 2n), putRat(1n, 3n), mv('R')]],
      ['sub',  [putRat(1n, 2n), putRat(1n, 3n), mv('R')]],
      ['lt',   [putRat(1n, 3n), putRat(1n, 2n)]],
      ['le',   [putRat(1n, 3n), putRat(1n, 2n)]],
      ['neq',  [putRat(1n, 2n), putRat(1n, 3n)]],
    ]) {
      const goal = Store.put(pred, args);
      for (const useFFI of [true, false]) {
        assert.ok(!prove(goal, useFFI).success,
          `${pred} on rats is out of contract (useFFI=${useFFI})`);
      }
    }
  });

  it('bin×bin behavior is untouched', () => {
    agree('plus', [bin(3n), bin(4n)], bin(7n));
    agree('div', [bin(7n), bin(2n)], bin(3n)); // Euclidean
    agreeBool('lt', [bin(1n), bin(2n)], true);
  });

  it('negative numerators fail on BOTH paths (ℚ≥0 contract, audit round 11)', () => {
    const neg = putRat(-1n, 2n);
    const goal = Store.put('qplus', [neg, bin(1n), mv('R')]);
    for (const useFFI of [true, false]) {
      assert.ok(!prove(goal, useFFI).success,
        `qplus on a negative numerator refuses (useFFI=${useFFI})`);
    }
  });

  it('eq on canonical rationals holds by pure canonicity (eq/z, not an overload)', () => {
    // putRat gives equal rationals equal hashes, so eq X X covers them with
    // zero rational clauses — FFI fails advisorily and clause resolution
    // answers on both paths.
    agreeBool('eq', [putRat(2n, 4n), putRat(1n, 2n)], true);
    agreeBool('eq', [putRat(1n, 2n), putRat(1n, 3n)], false);
  });
});
