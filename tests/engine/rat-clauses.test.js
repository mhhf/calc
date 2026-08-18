/**
 * Rational clause resolution vs FFI — TODO_0265 Phase 1 (FFI principle).
 *
 * FFI is optimization, theory is semantics: with FFI off, the rat(N,D)
 * clauses in calculus/till/prelude/rat.ill must derive exactly what the
 * rational FFI computes, hash-for-hash after canonicalization. This is the
 * per-case counterpart of the fuzz walker's rat variants.
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

describe('rat clauses vs FFI — arithmetic', () => {
  it('plus: rat×rat', () => {
    agree('plus', [putRat(1n, 2n), putRat(1n, 3n)], putRat(5n, 6n));
    agree('plus', [putRat(1n, 6n), putRat(1n, 3n)], putRat(1n, 2n)); // reduction
    agree('plus', [putRat(1n, 2n), putRat(1n, 2n)], bin(1n));        // den collapse
  });

  it('plus: mixed bin/rat (both argument orders)', () => {
    agree('plus', [bin(3n), putRat(1n, 2n)], putRat(7n, 2n));
    agree('plus', [putRat(1n, 2n), bin(3n)], putRat(7n, 2n));
    agree('plus', [bin(0n), putRat(1n, 2n)], putRat(1n, 2n)); // e-headed dispatch
  });

  it('qsub: exact, checked (fails on negative), bins coerce', () => {
    agree('qsub', [putRat(1n, 2n), putRat(1n, 3n)], putRat(1n, 6n));
    agree('qsub', [bin(2n), putRat(1n, 2n)], putRat(3n, 2n));
    agree('qsub', [putRat(1n, 2n), putRat(1n, 2n)], bin(0n));
    const goal = Store.put('qsub', [putRat(1n, 3n), putRat(1n, 2n), mv('R')]);
    for (const useFFI of [true, false]) {
      assert.ok(!prove(goal, useFFI).success, `qsub negative fails (useFFI=${useFFI})`);
    }
  });

  it('mul: rat×rat and mixed (both derivation families agree canonically)', () => {
    agree('mul', [putRat(2n, 3n), putRat(3n, 4n)], putRat(1n, 2n));
    agree('mul', [bin(4n), putRat(3n, 4n)], bin(3n));
    agree('mul', [putRat(3n, 4n), bin(4n)], bin(3n));
    agree('mul', [putRat(1n, 2n), bin(0n)], bin(0n));
  });

  it('qdiv: exact (field) division; div stays bin-only Euclidean', () => {
    agree('qdiv', [putRat(1n, 2n), bin(3n)], putRat(1n, 6n));
    agree('qdiv', [bin(3n), putRat(1n, 2n)], bin(6n));
    agree('qdiv', [putRat(3n, 2n), putRat(3n, 4n)], bin(2n));
    agree('qdiv', [bin(7n), bin(2n)], putRat(7n, 2n)); // exact, unlike div
    agree('div', [bin(7n), bin(2n)], bin(3n));         // bin div untouched
  });

  it('qdiv by zero fails on both paths', () => {
    const goal = Store.put('qdiv', [putRat(1n, 2n), bin(0n), mv('R')]);
    for (const useFFI of [true, false]) {
      assert.ok(!prove(goal, useFFI).success, `qdiv/0 fails (useFFI=${useFFI})`);
    }
  });
});

describe('rat clauses vs FFI — comparisons', () => {
  it('lt/le by value, across representations', () => {
    agreeBool('lt', [putRat(1n, 3n), putRat(1n, 2n)], true);
    agreeBool('lt', [putRat(1n, 2n), putRat(1n, 3n)], false);
    agreeBool('lt', [putRat(1n, 3n), bin(1n)], true);
    agreeBool('lt', [bin(1n), putRat(1n, 3n)], false);
    agreeBool('le', [putRat(1n, 2n), putRat(1n, 2n)], true);
    agreeBool('le', [bin(0n), putRat(1n, 2n)], true);
  });

  it('eq needs no overload: canonical forms make it structural', () => {
    agreeBool('eq', [putRat(2n, 4n), putRat(1n, 2n)], true);
    agreeBool('eq', [putRat(1n, 2n), putRat(1n, 3n)], false);
  });

  it('neq and eq_bool', () => {
    agreeBool('neq', [putRat(1n, 2n), putRat(1n, 3n)], true);
    agreeBool('neq', [putRat(1n, 2n), putRat(2n, 4n)], false);
    agreeBool('neq', [bin(1n), putRat(1n, 2n)], true);
    agree('eq_bool', [putRat(1n, 2n), putRat(1n, 3n)], bin(0n));
    agree('eq_bool', [putRat(1n, 2n), putRat(2n, 4n)], bin(1n));
  });
});
