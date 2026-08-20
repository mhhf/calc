/**
 * Unification property fuzzer (TODO_0272 M7).
 *
 * The apply() fuzzer (kernel-apply-fuzz.test.js) pins substitution against a
 * frozen reference; nothing checked that `unify` returns a SOUND unifier. This
 * fuzzer generates random term pairs over a shared metavar vocabulary and
 * asserts the defining properties of a most-general unifier θ = unify(a, b):
 *
 *   • soundness:   applyFix(a, θ) === applyFix(b, θ)   (θ makes the sides equal)
 *   • idempotence: apply(applyFix(t, θ), θ) === applyFix(t, θ)  (closure fixed)
 *   • symmetry:    unify(a, b) succeeds ⟺ unify(b, a) succeeds
 *   • reflexivity: unify(t, t) succeeds and fixes t    (apply(t, θ) === t)
 *
 * `unify` returns a union-find θ whose bindings are the class roots — raw
 * terms that may still mention other unified metavars, so the substitution is
 * NOT idempotent when BOTH sides are open (in engine use one side is a ground
 * fact, which makes it idempotent). The unifier property is therefore stated
 * over the substitution CLOSURE `applyFix` (apply to a fixed point), the
 * mathematically correct notion of "θ unifies a and b". The occurs check
 * guarantees `applyFix` terminates.
 *
 * Terms are drawn from atoms / freevars / metavars / tensor·loli·with·oplus /
 * arrlit — deliberately NO binlit/ratlit, so no cross-tag equational rewriting
 * muddies strict hash equality (that path has its own fuzzer, fuzz-ffi).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import calculus from '../lib/calculus/index.js';
import Store from '../lib/kernel/store.js';
import { apply } from '../lib/kernel/substitute.js';
import { unify } from '../lib/kernel/unify.js';

// Apply θ to a fixed point (substitution closure). Terminates because the
// occurs check forbids cyclic bindings.
function applyFix(h, theta) {
  let prev = h, cur = apply(h, theta);
  let guard = 0;
  while (cur !== prev) {
    if (++guard > 64) throw new Error('applyFix did not converge — cyclic θ?');
    prev = cur; cur = apply(cur, theta);
  }
  return cur;
}

function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const pick = (r, arr) => arr[Math.floor(r() * arr.length)];

function makeVocab(AST) {
  return {
    atoms: ['p', 'q', 'r', 's', 'stop', 'revert'].map(n => AST.atom(n)),
    freevars: ['X', 'Y', 'Z'].map(n => AST.freevar(n)),
    metavars: ['m0', 'm1', 'm2', 'm3', 'm4'].map(n => AST.metavar(n)),
  };
}

function genTerm(r, vocab, AST, depth) {
  if (depth <= 0) {
    const bag = r() < 0.4 ? vocab.metavars : (r() < 0.5 ? vocab.atoms : vocab.freevars);
    return pick(r, bag);
  }
  const k = r();
  if (k < 0.12) {
    const n = 2 + Math.floor(r() * 3);
    const elems = new Uint32Array(n);
    for (let i = 0; i < n; i++) elems[i] = genTerm(r, vocab, AST, depth - 1);
    return Store.putArray(elems);
  }
  if (k < 0.35) return AST.tensor(genTerm(r, vocab, AST, depth - 1), genTerm(r, vocab, AST, depth - 1));
  if (k < 0.55) return AST.loli(genTerm(r, vocab, AST, depth - 1), genTerm(r, vocab, AST, depth - 1));
  if (k < 0.72) return AST.with(genTerm(r, vocab, AST, depth - 1), genTerm(r, vocab, AST, depth - 1));
  if (k < 0.88) return AST.oplus(genTerm(r, vocab, AST, depth - 1), genTerm(r, vocab, AST, depth - 1));
  return pick(r, r() < 0.5 ? vocab.atoms : vocab.metavars);
}

describe('TODO_0272 M7 — unification property fuzzer', { concurrency: 1 }, () => {
  let AST, vocab;
  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
    vocab = makeVocab(AST);
  });

  it('sound + idempotent unifier over 5000 random pairs', () => {
    const r = rng(0x5EED01);
    let unified = 0, failed = 0;
    for (let i = 0; i < 5000; i++) {
      const a = genTerm(r, vocab, AST, 2 + Math.floor(r() * 3));
      const b = genTerm(r, vocab, AST, 2 + Math.floor(r() * 3));
      const theta = unify(a, b);
      if (theta === null) { failed++; continue; }
      unified++;
      const ea = applyFix(a, theta);
      const eb = applyFix(b, theta);
      assert.strictEqual(ea, eb,
        `unifier not sound: applyFix(a,θ) !== applyFix(b,θ) for pair #${i}`);
      // The closure is a fixed point: one more apply is a no-op.
      assert.strictEqual(apply(ea, theta), ea,
        `θ-closure not a fixed point for pair #${i}`);
    }
    // Sanity: the generator produces a healthy mix of both outcomes.
    assert.ok(unified > 200, `too few unifiable pairs (${unified}) — generator skew`);
    assert.ok(failed > 200, `too few non-unifiable pairs (${failed}) — generator skew`);
  });

  it('symmetry: unify(a,b) succeeds iff unify(b,a) succeeds (3000 pairs)', () => {
    const r = rng(0x5EED02);
    for (let i = 0; i < 3000; i++) {
      const a = genTerm(r, vocab, AST, 2 + Math.floor(r() * 3));
      const b = genTerm(r, vocab, AST, 2 + Math.floor(r() * 3));
      assert.strictEqual(unify(a, b) === null, unify(b, a) === null,
        `unification asymmetric for pair #${i}`);
    }
  });

  it('reflexivity: unify(t,t) fixes t (1000 terms)', () => {
    const r = rng(0x5EED03);
    for (let i = 0; i < 1000; i++) {
      const t = genTerm(r, vocab, AST, 2 + Math.floor(r() * 4));
      const theta = unify(t, t);
      assert.notStrictEqual(theta, null, `t did not unify with itself #${i}`);
      assert.strictEqual(apply(t, theta), t, `self-unify altered t #${i}`);
    }
  });
});
