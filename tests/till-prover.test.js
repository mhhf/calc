/**
 * till sequent calculus — TODO_0265 Phase 6b Stage 1 (D2/D3).
 *
 * The graded fragment, no stamps. Backward provability over till.rules:
 *   - counted bang !_k A ≡ A ⊗ … ⊗ A (k copies): left peel/weaken,
 *     right peel/zero — grade side conditions via the D1 template DSL
 *   - ω bang: ILL's promotion/dereliction/absorption, template-matched so
 *     the ω grade in `!A` is a real constraint (never fires on !_k)
 *   - graded lax monad: monad_l = graded bind (H := F − E, monus),
 *     monad_r = unit at grade 0; the graded-μ {{A}@d}@e ⊢ {A}@(d+e)
 *     is DERIVABLE, and only with exact accounting (no subeffecting in v1
 *     — availability monotonicity is Stage 2 / THY territory)
 *
 * Every found derivation must pass the L1 kernel checker. The grade
 * algebra is the SAME record the timed scheduler reads (D13).
 * ILL bit-identicality is the rest of the suite (nothing here loads ILL).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../lib/kernel/store.js';
import calculus from '../lib/calculus/index.js';
import { putRat } from '../lib/kernel/rat-term.js';
import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import { ProofTree } from '../lib/prover/pt.js';
import { loadTillSequent, tillTheory } from '../calculus/till/calculus-config.js';

describe('till sequent calculus (graded fragment, Stage 1)', () => {
  let calc, specs, alternatives, prover, kernel, P;

  before(() => {
    calc = loadTillSequent();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc);
    kernel = createKernel(calc);
    P = (s) => calc.parse(s);
  });

  // linear-only sequents; atoms are lowercase (rigid) — uppercase would be
  // metavars under the till parser and unify with anything
  const prove = (linear, succ) =>
    prover.prove(Seq.fromArrays(linear.map(P), [], P(succ)), { rules: specs, alternatives });

  const provable = (desc, linear, succ) => it(desc, () => {
    const r = prove(linear, succ);
    assert.ok(r.success, `expected provable: ${desc}`);
    const v = kernel.verifyTree(r.proofTree);
    assert.ok(v.valid, `kernel rejected ${desc}: ${v.errors.join('; ')}`);
    // pure sequent proofs (no bridge) must be FULLY verified — no
    // unverified steps (round-15 F1)
    assert.equal(v.unverified, undefined, `unverified steps in ${desc}`);
  });
  const refuted = (desc, linear, succ) => it(desc, () => {
    assert.ok(!prove(linear, succ).success, `expected refuted: ${desc}`);
  });

  describe('counted bang: !_k a ≡ a ⊗ … ⊗ a', () => {
    provable('!_5 a |- !_2 a * !_3 a  (split)', ['!_5 a'], '!_2 a * !_3 a');
    provable('!_2 a, !_3 a |- !_5 a  (merge)', ['!_2 a', '!_3 a'], '!_5 a');
    provable('!_3 a |- a * !_2 a  (dereliction)', ['!_3 a'], 'a * !_2 a');
    provable('!_2 a |- a * a', ['!_2 a'], 'a * a');
    provable('a, a |- !_2 a', ['a', 'a'], '!_2 a');
    provable('!_1 a |- a', ['!_1 a'], 'a');
    provable('a |- !_1 a', ['a'], '!_1 a');
    it('|- !_(count 0) a from nothing; surface !_0 is the g0 LABEL, not count zero', () => {
      // count zero (binlit 0) only arises internally, from peeling — the
      // surface literal `!_0` is SELL's compile-time grade label g0, which
      // has NO Stage-1 sequent rules (composed away before runtime).
      const count0 = Store.put('bang', [putRat(0n, 1n), P('a')]);
      const r = prover.prove(Seq.fromArrays([], [], count0), { rules: specs, alternatives });
      assert.ok(r.success, 'count zero provable from nothing');
      assert.ok(kernel.verifyTree(r.proofTree).valid);
      assert.ok(!prove([], '!_0 a').success, 'g0 label has no rules');
    });
    provable('!_5 a |- !_5 a  (identity)', ['!_5 a'], '!_5 a');
    provable('a -o b, !_1 a |- b', ['a -o b', '!_1 a'], 'b');
    provable('!_2 a |- (a * a) & (a * a)', ['!_2 a'], '(a * a) & (a * a)');

    refuted('!_2 a |-/ !_3 a  (cannot forge)', ['!_2 a'], '!_3 a');
    refuted('!_2 a |-/ a * !_2 a', ['!_2 a'], 'a * !_2 a');
    refuted('!_3 a |-/ !_2 a  (no weakening)', ['!_3 a'], '!_2 a');
    refuted('|-/ !_1 a', [], '!_1 a');
    refuted('!_5 a |-/ !_2 a * !_2 a  (leftover)', ['!_5 a'], '!_2 a * !_2 a');
    refuted('!_2 b |-/ !_2 a  (wrong atom)', ['!_2 b'], '!_2 a');
    refuted('!_2 a |-/ (a * a) & a  (with-branches must consume equally)',
      ['!_2 a'], '(a * a) & a');
  });

  describe('ω bang: promotion / dereliction / absorption, ω-restricted', () => {
    provable('!a |- a', ['!a'], 'a');
    provable('!a |- !a', ['!a'], '!a');
    provable('!a |- a * a  (contraction via absorption)', ['!a'], 'a * a');
    provable('!a |- !_2 a  (ω covers any count)', ['!a'], '!_2 a');

    refuted('!_2 a |-/ !a  (counted never promotes)', ['!_2 a'], '!a');
    refuted('a |-/ !a', ['a'], '!a');
  });

  describe('graded lax monad: bind + unit·sub (THY_0018 §4 — the grade is a BOUND)', () => {
    provable('{{a}@2}@3 |- {a}@5  (graded-μ)', ['{{a}@2}@3'], '{a}@5');
    provable('a |- {a}  (unit)', ['a'], '{a}');
    provable('{a}@2 |- {a}@2  (identity)', ['{a}@2'], '{a}@2');
    provable('{a}@2, {b}@3 |- {a * b}@5  (binds compose)',
      ['{a}@2', '{b}@3'], '{a * b}@5');
    provable('{{a}@1/2}@1/2 |- {a}@1  (exact ℚ)', ['{{a}@1/2}@1/2'], '{a}@1');
    provable('!_2 a |- {a * a}  (bang under the monad)', ['!_2 a'], '{a * a}');
    provable('a -o {b}@2, a |- {b}@2', ['a -o {b}@2', 'a'], '{b}@2');
    // subeffecting: a bound may be weakened (Theorem 1: operational stamps
    // are the LEAST derivable grades — later bounds must stay derivable)
    provable('a |- {a}@1  (sub: within 0 ⇒ within 1)', ['a'], '{a}@1');
    provable('{{a}@2}@3 |- {a}@6  (sub above the critical path)',
      ['{{a}@2}@3'], '{a}@6');
    provable('{a}@2 |- {a}@7  (sub)', ['{a}@2'], '{a}@7');

    refuted('{{a}@2}@3 |-/ {a}@4  (below the critical path)', ['{{a}@2}@3'], '{a}@4');
    refuted('{a}@2 |-/ a  (no escape)', ['{a}@2'], 'a');
    refuted('{a}@2, {b}@3 |-/ {a * b}@4', ['{a}@2', '{b}@3'], '{a * b}@4');
    refuted('{a}@5 |-/ {a}@3  (no strengthening)', ['{a}@5'], '{a}@3');
  });

  describe('stamped atoms: retiming (THY_0018 §5 — availability monotonicity)', () => {
    provable('a@3 |- a@3  (stamped identity)', ['a@3'], 'a@3');
    provable('a@3 |- a@5  (retiming: delaying availability is free)', ['a@3'], 'a@5');
    provable('a@1, b@2 |- a@4 * b@4  (synchronise late)', ['a@1', 'b@2'], 'a@4 * b@4');
    provable('a@1 |- {a@6}@9  (retime under the monad)', ['a@1'], '{a@6}@9');

    refuted('a@5 |-/ a@3  (never early)', ['a@5'], 'a@3');
    refuted('a@3 |-/ b@5  (wrong atom)', ['a@3'], 'b@5');
    refuted('a |-/ a@3  (no ambient rule in v1: unstamped stays unstamped)', ['a'], 'a@3');
  });

  describe('grade semantics is shared with the forward engine (D13/TODO_0273)', () => {
    it('calc.theory IS tillTheory (one numeric theory, both directions)', () => {
      assert.strictEqual(calc.theory, tillTheory);
    });
    it('{a} ≡ {a}@0 (unit elision is definitional)', () => {
      assert.strictEqual(P('{a}'), P('{a}@0'));
    });
  });

  describe('tillTheory.prove contract (TODO_0274: reason taxonomy + output binding)', () => {
    // The gate at calculus-config: only reason === 'conversion_failed' is
    // ADVISORY (falls through to clause resolution); every other FFI
    // failure is DECISIVE. These pins catch a future handler that adds a
    // new advisory reason — which would otherwise silently cause
    // incompleteness. Under CALC_NOFFI=1 the same answers must come from
    // the clause face alone (FFI principle).
    it('le success returns the empty theta', () => {
      assert.deepStrictEqual(
        tillTheory.prove(Store.put('le', [putRat(2n, 1n), putRat(5n, 1n)])), []);
    });
    it('le false comparison is decisive: null', () => {
      assert.strictEqual(
        tillTheory.prove(Store.put('le', [putRat(5n, 1n), putRat(2n, 1n)])), null);
    });
    it('qsub binds its output var to the canonical residual', () => {
      const H = Store.put('metavar', ['TH_qsub']);
      const theta = tillTheory.prove(Store.put('qsub', [putRat(5n, 1n), putRat(2n, 1n), H]));
      assert.ok(theta, 'qsub 5 2 H derivable');
      const b = theta.find(([v]) => v === H);
      assert.ok(b, 'binding for H present');
      assert.strictEqual(b[1], putRat(3n, 1n));
    });
    it('qsub out of fence is underivable (negative residual refused)', () => {
      const H = Store.put('metavar', ['TH_qsub2']);
      assert.strictEqual(
        tillTheory.prove(Store.put('qsub', [putRat(2n, 1n), putRat(5n, 1n), H])), null);
    });
    it('non-numeric grade: conversion_failed → clause fallback → null', () => {
      assert.strictEqual(
        tillTheory.prove(Store.put('le', [Store.put('atom', ['gw']), putRat(5n, 1n)])), null);
    });
    it('has(): typo fence — unknown predicates rejected, real ones known', () => {
      assert.ok(!tillTheory.has('qsib'));
      for (const p of ['qsub', 'le', 'eq', 'plus']) assert.ok(tillTheory.has(p), p);
    });
    it('a typo’d theory premise fails the calculus load loudly', () => {
      // the real loader path: a rules file with `<- !qsib F E H` (typo for
      // qsub) must be rejected at load — silent never-applicable rules are
      // the failure mode the closed-world checker exists to kill
      const src = '@formulas A, B, C\n\n' +
        'bad: G ; D, {A}@E |- {C}@F\n' +
        '  <- G ; D, A |- {C}@H\n' +
        '  <- !qsib F E H\n' +
        '  @side l.\n';
      const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-typo-'));
      const file = path.join(dir, 'typo.rules');
      fs.writeFileSync(file, src);
      try {
        assert.throws(
          () => calculus.load(
            path.join(import.meta.dirname, '../calculus/till/till.calc'), file, {
              parser: { multiCharFreevars: true, numbers: true },
              theory: tillTheory,
            }),
          /unknown theory predicate 'qsib'/);
      } finally {
        fs.rmSync(dir, { recursive: true, force: true });
      }
    });
  });

  describe('kernel guards template rules (soundness of verification)', () => {
    it('rejects bang_r3 claiming |- !_5 a with zero premises', () => {
      const bad = new ProofTree({
        conclusion: Seq.fromArrays([], [], P('!_5 a')),
        rule: 'bang_r3', proven: true, premises: [],
      });
      assert.ok(!kernel.verifyTree(bad).valid);
    });

    it('rejects monad_l with wrong grade arithmetic', () => {
      // claims {a}@2 |- {a}@4 from a |- {a}@1 — bind requires premise {a}@2
      const child = new ProofTree({
        conclusion: Seq.fromArrays([P('a')], [], P('{a}@1')),
        rule: 'id', proven: true, premises: [],
      });
      const bad = new ProofTree({
        conclusion: Seq.fromArrays([P('{a}@2')], [], P('{a}@4')),
        rule: 'monad_l', proven: true, premises: [child],
      });
      assert.ok(!kernel.verifyTree(bad).valid);
    });

    it('accepts the honest monad_l instance it just rejected the fake of', () => {
      const r = prove(['{a}@2'], '{a}@2');
      assert.ok(r.success);
      assert.ok(kernel.verifyTree(r.proofTree).valid);
    });

    // Round-15 F1: the kernel threads the linear resource discipline —
    // shape-valid steps that leak context are rejected at the root.
    it('rejects a forged at_l with unconsumed context: a@1, b |- a@2', () => {
      const bad = new ProofTree({
        conclusion: Seq.fromArrays([P('a@1'), P('b')], [], P('a@2')),
        rule: 'at_l', proven: true, premises: [],
      });
      const v = kernel.verifyTree(bad);
      assert.ok(!v.valid);
      assert.ok(v.errors.some(e => /unconsumed/.test(e)), v.errors.join('; '));
    });

    it('rejects a forged id with unconsumed context: a, b |- a', () => {
      const bad = new ProofTree({
        conclusion: Seq.fromArrays([P('a'), P('b')], [], P('a')),
        rule: 'id', proven: true, premises: [],
      });
      assert.ok(!kernel.verifyTree(bad).valid);
    });

    it('rejects a forged monad_l whose premise skips the compound groundness fence', () => {
      // sanity companion to the wrong-arithmetic forgery above: same shape,
      // grade far off — the theory premise `!qsub F E H` must recompute
      const child = new ProofTree({
        conclusion: Seq.fromArrays([P('a')], [], P('{a}@9')),
        rule: 'id', proven: true, premises: [],
      });
      const bad = new ProofTree({
        conclusion: Seq.fromArrays([P('{a}@2')], [], P('{a}@4')),
        rule: 'monad_l', proven: true, premises: [child],
      });
      assert.ok(!kernel.verifyTree(bad).valid);
    });

    it('flags a forged monad_r2 bridge node as unverified, never as proven', () => {
      // the kernel cannot re-run settle: a zero-premise modeShift node
      // passes shape checks but MUST carry the modeSwitch flag — callers
      // claiming full verification assert `valid && !unverified`
      const bad = new ProofTree({
        conclusion: Seq.fromArrays([P('b')], [], P('{a}@5')),
        rule: 'monad_r2', proven: true, premises: [],
      });
      const v = kernel.verifyTree(bad);
      assert.ok(v.valid);
      assert.deepEqual(v.unverified, ['modeSwitch']);
    });
  });
});
