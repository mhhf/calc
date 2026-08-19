/**
 * till sequent calculus — TODO_0265 Phase 6b Stage 1 (D2/D3).
 *
 * The graded fragment, no stamps. Backward provability over till.rules:
 *   - counted bang !_k A ≡ A ⊗ … ⊗ A (k copies): left peel/weaken,
 *     right peel/zero — grade side conditions via the D1 template DSL
 *   - ω bang: ILL's promotion/dereliction/absorption, template-matched so
 *     the ω grade in `!A` is a real constraint (never fires on !_k)
 *   - graded lax monad: gmonad_l = graded bind (H := F − E, monus),
 *     gmonad_r = unit at grade 0; the graded-μ {{A}@d}@e ⊢ {A}@(d+e)
 *     is DERIVABLE, and only with exact accounting (no subeffecting in v1
 *     — availability monotonicity is Stage 2 / THY territory)
 *
 * Every found derivation must pass the L1 kernel checker. The grade
 * algebra is the SAME record the timed scheduler reads (D13).
 * ILL bit-identicality is the rest of the suite (nothing here loads ILL).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import Store from '../lib/kernel/store.js';
import { putRat } from '../lib/kernel/rat-term.js';
import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import { ProofTree } from '../lib/prover/pt.js';
import { loadTillSequent, tillGrades } from '../calculus/till/calculus-config.js';

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
  });

  describe('ω bang: promotion / dereliction / absorption, ω-restricted', () => {
    provable('!a |- a', ['!a'], 'a');
    provable('!a |- !a', ['!a'], '!a');
    provable('!a |- a * a  (contraction via absorption)', ['!a'], 'a * a');
    provable('!a |- !_2 a  (ω covers any count)', ['!a'], '!_2 a');

    refuted('!_2 a |-/ !a  (counted never promotes)', ['!_2 a'], '!a');
    refuted('a |-/ !a', ['a'], '!a');
  });

  describe('graded lax monad: bind + unit, exact accounting', () => {
    provable('{{a}@2}@3 |- {a}@5  (graded-μ)', ['{{a}@2}@3'], '{a}@5');
    provable('a |- {a}  (unit)', ['a'], '{a}');
    provable('{a}@2 |- {a}@2  (identity)', ['{a}@2'], '{a}@2');
    provable('{a}@2, {b}@3 |- {a * b}@5  (binds compose)',
      ['{a}@2', '{b}@3'], '{a * b}@5');
    provable('{{a}@1/2}@1/2 |- {a}@1  (exact ℚ)', ['{{a}@1/2}@1/2'], '{a}@1');
    provable('!_2 a |- {a * a}  (bang under the monad)', ['!_2 a'], '{a * a}');
    provable('a -o {b}@2, a |- {b}@2', ['a -o {b}@2', 'a'], '{b}@2');

    refuted('{{a}@2}@3 |-/ {a}@4  (too early)', ['{{a}@2}@3'], '{a}@4');
    refuted('{{a}@2}@3 |-/ {a}@6  (no subeffecting)', ['{{a}@2}@3'], '{a}@6');
    refuted('a |-/ {a}@1  (unit is grade 0)', ['a'], '{a}@1');
    refuted('{a}@2 |-/ a  (no escape)', ['{a}@2'], 'a');
    refuted('{a}@2, {b}@3 |-/ {a * b}@4', ['{a}@2', '{b}@3'], '{a * b}@4');
  });

  describe('grade algebra is shared with the scheduler (D13)', () => {
    it('calc.grades IS tillGrades (one algebra, two faces)', () => {
      assert.strictEqual(calc.grades, tillGrades);
    });
    it('{a} ≡ {a}@0 (unit elision is definitional)', () => {
      assert.strictEqual(P('{a}'), P('{a}@0'));
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

    it('rejects gmonad_l with wrong grade arithmetic', () => {
      // claims {a}@2 |- {a}@4 from a |- {a}@1 — bind requires premise {a}@2
      const child = new ProofTree({
        conclusion: Seq.fromArrays([P('a')], [], P('{a}@1')),
        rule: 'id', proven: true, premises: [],
      });
      const bad = new ProofTree({
        conclusion: Seq.fromArrays([P('{a}@2')], [], P('{a}@4')),
        rule: 'gmonad_l', proven: true, premises: [child],
      });
      assert.ok(!kernel.verifyTree(bad).valid);
    });

    it('accepts the honest gmonad_l instance it just rejected the fake of', () => {
      const r = prove(['{a}@2'], '{a}@2');
      assert.ok(r.success);
      assert.ok(kernel.verifyTree(r.proofTree).valid);
    });
  });
});
