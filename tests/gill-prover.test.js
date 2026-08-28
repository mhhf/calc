/**
 * gill sequent calculus — the graded transport comonad (TODO_0284 P3).
 *
 * Backward provability over gill.rules' haul fragment: !!_d A =
 * "A reachable within haul-cost d", the spatial dual of the delay monad.
 *   haul_r — unit·sub: what is here is reachable within any budget
 *   haul_l — fetch (bind dual): the SAME ⊖ residual premise as monad_l
 *   haul_l2 — cost-0 dereliction: reachable at 0 = possessed
 * Subsumption (!!_E A |- !!_F A, F ≥ E) and the graded-μ
 * (!!_E (!!_F A) |- !!_G A, G ≥ E+F) are DERIVABLE, and cost fences hold
 * with no side conditions (qsub is checked — Grade Preservation).
 * Every found derivation must pass the L1 kernel checker.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import { loadGillSequent, gillTheory } from '../calculus/gill/calculus-config.js';

describe('gill sequent calculus — haul (graded transport comonad)', () => {
  let calc, specs, alternatives, prover, kernel, P;

  before(() => {
    calc = loadGillSequent();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc);
    kernel = createKernel(calc);
    P = (s) => calc.parse(s);
  });

  const prove = (linear, succ) =>
    prover.prove(Seq.fromArrays(linear.map(P), [], P(succ)), { rules: specs, alternatives });

  const provable = (desc, linear, succ) => it(desc, () => {
    const r = prove(linear, succ);
    assert.ok(r.success, `expected provable: ${desc}`);
    const v = kernel.verifyTree(r.proofTree);
    assert.ok(v.valid, `kernel rejected ${desc}: ${v.errors.join('; ')}`);
    assert.equal(v.unverified, undefined, `unverified steps in ${desc}`);
  });
  const refuted = (desc, linear, succ) => it(desc, () => {
    assert.ok(!prove(linear, succ).success, `expected refuted: ${desc}`);
  });

  describe('unit·sub (haul_r): here ⟹ reachable within any budget', () => {
    provable('a |- !!_0 a', ['a'], '!!_0 a');
    provable('a |- !!_5 a', ['a'], '!!_5 a');
    provable('a |- !!_(1/2) a  (fractional cost)', ['a'], '!!_(1/2) a');
    refuted('|- !!_3 a from nothing', [], '!!_3 a');
    refuted('b |- !!_3 a  (wrong atom)', ['b'], '!!_3 a');
  });

  describe('cost-0 dereliction (haul_l2): the fence is exact', () => {
    provable('!!_0 a |- a', ['!!_0 a'], 'a');
    refuted('!!_1 a |- a  (distance is not possession)', ['!!_1 a'], 'a');
    refuted('!!_(1/2) a |- a', ['!!_(1/2) a'], 'a');
  });

  describe('subsumption (derivable: haul_l + haul_r)', () => {
    provable('!!_2 a |- !!_5 a', ['!!_2 a'], '!!_5 a');
    provable('!!_2 a |- !!_2 a  (reflexive)', ['!!_2 a'], '!!_2 a');
    provable('!!_(1/2) a |- !!_(3/2) a', ['!!_(1/2) a'], '!!_(3/2) a');
    refuted('!!_5 a |- !!_2 a  (cost cannot shrink)', ['!!_5 a'], '!!_2 a');
  });

  describe('graded-μ (derivable): nested transport composes additively', () => {
    provable('!!_2 (!!_3 a) |- !!_5 a', ['!!_2 (!!_3 a)'], '!!_5 a');
    provable('!!_2 (!!_3 a) |- !!_7 a  (then subsume)', ['!!_2 (!!_3 a)'], '!!_7 a');
    refuted('!!_2 (!!_3 a) |- !!_4 a  (under the sum)', ['!!_2 (!!_3 a)'], '!!_4 a');
  });

  describe('fetch (haul_l): costs add across independent fetches', () => {
    provable('!!_2 a, !!_3 b |- !!_5 (a * b)', ['!!_2 a', '!!_3 b'], '!!_5 (a * b)');
    refuted('!!_2 a, !!_3 b |- !!_4 (a * b)', ['!!_2 a', '!!_3 b'], '!!_4 (a * b)');
  });

  it('theory face: min/max premises remain available to gill rules', () => {
    // (the P2 collapse — haul shares one theory engine with min/max)
    assert.ok(gillTheory.has('min') && gillTheory.has('qsub'));
  });
});
