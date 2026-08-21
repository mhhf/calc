/**
 * Work adequacy of the PURE graded fragment — THY_0023 §7 (TODO_0270 ob. 4).
 *
 * Non-circular adequacy: programs encoded as rule HYPOTHESES (linear lolis /
 * counted bangs in Δ), proved pure-backward — no bridge, no engineCalc, no
 * settle in the proof path. Every provable case must pass FULL kernel
 * verification (valid && !unverified).
 *
 * Theorem 10: Δ_ε ⊢ {⊗R}@W derivable ⟺ an execution with W ≥ TOTAL WORK
 *   (Σ of fired delays) reaches R.
 * Theorem 11 (separation): the pure grade measures WORK (Σ), settle measures
 *   MAKESPAN (max-plus). Join program: least pure W = 6 = 2+3+1, settle
 *   stamp = 4 = max(2,3)+1 — cross-checked against tools/till-oracle.mjs,
 *   the reference semantics (NOT used by the prover).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import { loadTillSequent } from '../calculus/till/calculus-config.js';
import { makeState, settle, rstr } from '../tools/till-oracle.mjs';

describe('pure work adequacy (THY_0023 §7 — rules as hypotheses, no bridge)', () => {
  let calc, specs, alternatives, prover, kernel, P;

  before(() => {
    calc = loadTillSequent();
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
    // non-circularity: pure derivations only — no bridge/modeSwitch steps
    assert.equal(v.unverified, undefined, `unverified steps in ${desc}`);
  });
  const refuted = (desc, linear, succ) => it(desc, () => {
    assert.ok(!prove(linear, succ).success, `expected refuted: ${desc}`);
  });

  // ── chain program: a ⊸ {b}@2, b ⊸ {c}@3 — work = makespan = 5 ──
  const chain = ['a', 'a -o {b}@2', 'b -o {c}@3'];

  describe('chain: work = makespan (Σ degenerates to critical path)', () => {
    provable('a, rules ⊢ {c}@5  (= work)', chain, '{c}@5');
    provable('a, rules ⊢ {c}@6  (sub above work)', chain, '{c}@6');
    refuted('a, rules ⊬ {c}@4  (below work)', chain, '{c}@4');
    refuted('a, rules ⊬ {c}@0', chain, '{c}@0');
  });

  // ── join program: a ⊸ {x}@2, b ⊸ {y}@3, x⊗y ⊸ {c}@1 ──
  //    pure work = 2+3+1 = 6;  settle makespan = max(2,3)+1 = 4
  const join = ['a', 'b', 'a -o {x}@2', 'b -o {y}@3', 'x * y -o {c}@1'];

  describe('join: the work/makespan separation (Theorem 11)', () => {
    provable('a, b, rules ⊢ {c}@6  (= total work)', join, '{c}@6');
    provable('a, b, rules ⊢ {c}@7  (sub)', join, '{c}@7');
    refuted('a, b, rules ⊬ {c}@5  (below work, above makespan)', join, '{c}@5');
    refuted('a, b, rules ⊬ {c}@4  (= makespan — pure calculus does NOT schedule)', join, '{c}@4');

    it('settle (reference oracle) produces c@4 from the same program — the other column', () => {
      const st = makeState([['a', 0], ['b', 0]]);
      const rules = [
        { name: 'ra', inputs: [{ atom: 'a' }], delay: 2, outputs: [['x']] },
        { name: 'rb', inputs: [{ atom: 'b' }], delay: 3, outputs: [['y']] },
        { name: 'rc', inputs: [{ atom: 'x' }, { atom: 'y' }], delay: 1, outputs: [['c']] },
      ];
      const { state } = settle(st, 10, { rules });
      const c = [...state.values()].find((f) => f.atom === 'c');
      assert.ok(c, 'settle produced c');
      assert.equal(rstr(c.stamp), '4', 'makespan = max(2,3)+1 = 4');
    });
  });

  describe('residual accounting (leftovers must be claimed)', () => {
    provable('a, d, chain-rules ⊢ {c * d}@5  (leftover in the goal tensor)',
      ['a', 'd', 'a -o {b}@2', 'b -o {c}@3'], '{c * d}@5');
    refuted('a, d, chain-rules ⊬ {c}@5  (leftover unclaimed — linearity)',
      ['a', 'd', 'a -o {b}@2', 'b -o {c}@3'], '{c}@5');
    provable('partial execution: unfired rule claimed back in the goal',
      ['a', 'a -o {b}@2', 'b -o {c}@3'], '{b * (b -o {c}@3)}@2');
  });

  describe('counted-bang rule multiplicity (Δ_ε encoding)', () => {
    provable('!_2 (a ⊸ {b}@2), a, a ⊢ {b * b}@4  (two firings, work 4)',
      ['!_2 (a -o {b}@2)', 'a', 'a'], '{b * b}@4');
    refuted('!_2 (a ⊸ {b}@2), a, a ⊬ {b * b}@3  (below work)',
      ['!_2 (a -o {b}@2)', 'a', 'a'], '{b * b}@3');
    provable('!_1 (a ⊸ {b}@2), a ⊢ {b}@2', ['!_1 (a -o {b}@2)', 'a'], '{b}@2');
  });

  describe('the boundary: stamps are outside the pure encoding', () => {
    // no rule derives `a` from `a@t` (stamps born at the boundary, THY_0018
    // §5) — the encoding cannot consume stamped inputs; max-plus enters only
    // through @fire/the bridge.
    refuted('a@1, (a ⊸ {b}@2) ⊬ {b}@W for any W', ['a@1', 'a -o {b}@2'], '{b}@9');
    provable('untimed CLF base case: a, (a ⊸ {b}@0) ⊢ {b}@0', ['a', 'a -o {b}@0'], '{b}@0');
  });
});
