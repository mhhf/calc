/**
 * Cut-admissibility across the calculus family (THY_0044 §4; the metatheorem's
 * operational witness). The generic `cut` rule (kernel + focused.js) is shared
 * verbatim by ill/fill/gill/grill — "one engine, calculi as specs". This pins,
 * per instance, that cut is ADMISSIBLE: for a cut template, both premises
 * `Γ ⊢ A` and `A, Δ ⊢ C` are cut-free provable AND the composed `Γ, Δ ⊢ C` is
 * cut-free provable and kernel-valid — so cut adds no theorems.
 *
 * The deep cases are FIXPOINTS (cyclic cut-elimination is known-hard:
 * Fortier–Santocanale; Baelde–Doumane–Saurin) and the grade × fixpoint
 * composition — coind-cut, ind-cut, graded-haul, graded-coind-cut go through the
 * same generic cut. This is the deterministic battery; tools/fuzz-cut.js is the
 * randomized sweep (test:heavy). It is EVIDENCE for the parametric
 * cut-elimination target, not the display-calculus metatheorem itself (deferred).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createProver } from '../../lib/prover/focused.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { TEMPLATES, loadCalc } from '../../tools/fuzz-cut.js';

const CALCI = ['ill', 'fill', 'gill', 'grill', 'trill', 'dill'];

for (const cname of CALCI) {
  describe(`cut-admissibility — ${cname}`, () => {
    let calc, fp, specs, alternatives, prover, kernel;
    before(async () => {
      ({ calc, fp } = await loadCalc(cname));
      ({ specs, alternatives } = buildRuleSpecs(calc));
      prover = createProver(calc); kernel = createKernel(calc);
    });
    const prove = (sq, cyclic) => prover.prove(
      Seq.fromArrays(sq.lin.map(fp), sq.cart.map(fp), fp(sq.succ)),
      { rules: specs, alternatives, maxDepth: 300, cyclicProofs: cyclic, exhaustive: true });

    const applicable = () => TEMPLATES.filter(t => t.calc.includes(cname));

    it(`every applicable cut template: Γ⊢A and A,Δ⊢C provable ⇒ Γ,Δ⊢C cut-free provable + kernel-valid`, () => {
      const [p, q] = ['a', 'b'];
      let exercised = 0;
      for (const tpl of applicable()) {
        const L = tpl.L(p, q), R = tpl.R(p, q), Cut = tpl.Cut(p, q);
        const lr = prove(L, tpl.cyclic), rr = prove(R, tpl.cyclic);
        assert.equal(lr.success, true, `${tpl.tag}: left premise Γ⊢A must be cut-free provable`);
        assert.equal(rr.success, true, `${tpl.tag}: right premise A,Δ⊢C must be cut-free provable`);
        const cr = prove(Cut, tpl.cyclic);
        assert.equal(cr.success, true, `${tpl.tag}: CUT NOT ADMISSIBLE — Γ,Δ⊢C unprovable cut-free`);
        assert.equal(kernel.verifyTree(cr.proofTree).valid, true, `${tpl.tag}: cut result must be kernel-valid`);
        exercised++;
      }
      assert.ok(exercised >= 5, `expected ≥5 templates for ${cname}, got ${exercised}`);
    });
  });
}

// The composition is the point: grill exercises graded × coinductive cut through
// the UNCHANGED generic cut — the axes compose at the cut-elimination layer too.
describe('cut-admissibility — the grade × fixpoint composition (grill)', () => {
  let fp, specs, alternatives, prover, kernel;
  before(async () => {
    const { calc, fp: parser } = await loadCalc('grill');
    fp = parser;
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc); kernel = createKernel(calc);
  });
  const prove = (lin, cart, succ) => prover.prove(
    Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ)),
    { rules: specs, alternatives, maxDepth: 300, cyclicProofs: true, exhaustive: true });

  const countCycles = (t) => { let n = 0; const w = (x) => { if (!x) return; if (x.rule === 'nu_cycle') n++; (x.premises || []).forEach(w); }; w(t); return n; };

  it('graded coinductive cut:  (!a ⊢ A)  cut  (A ⊢ A)  ⇒  !a ⊢ A  is cut-free AND still CYCLIC', () => {
    // The cut RESULT is the graded signal A = νX.(a & !!_0 X) itself, so cut
    // elimination must reproduce a genuinely COINDUCTIVE (nu_cycle) proof — not a
    // trivial identity. This is the grade × fixpoint composition at the cut layer.
    const A = 'nu X. (a & !!_0 X)';
    assert.equal(prove([], ['a'], A).success, true, 'left: the graded signal is derivable');
    assert.equal(prove([A], [], A).success, true, 'right: the identity consumer A ⊢ A');
    const cut = prove([], ['a'], A);
    assert.equal(cut.success, true, 'the composed !a ⊢ A is cut-free provable');
    assert.equal(kernel.verifyTree(cut.proofTree).valid, true, 'kernel- + GTC-verified');
    assert.ok(countCycles(cut.proofTree) >= 1, 'the composed proof is genuinely coinductive (carries a nu_cycle)');
  });
});
