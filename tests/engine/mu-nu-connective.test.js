/**
 * μMALL fixed-point connectives (TODO_0009 rung 3 / Inc-1).
 *
 * `mu` (least fixed point, positive) and `nu` (greatest fixed point, negative)
 * are added to ILL as DATA: unary de-Bruijn binder connectives (the exists/
 * forall template) with four unfold rules mu_r/mu_l/nu_r/nu_l realizing the
 * Knaster–Tarski identity σX.F = F[σX.F/X] via the new `@binding unfold` mode
 * (witness = the whole fixpoint formula — a single deterministic substitution).
 *
 * These pins establish, for FINITE proofs (no cycles yet): (1) the store/parser
 * plumbing (PRED_BOUNDARY shift, de-Bruijn encoding, polarity, roles); (2) all
 * four rule directions prove; (3) the kernel FULLY verifies each unfold step
 * (no `unverified:'binding'` degradation — unfold is deterministic, unlike ∃/∀);
 * (4) forged unfoldings are REJECTED (the soundness gate).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import Seq from '../../lib/kernel/sequent.js';
import { createProver } from '../../lib/prover/focused.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { ProofTree } from '../../lib/prover/pt.js';
import { loadILL } from '../../calculus/ill/index.js';
import { buildForwardParser } from '../../calculus/ill/lib/forward-parser.js';

describe('μ/ν connectives — store + parser plumbing (Inc-1)', () => {
  let calc, fp;
  before(async () => { calc = await loadILL(); fp = buildForwardParser(); });

  it('appends exactly two tags, shifting PRED_BOUNDARY 35→37', () => {
    assert.equal(Store.PRED_BOUNDARY, 37);
    assert.equal(typeof Store.TAG.mu, 'number');
    assert.equal(typeof Store.TAG.nu, 'number');
    assert.ok(Store.TAG.mu < Store.PRED_BOUNDARY && Store.TAG.nu < Store.PRED_BOUNDARY);
  });

  it('parses `mu X. (a * X)` to a de-Bruijn binder term mu(tensor(a, bound 0))', () => {
    const f = fp('mu X. (a * X)');
    assert.equal(Store.tag(f), 'mu');
    const body = Store.child(f, 0);
    assert.equal(Store.tag(body), 'tensor');
    assert.equal(Store.tag(Store.child(body, 1)), 'bound');
    assert.equal(Store.child(Store.child(body, 1), 0), 0n);   // innermost = index 0
  });

  it('encodes nested binders `mu X. nu Y. (X & Y)` with correct de-Bruijn depths', () => {
    // X is the OUTER binder (index 1 from inside the nu), Y the inner (index 0).
    const f = fp('mu X. nu Y. (X & Y)');
    assert.equal(Store.tag(f), 'mu');
    const nu = Store.child(f, 0);
    assert.equal(Store.tag(nu), 'nu');
    const withNode = Store.child(nu, 0);
    assert.equal(Store.tag(withNode), 'with');
    assert.equal(Store.child(Store.child(withNode, 0), 0), 1n); // X → depth 1
    assert.equal(Store.child(Store.child(withNode, 1), 0), 0n); // Y → depth 0
  });

  it('assigns μ positive / ν negative polarity and lfp/gfp roles', () => {
    assert.equal(calc.polarity.mu, 'positive');
    assert.equal(calc.polarity.nu, 'negative');
    assert.equal(calc.roles.lfp, 'mu');
    assert.equal(calc.roles.gfp, 'nu');
  });

  it('loads the four unfold rules with correct invertibility', () => {
    for (const r of ['mu_r', 'mu_l', 'nu_r', 'nu_l']) assert.ok(calc.rules[r], `${r} present`);
    // μ positive: μL invertible, μR needs focus. ν negative: νR invertible, νL needs focus.
    assert.equal(calc.invertible?.mu_r, false);
    assert.equal(calc.invertible?.nu_l, false);
  });
});

describe('μ/ν unfold — finite proofs prove and FULLY kernel-verify', () => {
  let calc, fp, prover, kernel, opts;
  before(async () => {
    calc = await loadILL();
    fp = buildForwardParser();
    const built = buildRuleSpecs(calc);
    prover = createProver(calc);
    kernel = createKernel(calc);
    opts = { rules: built.specs, alternatives: built.alternatives };
  });
  const seq = (lin, succ) => Seq.fromArrays(lin.map(fp), [], fp(succ));

  // Each: μL/μR/νR/νL, all finite (the recursive branch is discarded or absent).
  const cases = [
    ['μL   mu X.(a & X) ⊢ a',        ['mu X. (a & X)'], 'a'],
    ['μR   ⊢ mu X.(I + X)  (Nat 0)', [],               'mu X. (I + X)'],
    ['νR   ⊢ nu X.(I & I)',          [],               'nu X. (I & I)'],
    ['νL   nu X.(a & I) ⊢ a',        ['nu X. (a & I)'], 'a'],
    ['μL²  mu X.(a & (b & X)) ⊢ b',  ['mu X. (a & (b & X))'], 'b'],
  ];
  for (const [name, lin, succ] of cases) {
    it(`proves + verifies: ${name}`, () => {
      const r = prover.prove(seq(lin, succ), opts);
      assert.equal(r.success, true, 'proof search succeeds');
      const v = kernel.verifyTree(r.proofTree);
      assert.equal(v.valid, true, `kernel verifies (${v.errors?.[0] || ''})`);
      // The whole point of `@binding unfold`: deterministic, so NO binding
      // degradation — unlike ∃/∀ which mark unverified:'binding'.
      const unv = v.unverified ? [...v.unverified] : [];
      assert.ok(!unv.includes('binding'), `unfold steps fully verified, not degraded (${JSON.stringify(unv)})`);
    });
  }
});

describe('μ/ν unfold — the kernel rejects forged unfoldings (soundness gate)', () => {
  let calc, fp, kernel;
  before(async () => { calc = await loadILL(); fp = buildForwardParser(); kernel = createKernel(calc); });
  const S = (lin, succ) => Seq.fromArrays(lin.map(fp), [], fp(succ));
  const leafId = (f) => new ProofTree({ conclusion: Seq.fromArrays([fp(f)], [], fp(f)), rule: 'id', proven: true, premises: [] });

  it('rejects a mu_l step whose premise is the WRONG unfolding (a & I ≠ a & mu X.(a&X))', () => {
    const goal = S(['mu X. (a & X)'], 'a');
    // correct unfolding is `a & mu X.(a&X)`; forge `a & I` instead.
    const forged = new ProofTree({
      conclusion: goal, rule: 'mu_l', proven: true,
      premises: [new ProofTree({ conclusion: S(['a & I'], 'a'), rule: 'with_l1', proven: true, premises: [leafId('a')] })],
    });
    const v = kernel.verifyTree(forged);
    assert.equal(v.valid, false, 'forged unfolding must be rejected');
    assert.ok(v.errors.length > 0);
  });

  it('rejects a mu_l step applied to a non-μ principal (wrong tag)', () => {
    // conclusion has `a & b` (a with, not a mu) in the context; claim mu_l.
    const goal = S(['a & b'], 'a');
    const forged = new ProofTree({
      conclusion: goal, rule: 'mu_l', proven: true,
      premises: [leafId('a')],
    });
    const v = kernel.verifyTree(forged);
    assert.equal(v.valid, false, 'mu_l on a non-μ formula must be rejected');
  });

  it('rejects a nu_r step whose premise is the WRONG unfolding', () => {
    // ⊢ nu X.(a & I): correct unfolding `a & I`; forge `a & a`.
    const goal = S([], 'nu X. (a & I)');
    const forged = new ProofTree({
      conclusion: goal, rule: 'nu_r', proven: true,
      premises: [new ProofTree({ conclusion: S([], 'a & a'), rule: 'with_r', proven: true,
        premises: [leafId('a'), leafId('a')] })],
    });
    const v = kernel.verifyTree(forged);
    assert.equal(v.valid, false, 'forged νR unfolding must be rejected');
  });
});
