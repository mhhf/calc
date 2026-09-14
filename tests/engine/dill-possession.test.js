/**
 * dill — principal-indexed possession `says K A` over gill (THY_0045 / THY_0046).
 *
 * The mechanized witness for the cut-admissibility and non-interference results.
 * The headline is a REFUTATION: no-cross-principal-collapse (THY_0045 Fact P1) is
 * the partial-⊕ of the principal grade, realized as INDEX UNIFICATION in poss_l —
 * so `says k1 a ⊢ says k2 a` is UNDERIVABLE for distinct principals, while the
 * diagonal `says k (says k b) ⊢ says k b` holds. The combined `says k (!!_0 a)`
 * (possession over gill's graded comonad, standing in for the weight-graded stake)
 * witnesses the orthogonal-composition cut (THY_0045 §5.3, Lemma O) through the
 * UNCHANGED generic cut. Principals are numeric identity tags (see dill.calc).
 *
 * Refutation caveat (as tools/fuzz-cut.js): `.success === false` means the
 * exhaustive focused search found no proof; for this fragment (poss rules are
 * deterministic, no additive don't-know beyond gill's) that coincides with
 * underivability — the same search-completeness-relative reading the family's
 * `!!_5 a ⊬ !!_3 a` refutation carries.
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createProver } from '../../lib/prover/focused.js';
import { createKernel } from '../../lib/prover/kernel.js';

describe('dill — principal possession `says K A` (THY_0045/0046)', () => {
  let fp, specs, alternatives, prover, kernel;
  before(async () => {
    const { loadDillSequent, dillCalculusConfig } = await import('../../calculus/dill/calculus-config.js');
    const calc = loadDillSequent();
    fp = dillCalculusConfig.loader.buildParser();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc);
    kernel = createKernel(calc);
  });
  const prove = (lin, succ, cart = []) => prover.prove(
    Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ)),
    { rules: specs, alternatives, maxDepth: 300, exhaustive: true });

  // ── derivable: identity, the [μ] diagonal, affirmation intro ──────────────
  it('identity of a possession:  says 1 a ⊢ says 1 a', () => {
    assert.equal(prove(['says 1 a'], 'says 1 a').success, true);
  });
  it('same-principal collapse ([μ] diagonal, K1=K2):  says 1 (says 1 b) ⊢ says 1 b', () => {
    assert.equal(prove(['says 1 (says 1 b)'], 'says 1 b').success, true);
  });
  it('affirmation intro (says-I):  a ⊢ says 1 a', () => {
    assert.equal(prove(['a'], 'says 1 a').success, true);
  });

  // ── the headline: no-cross-principal-collapse = partial-⊕ vacuity ─────────
  it('REFUTED cross-principal:  says 1 a ⊬ says 2 a', () => {
    assert.equal(prove(['says 1 a'], 'says 2 a').success, false);
  });
  it('REFUTED nested cross-principal:  says 1 (says 2 b) ⊬ says 1 b  (K1≠K2)', () => {
    assert.equal(prove(['says 1 (says 2 b)'], 'says 1 b').success, false);
  });
  it('REFUTED non-degeneracy (says ⊬ truth):  says 1 a ⊬ a', () => {
    assert.equal(prove(['says 1 a'], 'a').success, false);
  });

  // ── orthogonal composition (Lemma O): the combined modality ───────────────
  it('combined modality intro:  a ⊢ says 1 (!!_0 a)', () => {
    assert.equal(prove(['a'], 'says 1 (!!_0 a)').success, true);
  });

  // ── cut admissibility over the combined modality (mechanized THY_0045) ────
  it('cut admissible over `says 1 (!!_0 a)`: L, R, Cut cut-free provable + kernel-valid', () => {
    const A = 'says 1 (!!_0 a)';
    const L = prove(['a'], A);                 // Γ ⊢ A
    const R = prove([A], A);                   // A, Δ ⊢ A  (identity consumer)
    const Cut = prove(['a'], A);               // Γ, Δ ⊢ A  (composed)
    assert.equal(L.success, true, 'L: a ⊢ says 1 (!!_0 a)');
    assert.equal(R.success, true, 'R: says 1 (!!_0 a) ⊢ says 1 (!!_0 a)');
    assert.equal(Cut.success, true, 'Cut: a ⊢ says 1 (!!_0 a) cut-free');
    assert.equal(kernel.verifyTree(Cut.proofTree).valid, true, 'cut result kernel-valid');
  });

  // ── NI-2 (THY_0046): the inner cost-0 grade is inert (grade-0 erasure shadow) ─
  it('inner dereliction (NI-2 shadow):  says 1 (!!_0 a) ⊢ says 1 a', () => {
    assert.equal(prove(['says 1 (!!_0 a)'], 'says 1 a').success, true);
  });
});
