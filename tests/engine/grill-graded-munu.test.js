/**
 * grill — graded μMALL: gill (grades) + fill (μ/ν fixpoints) in ONE calculus.
 * The concrete "grade × fixpoint" experiment (the unification's first brick):
 * does a resource-semiring grade compose SOUNDLY with least/greatest fixed
 * points? This pins that it does — graded coinductive signals, graded inductive
 * streams, and grade arithmetic UNDER fixpoints all prove and kernel-verify,
 * while the genuinely unprovable stays refused. The generic cyclic-proof GTC
 * needs NO change: grades ride inside the fixpoint body and are discharged by
 * gill's own rules; νR remains the trace progress.
 *
 * Findings recorded here (see doc/theory for the roadmap):
 *   - grill loads by @extends gill + the fill μ/ν surface; deriveRoles arms
 *     lfp/gfp alongside gill's grade roles — no engine change.
 *   - The exponential-as-fixpoint bridge: the ν-encoding !A = νX.(A&(1&(X⊗X)))
 *     VALIDATES the exponential's laws (dereliction, contraction, and
 *     !a ⊢ encoding), demonstrating grades and the fixpoint-exponential coexist.
 *     The reverse direction (encoding ⊢ primitive-!a) is SEMANTICALLY valid (both
 *     denote the free commutative comonoid on a) but NOT cut-free derivable in the
 *     current rules — a calculus-completeness gap (fill has no rule promoting a
 *     linearly/type-held comonoid into the persistent zone), NOT a search gap:
 *     `exhaustive` does not recover it either (THY_0044 §3; the directionality is
 *     pinned in baelde-exponential.test.js). So it is not merely UN-asserted — the
 *     search is DOOMED (the rules cannot produce the proof), and it must NEVER be
 *     added because the doomed search also BLOWS UP: nu_l is non-invertible, so it
 *     branches through with_l's tensor arm (enc*enc → two copies), doubling the enc
 *     count per level (~2.25x/depth; maxDepth=25: ~1.4s; maxDepth=30: ~85s).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createProver } from '../../lib/prover/focused.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { loadGrillSequent, grillCalculusConfig } from '../../calculus/grill/calculus-config.js';

const countCycles = (t) => { let n = 0; const w = (x) => { if (!x) return; if (x.rule === 'nu_cycle') n++; (x.premises || []).forEach(w); }; w(t); return n; };

describe('grill — graded μMALL (gill grades × fill μ/ν)', () => {
  let calc, specs, alternatives, prover, kernel, fp;
  before(() => {
    calc = loadGrillSequent();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc); kernel = createKernel(calc);
    fp = grillCalculusConfig.loader.buildParser();
  });
  // returns { ok, kv, cycles }
  const prove = (lin, cart, succ, extra = {}) => {
    const r = prover.prove(Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ)),
      { rules: specs, alternatives, maxDepth: 300, ...extra });
    return r.success
      ? { ok: true, kv: kernel.verifyTree(r.proofTree).valid, cycles: countCycles(r.proofTree) }
      : { ok: false };
  };

  it('loads: BOTH axes present — grade roles (gill) AND lfp/gfp (fill μ/ν)', () => {
    assert.equal(calc.roles.lfp, 'mu', 'μ armed');
    assert.equal(calc.roles.gfp, 'nu', 'ν armed');
    assert.equal(calc.roles.exponential, 'bang', 'graded ! inherited');
    assert.ok(calc.roles.computation, 'graded lax monad inherited');
    assert.ok(calc.constructors.haul || calc.constructors.circle === undefined, 'gill graded surface inherited');
  });

  it('FIXPOINTS still work (inherited from fill surface)', () => {
    const sig = prove([], ['a'], 'nu X. (a & X)', { cyclicProofs: true });
    assert.equal(sig.ok, true); assert.equal(sig.kv, true); assert.equal(sig.cycles, 1);
    assert.equal(prove([], [], 'nu X. (a * X)', { cyclicProofs: true }).ok, false, 'νX.(a*X) from ∅ unprovable');
  });

  it('GRADES still work (inherited from gill — haul transport comonad + arithmetic)', () => {
    assert.equal(prove(['a'], [], '!!_0 a').ok, true, 'haul unit: a ⊢ !!_0 a');
    const sub = prove(['!!_2 a'], [], '!!_5 a');
    assert.equal(sub.ok, true, 'cost subsumption !!_2 ⊢ !!_5 (grade arithmetic)');
    assert.equal(sub.kv, true, 'kernel-verified');
    assert.equal(prove(['!!_1 a'], [], 'a').ok, false, 'distance is not possession: !!_1 a ⊬ a');
  });

  it('COMPOSE — graded COINDUCTIVE signal:  !a ⊢ νX.(a & !!_0 X)  (kernel + GTC verified)', () => {
    const r = prove([], ['a'], 'nu X. (a & !!_0 X)', { cyclicProofs: true });
    assert.equal(r.ok, true, 'a signal whose tail is reachable each tick');
    assert.equal(r.kv, true, 'kernel- + GTC-verified — grades ride the cycle soundly');
    assert.equal(r.cycles, 1);
  });

  it('COMPOSE — graded INDUCTIVE stream:  a ⊢ μX.(a ⊕ !!_0 X)  and  !!_0 a ⊢ μX.(a ⊕ X)', () => {
    const s1 = prove(['a'], [], 'mu X. (a + !!_0 X)');
    assert.equal(s1.ok, true); assert.equal(s1.kv, true); assert.equal(s1.cycles, 0, 'inductive: finite');
    const s2 = prove(['!!_0 a'], [], 'mu X. (a + X)');
    assert.equal(s2.ok, true); assert.equal(s2.kv, true);
  });

  it('COMPOSE — a graded modality over a fixpoint:  νX.(a&X) ⊢ !!_0 (νX.(a&X))', () => {
    const r = prove(['nu X. (a & X)'], [], '!!_0 (nu X. (a & X))');
    assert.equal(r.ok, true); assert.equal(r.kv, true);
  });

  it('BRIDGE — the ν-encoding validates the exponential laws (grades × fixpoint-!)', () => {
    const B = 'nu X. (a & (I & (X * X)))';   // !a as a ν-encoding
    assert.equal(prove(['! a'], [], B, { cyclicProofs: true }).kv, true, '!a ⊢ encoding');
    assert.equal(prove([B], [], 'a', { cyclicProofs: true }).kv, true, 'dereliction: enc ⊢ a');
    assert.equal(prove([B], [], 'a * a', { cyclicProofs: true }).kv, true, 'contraction: enc ⊢ a⊗a');
  });

  it('SOUNDNESS — the composition manufactures no false proof', () => {
    assert.equal(prove(['!!_1 a'], [], 'mu X. (a + X)', { cyclicProofs: true }).ok, false);
    assert.equal(prove([], [], 'nu X. (a & !!_0 X)', { cyclicProofs: true }).ok, false, 'no resource ⇒ no signal');
    assert.equal(prove(['a', 'b'], [], 'a & b').ok, false);
    // coinductive weakening is rejected in the graded setting too (audit fix):
    // a linear/graded resource conserved around a ν-cycle cannot be discharged.
    assert.equal(prove(['a'], [], 'nu X. X', { cyclicProofs: true }).ok, false, 'linear a ⊬ νX.X');
    assert.equal(prove(['!!_5 a'], [], 'nu X. (!!_2 X)', { cyclicProofs: true }).ok, false,
      '!!_5 a ⊬ νX.(!!_2 X) — graded resource not discharged by the cycle');
    assert.equal(prove([], [], 'nu X. X', { cyclicProofs: true }).ok, true, '· ⊢ νX.X (empty pool, nothing dropped)');
    // INVARIANT: every grill success across a battery is kernel-valid.
    const battery = [
      [['a'], [], '!!_0 a'], [['!!_2 a'], [], '!!_5 a'], [[], ['a'], 'nu X. (a & !!_0 X)'],
      [['a'], [], 'mu X. (a + !!_0 X)'], [['! a'], [], 'a'], [[], ['a'], 'nu X. (a & X)'],
    ];
    for (const [lin, cart, succ] of battery) {
      const r = prover.prove(Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ)),
        { rules: specs, alternatives, maxDepth: 300, cyclicProofs: true });
      if (r.success) assert.equal(kernel.verifyTree(r.proofTree).valid, true,
        `grill success must be kernel-valid: ${JSON.stringify(lin)}/${JSON.stringify(cart)} ⊢ ${succ}`);
    }
  });
});
