/**
 * trill — graded reactive μMALL: grades (gill) × fixpoints (fill/grill) × the ○
 * next-time modality (rill), ALL THREE unification axes in one calculus (THY_0044
 * roadmap item 3). trill @extends grill and adds only the ○ tick, as rill @extends
 * fill. This pins that the axes COMPOSE with NO engine change: the whole-context
 * @tick is grade- and fixpoint-agnostic, so graded temporal signals and streams
 * prove and kernel-verify while the genuinely unprovable stays refused.
 *
 * The composition payoff:
 *   - graded ○-guarded signal   !a ⊢ νX.(a & ○(!!_0 X))   (coinductive + temporal + graded)
 *   - graded temporal stream     a ⊢ μX.(a ⊕ ○(!!_0 X))
 *   - grade commutes over a tick  ○(!!_0 a) ⊢ !!_0 (○a)
 * All kernel- and GTC-verified; the ○ still does not collapse (○a ⊬ a, a ⊬ ○a).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createProver } from '../../lib/prover/focused.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { loadTrillSequent, trillCalculusConfig } from '../../calculus/trill/calculus-config.js';

const countCycles = (t) => { let n = 0; const w = (x) => { if (!x) return; if (x.rule === 'nu_cycle') n++; (x.premises || []).forEach(w); }; w(t); return n; };

describe('trill — graded reactive μMALL (grades × μ/ν × ○)', () => {
  let calc, specs, alternatives, prover, kernel, fp;
  before(() => {
    calc = loadTrillSequent();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc); kernel = createKernel(calc);
    fp = trillCalculusConfig.loader.buildParser();
  });
  // tries finite then cyclic; returns { ok, kv, cycles }
  const prove = (lin, cart, succ, extra = {}) => {
    for (const cyclicProofs of [false, true]) {
      const r = prover.prove(Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ)),
        { rules: specs, alternatives, maxDepth: 300, cyclicProofs, ...extra });
      if (r.success) return { ok: true, kv: kernel.verifyTree(r.proofTree).valid, cycles: countCycles(r.proofTree) };
    }
    return { ok: false };
  };

  it('loads: ALL THREE axes present — grade roles, lfp/gfp, and ○ (no role)', () => {
    assert.equal(calc.roles.lfp, 'mu', 'μ armed (fixpoints)');
    assert.equal(calc.roles.gfp, 'nu', 'ν armed (fixpoints)');
    assert.equal(calc.roles.exponential, 'bang', 'graded ! inherited (grades)');
    assert.ok(calc.roles.computation, 'graded lax monad inherited (grades)');
    assert.equal(calc.roles.circle, undefined, '○ is @category modality → NO engine role (does not touch the cyclic/grade engines)');
    assert.ok(calc.constructors.circle, '○ connective present');
  });

  it('GRADES inherited (gill): haul transport + arithmetic', () => {
    assert.equal(prove(['a'], [], '!!_0 a').ok, true, 'haul unit: a ⊢ !!_0 a');
    const sub = prove(['!!_2 a'], [], '!!_5 a');
    assert.equal(sub.ok, true); assert.equal(sub.kv, true, 'grade subsumption !!_2 ⊢ !!_5');
    assert.equal(prove(['!!_1 a'], [], 'a').ok, false, 'distance ≠ possession: !!_1 a ⊬ a');
  });

  it('FIXPOINTS inherited (fill/grill): a coinductive signal', () => {
    const s = prove([], ['a'], 'nu X. (a & X)', { cyclicProofs: true });
    assert.equal(s.ok, true); assert.equal(s.kv, true); assert.equal(s.cycles, 1);
  });

  it('○ TICK inherited (rill): applicative + non-collapse', () => {
    const app = prove(['O (a -o b)', 'O a'], [], 'O b');
    assert.equal(app.ok, true); assert.equal(app.kv, true, 'applicative ○(a⊸b),○a ⊢ ○b');
    assert.equal(prove(['O a'], [], 'a').ok, false, '○a ⊬ a (non-collapse)');
    assert.equal(prove(['a'], [], 'O a').ok, false, 'a ⊬ ○a (non-collapse)');
  });

  it('COMPOSE — graded ○-guarded SIGNAL:  !a ⊢ νX.(a & ○(!!_0 X))  (coinductive + temporal + graded)', () => {
    const r = prove([], ['a'], 'nu X. (a & O (!!_0 X))', { cyclicProofs: true });
    assert.equal(r.ok, true, 'a signal reachable each tick at a grade cost');
    assert.equal(r.kv, true, 'kernel- + GTC-verified — all three axes ride one proof');
    assert.equal(r.cycles, 1, 'genuinely coinductive (the ○ guard + haul reach the companion)');
  });

  it('COMPOSE — graded temporal STREAM:  a ⊢ μX.(a ⊕ ○(!!_0 X))', () => {
    const r = prove(['a'], [], 'mu X. (a + O (!!_0 X))');
    assert.equal(r.ok, true); assert.equal(r.kv, true); assert.equal(r.cycles, 0, 'inductive: finite');
  });

  it('COMPOSE — the grade commutes over the tick:  ○(!!_0 a) ⊢ !!_0 (○a)', () => {
    const r = prove(['O (!!_0 a)'], [], '!!_0 (O a)');
    assert.equal(r.ok, true); assert.equal(r.kv, true);
  });

  it('SOUNDNESS — the three-axis composition manufactures no false proof', () => {
    // coinductive weakening still rejected (a linear resource cannot ride a ν-cycle):
    assert.equal(prove(['a'], [], 'nu X. X', { cyclicProofs: true }).ok, false, 'a ⊬ νX.X');
    // no signal from nothing:
    assert.equal(prove([], [], 'nu X. (a & O (!!_0 X))', { cyclicProofs: true }).ok, false, '· ⊬ graded signal');
    // the ○ tick still cannot duplicate or collapse in the graded setting:
    assert.equal(prove(['O a'], [], 'O (a * a)').ok, false, '○a ⊬ ○(a⊗a) (no duplication over tick)');
    assert.equal(prove(['O a', 'b'], [], 'O b').ok, false, '○a, b ⊬ ○b (a non-○ resource cannot ride the tick)');
    // grade arithmetic is not bypassed by the temporal layer:
    assert.equal(prove(['!!_1 a'], [], 'mu X. (a + O (!!_0 X))', { cyclicProofs: true }).ok, false);
    // INVARIANT: every trill success across a battery is kernel-valid.
    const battery = [
      [['a'], [], '!!_0 a'], [[], ['a'], 'nu X. (a & O (!!_0 X))'],
      [['a'], [], 'mu X. (a + O (!!_0 X))'], [['O (a -o b)', 'O a'], [], 'O b'],
      [[], ['a'], 'nu X. (a & X)'], [['O (!!_0 a)'], [], '!!_0 (O a)'],
    ];
    for (const [lin, cart, succ] of battery) {
      const r = prover.prove(Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ)),
        { rules: specs, alternatives, maxDepth: 300, cyclicProofs: true });
      if (r.success) assert.equal(kernel.verifyTree(r.proofTree).valid, true,
        `trill success must be kernel-valid: ${JSON.stringify(lin)}/${JSON.stringify(cart)} ⊢ ${succ}`);
    }
  });
});
