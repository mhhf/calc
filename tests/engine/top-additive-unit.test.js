/**
 * ⊤ — the additive unit (unit of &), the LAST connective of the MALL fragment
 * (THY_0044 chapter 0 / big_next §0; TODO_0203's inventory). ⊤ is the exact DUAL
 * of `zero` (0, the unit of ⊕): 0 has a context-absorbing LEFT rule and no right
 * rule; ⊤ has a context-absorbing RIGHT rule and no left rule. `top_r` is the
 * whole-linear-context absorber `G ; Δ ⊢ ⊤` (no premises) — ⊤ is the top element,
 * so any linear resources are discarded into it. That is exactly `zero_l`'s dual,
 * so it rides the kernel's existing `discardsContext` machinery.
 *
 * SOUNDNESS (non-collapse): ⊤ has NO left rule (dual to 0 having no right rule),
 * so ⊤ on the left is inert — `⊤ ⊢ a` is NOT derivable. And ⊤ does not license
 * weakening for the OTHER units: `a ⊢ I` stays underivable (a linear resource
 * cannot vanish except into a ⊤). The kernel re-derives `top_r` and — the hole a
 * context-absorbing right rule would otherwise open — VALIDATES the succedent is
 * actually ⊤, so a forged `top_r` cannot prove an arbitrary `a ⊢ b`.
 *
 * COMPLETENESS: ⊤ absorbs an arbitrary SUBSET of the pool, so a multiplicative
 * split `Δ ⊢ ⊤ ⊗ b` where the ⊤ appears before a resource-consuming sibling needs
 * the don't-know exhaustive driver (the ⊤-vs-multiplicative-split corner); the
 * committed path handles `Δ ⊢ b ⊗ ⊤` (⊤ last) and the whole additive fragment.
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import Store from '../../lib/kernel/store.js';
import { createProver } from '../../lib/prover/focused.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { ProofTree } from '../../lib/prover/pt.js';
import { loadILL } from '../../calculus/ill/index.js';
import { loadFill } from '../../calculus/fill/index.js';

describe('⊤ — the additive unit (unit of &)', () => {
  let calc, fp, prover, kernel, base;
  before(async () => {
    calc = await loadILL();
    fp = (s) => calc.parse(s);
    const built = buildRuleSpecs(calc);
    prover = createProver(calc); kernel = createKernel(calc);
    base = { rules: built.specs, alternatives: built.alternatives };
  });
  const seq = (lin, cart, succ) => Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ));
  // tries committed, then exhaustive; returns { ok, kv }
  const prove = (lin, cart, succ, extra = {}) => {
    for (const exhaustive of [false, true]) {
      const r = prover.prove(seq(lin, cart, succ), { ...base, maxDepth: 200, exhaustive, ...extra });
      if (r.success) return { ok: true, kv: kernel.verifyTree(r.proofTree).valid, mode: exhaustive ? 'exh' : 'committed' };
    }
    return { ok: false };
  };
  const provable = (lin, cart, succ) => { const r = prove(lin, cart, succ); return r.ok && r.kv; };

  it('loads: ⊤ is a declared connective — additive, negative (dual of 0), no left rule', () => {
    assert.ok(calc.constructors.top, 'top declared');
    assert.equal(calc.polarity.top, 'negative', 'unit of the negative & is negative (0 is positive)');
    assert.equal(calc.constructors.top.annotations.category, 'additive');
    // The additiveUnit/additiveZero role SPLIT: ⊤ and 0 are distinct nullary
    // additives (both were previously lumped as additiveZero — a role collision).
    assert.equal(calc.roles.additiveUnit, 'top', '⊤ = additiveUnit');
    assert.equal(calc.roles.additiveZero, 'zero', '0 = additiveZero (unchanged)');
    assert.ok(calc.rules.top_r, 'top_r present');
    assert.ok(!calc.rules.top_l, 'NO top_l — ⊤ is inert on the left (dual of 0 having no right rule)');
    assert.ok(calc.constructors.zero, 'its dual 0 is present too');
  });

  it('⊤ is derivable from ANY linear context (the top element absorbs resources)', () => {
    assert.ok(provable([], [], 'top'), '⊢ ⊤');
    assert.ok(provable(['a'], [], 'top'), 'a ⊢ ⊤ (a absorbed)');
    assert.ok(provable(['a', 'b'], [], 'top'), 'a, b ⊢ ⊤');
    assert.ok(provable([], ['a'], 'top'), '!a ; ⊢ ⊤ (persistent present)');
    assert.ok(provable(['a', 'b'], ['c'], 'top'), 'a, b ; !c ⊢ ⊤');
  });

  it('⊤ is the unit of & — additive positions', () => {
    assert.ok(provable(['a'], [], 'top & a'), 'a ⊢ ⊤ & a');
    assert.ok(provable(['a'], [], 'a & top'), 'a ⊢ a & ⊤');
    assert.ok(provable([], [], 'top & top'), '⊢ ⊤ & ⊤');
    assert.ok(provable(['a', 'b'], [], '(a * b) & top'), 'a, b ⊢ (a⊗b) & ⊤');
    assert.ok(provable(['a'], [], 'a & (b -o top)'), 'a ⊢ a & (b ⊸ ⊤)');
  });

  it('⊤ on the left is a consumable absorbed by top_r; still no extraction', () => {
    assert.ok(provable(['top'], [], 'top'), '⊤ ⊢ ⊤');
    assert.ok(provable(['top', 'a'], [], 'top'), '⊤, a ⊢ ⊤');
  });

  it('multiplicative split: ⊤ absorbs its share (⊤ last is committed; ⊤ first needs exhaustive)', () => {
    assert.ok(provable(['a', 'b'], [], 'b * top'), 'a, b ⊢ b ⊗ ⊤ (⊤ last)');
    assert.ok(provable(['a', 'b'], [], 'top * b'), 'a, b ⊢ ⊤ ⊗ b (⊤ first — the corner)');
    assert.ok(provable(['a', 'b', 'c'], [], 'b * top'), 'a, b, c ⊢ b ⊗ ⊤');
    assert.ok(provable(['a'], [], '(a * top) & a'), 'a ⊢ (a⊗⊤) & a (⊤ absorbs nothing in branch 1)');
  });

  it('SOUNDNESS: ⊤ does NOT collapse and does NOT leak weakening', () => {
    // No left rule — ⊤ cannot yield an arbitrary succedent.
    assert.equal(prove(['top'], [], 'a').ok, false, '⊤ ⊬ a (no left rule)');
    assert.equal(prove(['top'], [], 'b').ok, false, '⊤ ⊬ b');
    assert.equal(prove(['top', 'a'], [], 'b').ok, false, '⊤, a ⊬ b');
    // ⊤ does not license weakening for the OTHER units / atoms.
    assert.equal(prove(['a'], [], 'I').ok, false, 'a ⊬ 1 (no ⊤ to absorb a)');
    assert.equal(prove(['a'], [], 'b').ok, false, 'a ⊬ b');
    assert.equal(prove(['a'], [], 'a * b').ok, false, 'a ⊬ a⊗b');
    assert.equal(prove(['a', 'b'], [], 'a').ok, false, 'a, b ⊬ a (b stranded, no ⊤)');
    // ⊤ ⊗ b still needs a real b.
    assert.equal(prove(['a'], [], 'top * b').ok, false, 'a ⊬ ⊤ ⊗ b (no b anywhere)');
  });

  it('KERNEL FORGERY FENCE: a context-absorbing right rule must re-check its succedent', () => {
    // The critical hole a ⊤-shaped rule would open: forge top_r on `a ⊢ b` — ⊤R
    // absorbs `a`, and without a succedent check the kernel would accept an
    // ARBITRARY succedent b. It must be rejected.
    const forgedTop = new ProofTree({
      conclusion: seq(['a'], [], 'b'), premises: [], rule: 'top_r', proven: true,
    });
    assert.equal(kernel.verifyTree(forgedTop).valid, false, 'forged top_r a ⊢ b REJECTED');
    // The same class, latent for one_r (empty-context only): also closed.
    const forgedOne = new ProofTree({
      conclusion: seq([], [], 'b'), premises: [], rule: 'one_r', proven: true,
    });
    assert.equal(kernel.verifyTree(forgedOne).valid, false, 'forged one_r ⊢ b REJECTED');
    // A genuine top_r stays valid.
    const realTop = new ProofTree({
      conclusion: seq(['a'], [], 'top'), premises: [], rule: 'top_r', proven: true,
    });
    assert.equal(kernel.verifyTree(realTop).valid, true, 'genuine top_r a ⊢ ⊤ VALID');
  });

  it('INVARIANT: every ⊤ success is kernel-valid (soundness battery)', () => {
    const battery = [
      [[], [], 'top'], [['a'], [], 'top'], [['a', 'b'], ['c'], 'top'],
      [['a'], [], 'top & a'], [['a'], [], 'a & top'], [['a', 'b'], [], 'b * top'],
      [['a', 'b'], [], 'top * b'], [['top'], [], 'top'],
    ];
    for (const [lin, cart, succ] of battery) {
      const r = prove(lin, cart, succ);
      assert.equal(r.ok, true, `${succ} should prove`);
      assert.equal(r.kv, true, `${lin}|${cart} ⊢ ${succ} must be kernel-valid (${r.mode})`);
    }
  });

  it('inherited: ⊤ flows to the fill fork (μMALL) via @extends', async () => {
    const fcalc = await loadFill();
    assert.ok(fcalc.constructors.top, 'fill inherits ⊤');
    assert.ok(fcalc.rules.top_r, 'fill inherits top_r');
  });
});
