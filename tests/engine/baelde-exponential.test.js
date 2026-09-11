/**
 * The Baelde exponential correspondence in intuitionistic linear μMALL
 * (TODO_0009 rung 3, Inc-5a; THY_0042). Baelde (TOCL 2012) showed the
 * exponentials are DEFINABLE from fixed points. big_next.md §1 / TODO_0203
 * record this as `!A = νX.(A & X)` — but that is an OVERSIMPLIFICATION in the
 * intuitionistic LINEAR setting: a linear `&` cannot duplicate its resource, so
 * νX.(A & X) gives dereliction but NOT contraction. The correspondence needs the
 * multiplicative body:
 *
 *     !A  :=  νX. (A & (1 & (X ⊗ X)))
 *
 * where the `X ⊗ X` is what lets a left-ν UNFOLD into two independent copies
 * (contraction) and the `1` is the weakening alternative. This file validates,
 * all machine-checked by the kernel + GTC, the directions that hold and pins the
 * correction: contraction succeeds for the ⊗-body encoding and FAILS for the
 * naive one. Contraction/dereliction are FINITE (the left ν unfolds on demand);
 * the genuinely coinductive direction — building an unbounded signal from
 * persistent resources — is the cyclic proof (Inc-4).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import { createProver } from '../../lib/prover/focused.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { loadFill } from '../../calculus/fill/index.js';
import { buildForwardParser } from '../../calculus/fill/lib/forward-parser.js';

const BANG = (A) => `nu X. (${A} & (I & (X * X)))`;   // !A, corrected encoding
const NAIVE = (A) => `nu X. (${A} & X)`;               // big_next.md's oversimplification
const countCycles = (t) => { let n = 0; const w = (x) => { if (!x) return; if (x.rule === 'nu_cycle') n++; (x.premises || []).forEach(w); }; w(t); return n; };

describe('Baelde exponential correspondence, ILL-corrected (Inc-5a)', () => {
  let fp, prover, kernel, base;
  before(async () => {
    const calc = await loadFill();
    fp = buildForwardParser();
    const built = buildRuleSpecs(calc);
    prover = createProver(calc); kernel = createKernel(calc);
    base = { rules: built.specs, alternatives: built.alternatives };
  });
  // returns { ok, kv, cycles }; tries finite then cyclic
  const prove = (lin, succ, cart = []) => {
    for (const cyclicProofs of [false, true]) {
      const r = prover.prove(Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ)), { ...base, maxDepth: 400, cyclicProofs });
      if (r.success) return { ok: true, kv: kernel.verifyTree(r.proofTree).valid, cycles: countCycles(r.proofTree) };
    }
    return { ok: false };
  };

  it('dereliction  !a ⊢ a  (finite, kernel-verified)', () => {
    const r = prove([BANG('a')], 'a');
    assert.equal(r.ok, true); assert.equal(r.kv, true);
  });

  it('CONTRACTION  !a ⊢ !a ⊗ !a  (the headline: a fixed point yields duplication)', () => {
    const r = prove([BANG('a')], `(${BANG('a')}) * (${BANG('a')})`);
    assert.equal(r.ok, true, 'contraction holds for the ⊗-body encoding');
    assert.equal(r.kv, true, 'kernel-verified');
  });

  it('resource reuse  !a ⊢ a ⊗ a  and  !a ⊢ a ⊗ (a ⊗ a)', () => {
    for (const succ of ['a * a', 'a * (a * a)']) {
      const r = prove([BANG('a')], succ);
      assert.equal(r.ok, true, succ); assert.equal(r.kv, true);
    }
  });

  it('promotion / idempotence  !a ⊢ !a  (kernel-verified)', () => {
    const r = prove([BANG('a')], BANG('a'));
    assert.equal(r.ok, true); assert.equal(r.kv, true);
  });

  it('CORRECTION: the naive νX.(A & X) gives dereliction but NOT contraction', () => {
    assert.equal(prove([NAIVE('a')], 'a').ok, true, 'naive encoding still dereliction');
    assert.equal(prove([NAIVE('a')], 'a * a').ok, false,
      'a linear & cannot duplicate — naive νX.(A&X) is not !A (big_next.md corrected)');
  });

  it('the COINDUCTIVE direction — an unbounded signal from persistent a — is a cyclic proof', () => {
    // !a (persistent, backward !) ⊢ νX.(a & X): the signal is available forever;
    // only provable coinductively (a νR back-edge). This is the genuinely cyclic
    // half — contraction above was finite (left-ν unfolds on demand).
    const finite = prover.prove(Seq.fromArrays([], [fp('a')], fp(NAIVE('a'))), { ...base, maxDepth: 300 });
    assert.equal(finite.success, false, 'no finite proof');
    const cyc = prover.prove(Seq.fromArrays([], [fp('a')], fp(NAIVE('a'))), { ...base, maxDepth: 300, cyclicProofs: true });
    assert.equal(cyc.success, true, 'coinductive proof succeeds');
    assert.equal(countCycles(cyc.proofTree), 1);
    assert.equal(kernel.verifyTree(cyc.proofTree).valid, true);
  });

  it('KNOWN GAP: multiplicative weakening !a ⊢ I is not captured (with_l2/1 focus corner)', () => {
    // Discarding the signal would need to project the `1` alternative, but the
    // focused prover has a pre-existing with_l2 + I focus-completeness corner
    // (a & I ⊢ I fails while I & a ⊢ I succeeds) — orthogonal to μ/ν. Pinned so a
    // future focus fix surfaces here. ILL's primitive ! weakens via its cartesian
    // zone; the fixed-point encoding does not recover that here.
    assert.equal(prove([BANG('a')], 'I').ok, false);
  });
});
