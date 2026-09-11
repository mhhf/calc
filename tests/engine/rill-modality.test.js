/**
 * rill — the ○ next-time modality (TODO_0203, THY_0042). rill = fill + ○, the
 * reactive/FRP layer forked out of fill to firewall the soundness-subtle temporal
 * machinery from the audited μMALL core (as fill firewalls μMALL from ILL).
 *
 * ○A = "A at the NEXT tick, not now." Its single rule ○R is promotion-shaped
 * (G ; |- ○A <- G ; |- A, empty linear context): a linear resource consumed now
 * cannot be re-offered next tick — only persistent (!) resources, or the tail of
 * a signal, advance. There is NO ○-left rule, so ○ does not collapse (○a ⊬ a,
 * a ⊬ ○a). Guarded signals νX.(A & ○X) coinduct via the ν back-edge (the GTC
 * needs no change — ○ is the syntactic guard, νR is the trace progress). All
 * proofs below are kernel- and GTC-verified.
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import Store from '../../lib/kernel/store.js';
import { createProver } from '../../lib/prover/focused.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { loadRill } from '../../calculus/rill/index.js';
import { buildForwardParser } from '../../calculus/rill/lib/forward-parser.js';
import { loadFill } from '../../calculus/fill/index.js';
import { loadILL } from '../../calculus/ill/index.js';

const countCycles = (t) => { let n = 0; const w = (x) => { if (!x) return; if (x.rule === 'nu_cycle') n++; (x.premises || []).forEach(w); }; w(t); return n; };

describe('rill — the ○ next-time modality (TODO_0203)', () => {
  let calc, fp, prover, kernel, base;
  before(async () => {
    calc = await loadRill();
    fp = buildForwardParser();
    const built = buildRuleSpecs(calc);
    prover = createProver(calc); kernel = createKernel(calc);
    base = { rules: built.specs, alternatives: built.alternatives };
  });
  const seq = (lin, cart, succ) => Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ));
  // tries finite then cyclic; returns { ok, kv, cycles }
  const prove = (lin, cart, succ, extra = {}) => {
    for (const cyclicProofs of [false, true]) {
      const r = prover.prove(seq(lin, cart, succ), { ...base, maxDepth: 300, cyclicProofs, ...extra });
      if (r.success) return { ok: true, kv: kernel.verifyTree(r.proofTree).valid, cycles: countCycles(r.proofTree) };
    }
    return { ok: false };
  };

  it('loads: ○ is a declared connective; μ/ν inherited; ○ gets NO engine role', () => {
    assert.ok(calc.constructors.circle, 'circle declared');
    assert.equal(calc.polarity.circle, 'positive');
    assert.equal(calc.roles.lfp, 'mu', 'μ inherited from fill');
    assert.equal(calc.roles.gfp, 'nu', 'ν inherited from fill');
    // circle is @category modality → no lfp/gfp/exponential/... role, so the
    // cyclic-proof engine is untouched by ○.
    for (const [role, v] of Object.entries(calc.roles)) {
      assert.notEqual(v, 'circle', `circle must not claim role ${role}`);
    }
  });

  it('parses ○ without corrupting identifiers that start with O', () => {
    assert.equal(Store.tag(fp('O a')), 'circle');
    assert.equal(Store.tag(fp('Out')), 'metavar', 'Out is one identifier, not O·ut');
    assert.equal(Store.tag(fp('O (a * b)')), 'circle');
  });

  it('NON-COLLAPSE (soundness): ○ is a genuine modality — ○a ⊬ a and a ⊬ ○a', () => {
    // A linear resource cannot advance to the next tick, and an ○A cannot be
    // used in the present. Both directions and their iterates must FAIL.
    assert.equal(prove(['a'], [], 'O a').ok, false, 'a ⊬ ○a (linear no-advance)');
    assert.equal(prove(['a'], [], 'O O a').ok, false, 'a ⊬ ○○a (iterate: linear no-advance)');
    assert.equal(prove(['O a'], [], 'a').ok, false, '○a ⊬ a (no elim now)');
    assert.equal(prove(['O O a'], [], 'a').ok, false, '○○a ⊬ a (iterate: no elim)');
    assert.equal(prove(['O a'], [], 'O O a').ok, false, '○a ⊬ ○○a');
    assert.equal(prove([], [], 'O a').ok, false, '· ⊬ ○a');
    // ○ is NOT monoidal here (no ○-left / whole-context advance): ○a,○b ⊬ ○(a⊗b)
    assert.equal(prove(['O a', 'O b'], [], 'O (a * b)').ok, false);
  });

  it('ADDITIVE identical branches:  !a ⊢ ○a & ○a  and  !a ⊢ a & a  (committed AND exhaustive)', () => {
    // Two with_r branches with the SAME sequent hash. Exercises the CPS
    // loop-detection scoping fix (audit 2026-09-11): without it the exhaustive
    // driver spuriously self-detected a loop on the second branch and failed.
    for (const succ of ['(O a) & (O a)', 'a & a']) {
      const committed = prove([], ['a'], succ);
      assert.equal(committed.ok, true, `committed: !a ⊢ ${succ}`);
      assert.equal(committed.kv, true);
      const exh = prove([], ['a'], succ, { exhaustive: true });
      assert.equal(exh.ok, true, `exhaustive: !a ⊢ ${succ}`);
      assert.equal(exh.kv, true, `exhaustive kernel-verified: ${succ}`);
    }
  });

  it('PERSISTENT ADVANCE: !a ⊢ ○a and !a ⊢ ○○a (kernel-verified)', () => {
    for (const succ of ['O a', 'O O a', 'O O O a']) {
      const r = prove([], ['a'], succ);
      assert.equal(r.ok, true, `!a ⊢ ${succ}`);
      assert.equal(r.kv, true, `kernel-verified: ${succ}`);
    }
  });

  it('SIGNAL  □a = νX.(a & ○X)  is available forever from persistent a (coinductive)', () => {
    // The headline FRP fact: from a persistent a, the signal is available every
    // tick — provable ONLY coinductively (a νR back-edge whose ○-branch advances
    // the persistent context across the tick). Finite search cannot.
    const finite = prover.prove(seq([], ['a'], 'nu X. (a & O X)'), { ...base, maxDepth: 200 });
    assert.equal(finite.success, false, 'no finite proof');
    const r = prove([], ['a'], 'nu X. (a & O X)');
    assert.equal(r.ok, true, 'coinductive proof succeeds');
    assert.equal(r.cycles, 1, 'exactly one back-edge');
    assert.equal(r.kv, true, 'kernel- + GTC-verified');
  });

  it('STREAM / EVENT  ◇a = μX.(a ⊕ ○X)  fires now  a ⊢ ◇a  (finite, kernel-verified)', () => {
    const r = prove(['a'], [], 'mu X. (a + O X)');
    assert.equal(r.ok, true);
    assert.equal(r.kv, true);
    assert.equal(r.cycles, 0, 'inductive: no back-edge');
  });

  it('a persistent signal of a signal:  !a ⊢ νX.(○a & ○X)  (both conjuncts advance)', () => {
    const r = prove([], ['a'], 'nu X. (O a & O X)');
    assert.equal(r.ok, true);
    assert.equal(r.kv, true);
  });

  it('SOUNDNESS under exhaustive search: ○ does not manufacture proofs', () => {
    // Exhaustive backtracking (the weakening-recovery driver) must still refuse
    // the genuinely unprovable ○ sequents.
    assert.equal(prove(['a'], [], 'O a', { exhaustive: true }).ok, false);
    assert.equal(prove(['O a'], [], 'a', { exhaustive: true }).ok, false);
    assert.equal(prove(['O a'], [], 'O O a', { exhaustive: true }).ok, false, '○a ⊬ ○○a (exhaustive)');
    // but the real proofs still go through exhaustively + kernel-verify
    assert.equal(prove([], ['a'], 'O a', { exhaustive: true }).kv, true);
    assert.equal(prove([], ['a'], 'nu X. (a & O X)', { exhaustive: true }).kv, true);
  });

  it('FIREWALL: ○ lives ONLY in rill — fill and ILL declare no circle', async () => {
    const fill = await loadFill();
    const ill = await loadILL();
    assert.ok(!fill.constructors.circle, 'fill has no ○ (μMALL core stays clean)');
    assert.ok(!ill.constructors.circle, 'ILL has no ○ (EVM path stays clean)');
    // and rill still inherits fill fully:
    assert.ok(calc.constructors.mu && calc.constructors.nu, 'rill inherits μ/ν from fill');
  });
});
