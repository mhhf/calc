/**
 * rill — the ○ next-time modality (TODO_0203, THY_0042). rill = fill + ○, the
 * reactive/FRP layer forked out of fill to firewall the soundness-subtle temporal
 * machinery from the audited μMALL core (as fill firewalls μMALL from ILL).
 *
 * ○A = "A at the NEXT tick, not now." Its rule is the whole-context TICK
 * (G ; ○Δ |- ○C <- G ; Δ |- C, THY_0043 §temporal-cut): it fires only when every
 * consumable formula is ○-wrapped, strips one ○ from each, and advances the whole
 * sequent one step. The empty-Δ case is the promotion-shaped base (only persistent
 * resources / a signal tail advance). Because the tick needs an ○-succedent AND an
 * all-○ context, ○ does NOT collapse (○a ⊬ a, a ⊬ ○a) — yet signals are now
 * CONSUMED: the applicative ○(a⊸b),○a ⊢ ○b and lax-monoidal ○a,○b ⊢ ○(a⊗b) hold
 * (○-elimination / temporal cut). Guarded signals νX.(A & ○X) coinduct via the ν
 * back-edge (the GTC needs no change — ○ is the syntactic guard, νR is the trace
 * progress). All proofs below are kernel- and GTC-verified (the kernel re-derives
 * the tick — succedent ○C, all-○ pool, premise = stripped context — never trusts it).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import Store from '../../lib/kernel/store.js';
import { createProver } from '../../lib/prover/focused.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { ProofTree } from '../../lib/prover/pt.js';
import { freshMetavar } from '../../lib/kernel/fresh.js';
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
  });

  it('○-ELIMINATION / temporal cut: the whole-context tick advances ○Δ ⊢ ○C to Δ ⊢ C', () => {
    // The tick (○R generalized, THY_0043 §temporal-cut) consumes signals, not only
    // produces them. It fires ONLY when every consumable formula is ○-wrapped, so
    // non-collapse (above) is preserved while these become provable + kernel-valid:
    const applicative = prove(['O (a -o b)', 'O a'], [], 'O b');   // the ⊛ combinator
    assert.equal(applicative.ok, true, '○(a⊸b), ○a ⊢ ○b (applicative)');
    assert.equal(applicative.kv, true, 'kernel-verified: the tick is re-derived, not trusted');
    const monoidal = prove(['O a', 'O b'], [], 'O (a * b)');       // lax monoidal
    assert.equal(monoidal.ok, true, '○a, ○b ⊢ ○(a⊗b) (lax monoidal)');
    assert.equal(monoidal.kv, true);
    for (const g of ['O a', 'O O a']) {                            // functoriality of ○
      const r = prove([g], [], g);
      assert.equal(r.ok, true, `${g} ⊢ ${g} (○ functorial)`); assert.equal(r.kv, true);
    }
    // temporal cut also works under exhaustive search (the CPS twin):
    const exh = prove(['O (a -o b)', 'O a'], [], 'O b', { exhaustive: true });
    assert.equal(exh.ok, true, 'applicative under exhaustive'); assert.equal(exh.kv, true);
  });

  it('TCB FENCE: the kernel REJECTS a forged tick (it re-derives, never trusts, the step)', () => {
    // A genuine proof of a ⊢ a — a legitimately-proven subtree...
    const inner = prover.prove(seq(['a'], [], 'a'), { ...base, maxDepth: 20 });
    assert.equal(inner.success, true);
    // (the tick's spec key is circle_r — specKey maps next_r → connective_side)
    // (i) ...wrapped as a bogus tick claiming ○a ⊢ ○b: pool [○a] strips to [a], the
    // premise a ⊢ a is real, but its succedent a ≠ the ○-body b. Kernel must reject.
    const wrongBody = new ProofTree({
      conclusion: seq(['O a'], [], 'O b'), premises: [inner.proofTree], rule: 'circle_r', proven: true,
    });
    const v1 = kernel.verifyTree(wrongBody);
    assert.equal(v1.valid, false, 'kernel rejects premise-succedent ≠ ○-body');
    assert.ok(v1.errors.some(e => /body|circle|tick|succedent/i.test(e)));
    // (ii) a tick whose conclusion pool holds a NON-○ formula (c) must be rejected —
    // the guard that keeps ○ non-collapsing lives in the TCB, not only in the search.
    const nonCircle = new ProofTree({
      conclusion: seq(['c'], [], 'O a'), premises: [inner.proofTree], rule: 'circle_r', proven: true,
    });
    const v2 = kernel.verifyTree(nonCircle);
    assert.equal(v2.valid, false, 'kernel rejects a non-○ formula riding the tick');
    assert.ok(v2.errors.some(e => /circle|wrapped|advance|tick/i.test(e)));
    // (iii) METAVAR forgery (audit 2026-09-11): a premise with a metavar succedent
    // X — a real id leaf `a ⊢ X` unifies a=X, and the tick body check must NOT
    // independently unify X=b (two fresh unions never reconciled). The tick body
    // check is EXACT (ps === C), so this forged ○a ⊢ ○b is rejected.
    const idMeta = new ProofTree({
      conclusion: Seq.fromArrays([fp('a')], [], freshMetavar()), rule: 'id', proven: true, premises: [],
    });
    const metaForge = new ProofTree({
      conclusion: seq(['O a'], [], 'O b'), premises: [idMeta], rule: 'circle_r', proven: true,
    });
    const v3 = kernel.verifyTree(metaForge);
    assert.equal(v3.valid, false, 'kernel rejects a metavar-premise tick forging ○a ⊢ ○b');
    assert.ok(v3.errors.some(e => /body|circle|succedent/i.test(e)));
  });

  it('○ is STRONG MONOIDAL over ⊗ (sound feature) — the tick distributes, without leaking', () => {
    // With the whole-context tick, ○ is a STRONG monoidal functor for the
    // time-shift reading: ○(A⊗B) and ○A⊗○B are the SAME resource multiset (A,B
    // both at t+1), so both directions hold. The leftover re-wrap (wrapTick) is
    // linear accounting — the part of ○Δ a branch does not consume passes on as ○
    // of that part — NOT duplication. Audit 2026-09-11: two attackers read this as
    // a soundness hole assuming lax-only monoidality; it is sound, pinned here.
    for (const [lin, succ] of [
      [['O (a * b)'], '(O a) * (O b)'],           // distribute (strong)
      [['O a', 'O b'], 'O (a * b)'],               // gather (lax)
      [['O (a * b)'], '(O b) * (O a)'],            // + commutativity
      [['O (a * b)', 'O c'], '(O a) * ((O b) * (O c))'],
    ]) {
      const r = prove(lin, [], succ);
      assert.equal(r.ok, true, `valid: ${JSON.stringify(lin)} ⊢ ${succ}`);
      assert.equal(r.kv, true, 'kernel-verified');
    }
    // ...and the strong-monoidal machinery leaks NOTHING: no duplication, creation,
    // over-extraction, or discard rides the leftover re-wrap.
    assert.equal(prove(['O a'], [], '(O a) * (O a)').ok, false, 'no duplication ○a ⊬ ○a⊗○a');
    assert.equal(prove([], [], '(O a) * (O b)').ok, false, 'no creation ⊬ ○a⊗○b');
    assert.equal(prove(['O (a * b)'], [], '(O a) * ((O b) * (O b))').ok, false, 'no over-extraction');
    assert.equal(prove(['O (a * b)'], [], 'O a').ok, false, 'no discard: b cannot be dropped (○b leftover fails root)');
  });

  it('○-ELIMINATION is SOUND: the tick manufactures nothing and never collapses', () => {
    // A non-○ linear resource cannot ride the tick (would silently advance it):
    assert.equal(prove(['O a', 'b'], [], 'O b').ok, false, '○a, b ⊬ ○b (b is not ○-wrapped)');
    // the tick cannot duplicate a linear resource across the step:
    assert.equal(prove(['O a'], [], 'O (a * a)').ok, false, '○a ⊬ ○(a⊗a)');
    // and cannot invent a resource:
    assert.equal(prove(['O a'], [], 'O b').ok, false, '○a ⊬ ○b');
    assert.equal(prove(['O a'], [], 'O (a * b)').ok, false, '○a ⊬ ○(a⊗b)');
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
