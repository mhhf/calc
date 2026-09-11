/**
 * μ/ν soundness fences + reconstruction pins (TODO_0009 audit 2026-09-11).
 *
 * The audit found one LATENT soundness gap and its enabler: the lax-monad
 * bridge (bridge.js rightFocus/rightFocusTerm) treated a μ/ν succedent as an
 * opaque atom to consume from the forward residual, and nothing stopped a
 * forward rule from PRODUCING a μ/ν token — together, a forward-produced
 * fixpoint could close a coinductive monad goal with no proof. Two defenses,
 * pinned here:
 *   (1) a load-time fence: μ/ν may not appear in a forward rule (convert.js);
 *   (2) the TCB gate: rightFocus/rightFocusTerm REFUSE μ/ν succedents by role.
 * Either alone closes the hole; both together are the belt-and-suspenders TCB
 * discipline. Also pinned: 'nu_cycle' is a machinery-reserved rule name, and
 * checkCyclicProof rejects a REAL cyclic proof whose progress step is defaced.
 */
import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import Store from '../../lib/kernel/store.js';
import Seq from '../../lib/kernel/sequent.js';
import bridge from '../../lib/prover/bridge.js';
import { ProofTree } from '../../lib/prover/pt.js';
import { createProver } from '../../lib/prover/focused.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { checkCyclicProof } from '../../lib/prover/gtc-check.js';
import { RESERVED_RULE_NAMES } from '../../lib/engine/reserved-preds.js';
import calcLoader from '../../lib/calculus/index.js';
import { load as fillLoad, loadFill } from '../../calculus/fill/index.js';
import { buildForwardParser } from '../../calculus/fill/lib/forward-parser.js';

// μ/ν live in fill now (fill.calc @extends ill), so fixpoint-bearing loads go
// through fill. ILL's paths are kept for the reserved-name test below — it is
// a calculus-agnostic loader fence, and exercising it on post-extraction ILL
// doubles as a "plain ILL still loads clean" probe.
const ILL_CALC = path.join(import.meta.dirname, '../../calculus/ill/ill.calc');
const ILL_RULES = path.join(import.meta.dirname, '../../calculus/ill/ill.rules');

describe('μ/ν forward-rule soundness fence (audit 2026-09-11)', () => {
  let dir;
  before(() => { dir = fs.mkdtempSync(path.join(os.tmpdir(), 'munu-fence-')); });
  after(() => { try { fs.rmSync(dir, { recursive: true, force: true }); } catch {} });
  const write = (name, src) => { const p = path.join(dir, name); fs.writeFileSync(p, src); return p; };

  it('rejects a fixpoint connective in a forward-rule CONSEQUENT at load', () => {
    const p = write('conseq.ill', 'a: type.\nbad: a -o { nu X. (a & X) }.\n');
    assert.throws(() => fillLoad(p), /fixpoint connective.*forward|forward rule.*fixpoint/i);
  });

  it('rejects a fixpoint connective in a forward-rule ANTECEDENT at load', () => {
    const p = write('ante.ill', 'a: type.\nbad2: (mu X. (a + X)) -o { a }.\n');
    assert.throws(() => fillLoad(p), /fixpoint connective|backward-proof/i);
  });

  it('a fixpoint-free forward rule still loads (fence does not over-reject)', () => {
    const p = write('ok.ill', 'a: type.\nok: a -o { a }.\n');
    assert.doesNotThrow(() => fillLoad(p));
  });
});

describe('lax-monad bridge refuses μ/ν succedents (TCB gate)', () => {
  let roles, fp;
  before(async () => { const calc = await loadFill(); roles = calc.roles; fp = buildForwardParser(); });

  it('rightFocus/rightFocusTerm return null for a ν succedent even when the token is in linear state', () => {
    const nu = fp('nu X. (a & X)');
    assert.equal(bridge.rightFocus({ [nu]: 1 }, {}, nu, roles), null);
    assert.equal(bridge.rightFocusTerm({ [nu]: 1 }, {}, nu, roles), null);
  });

  it('rightFocus/rightFocusTerm return null for a μ succedent', () => {
    const mu = fp('mu X. (a + X)');
    assert.equal(bridge.rightFocus({ [mu]: 1 }, {}, mu, roles), null);
    assert.equal(bridge.rightFocusTerm({ [mu]: 1 }, {}, mu, roles), null);
  });

  it('a plain atom is still consumed from linear (fence does not break the normal path)', () => {
    const a = fp('a');
    assert.deepEqual(bridge.rightFocus({ [a]: 1 }, {}, a, roles), {});
    const t = bridge.rightFocusTerm({ [a]: 1 }, {}, a, roles);
    assert.ok(t && t.term && t.term.rule === 'id');
  });
});

describe("'nu_cycle' is a machinery-reserved rule name", () => {
  let dir;
  before(() => { dir = fs.mkdtempSync(path.join(os.tmpdir(), 'munu-resv-')); });
  after(() => { try { fs.rmSync(dir, { recursive: true, force: true }); } catch {} });

  it('exports nu_cycle in RESERVED_RULE_NAMES', () => {
    assert.ok(RESERVED_RULE_NAMES.has('nu_cycle'));
  });

  it('the loader rejects a calculus that declares a rule named nu_cycle', () => {
    const rp = path.join(dir, 'collide.rules');
    fs.writeFileSync(rp, '@formulas A, B, C\n\nnu_cycle: ; A |- A\n  @invertible true.\n');
    assert.throws(() => calcLoader.load(ILL_CALC, [ILL_RULES, rp]), /machinery-reserved rule name/);
  });
});

describe('μ/ν × lax monad: {νX.A} is not provable via cyclic proof (sound, documented gap)', () => {
  let fp, prover, base;
  before(async () => {
    const calc = await loadFill();
    fp = buildForwardParser();
    const built = buildRuleSpecs(calc);
    prover = createProver(calc);
    base = { rules: built.specs, alternatives: built.alternatives };
  });
  it('!a ⊢ {νX.(a & X)} FAILS even with cyclicProofs (the bud needs a ν succedent, not a monad one)', () => {
    // After monad_r the succedent is monad-tagged, so no nu_cycle bud is emitted;
    // the goal correctly fails (never a false accept). Architectural completeness
    // limitation — bare ν coinduction crosses no monad bridge. Pinned so a future
    // change cannot turn it into an UNSOUND success.
    const g = Seq.fromArrays([], [fp('a')], fp('{ nu X. (a & X) }'));
    assert.equal(prover.prove(g, { ...base, maxDepth: 200, cyclicProofs: true }).success, false);
  });
});

describe('checkCyclicProof reconstruction rejects a defaced REAL cyclic proof (whole-tree)', () => {
  let calc, fp, prover, gtcOpts;
  before(async () => {
    calc = await loadFill();
    fp = buildForwardParser();
    prover = createProver(calc);
    const built = buildRuleSpecs(calc);
    prover._base = { rules: built.specs, alternatives: built.alternatives };
    gtcOpts = { roles: calc.roles, contextStructure: calc.contextStructure, canonicalize: calc.canonicalize };
  });
  const deepClone = (t) => t && new ProofTree({
    conclusion: t.conclusion, rule: t.rule, proven: t.proven,
    premises: (t.premises || []).map(deepClone),
  });
  const relabel = (t, from, to) => { if (!t) return; if (t.rule === from) t.rule = to; (t.premises || []).forEach(k => relabel(k, from, to)); };

  it('the genuine proof validates, but relabelling its νR progress step is REJECTED', () => {
    const g = Seq.fromArrays([], [fp('a')], fp('nu X. (a & X)'));
    const r = prover.prove(g, { ...prover._base, maxDepth: 200, cyclicProofs: true });
    assert.equal(r.success, true, 'baseline coinductive proof exists');
    // (i) the real tree passes reconstruction + GTC
    assert.equal(checkCyclicProof(r.proofTree, gtcOpts).valid, true);
    // (ii) deface the sole progress step (νR → a non-fixpoint rule): reconstruction
    // reads rule names from the tree, finds no νR-on-ν / μL-on-μ step → REJECT.
    const defaced = deepClone(r.proofTree);
    relabel(defaced, 'nu_r', 'with_r');
    const v = checkCyclicProof(defaced, gtcOpts);
    assert.equal(v.valid, false, 'no progressing thread after defacing νR');
    assert.ok(v.errors.some(e => /progress/i.test(e)));
  });
});
