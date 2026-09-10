/**
 * Cyclic (co)inductive proofs (TODO_0009 rung 3, Inc-4) — where coinduction
 * lands. Under opt-in `opts.cyclicProofs`, the focused prover reinstates a
 * recurring ν-succedent sequent as a coinductive back-edge (a `nu_cycle` bud
 * leaf closing to its companion) instead of failing. The search is UNTRUSTED;
 * soundness is the TCB global trace condition (checkCyclicProof / checkGTC),
 * run post-search inside prove() AND inside kernel.verifyTree.
 *
 * Canonical example: νX.(A & X) = !A (Baelde 2012), so `!a ⊢ νX.(a & X)` is the
 * derelic­tion/availability of a signal — provable only coinductively (a cyclic
 * proof through νR). Pins: it fails without cyclicProofs, succeeds with, and the
 * proof kernel-verifies fully (the νR back-edge is GTC-certified); the μ
 * (inductive) loop stays conservatively refused; finite proofs are unaffected;
 * and the kernel rejects forged cycles (no companion / no progress).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import { createProver } from '../../lib/prover/focused.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { ProofTree } from '../../lib/prover/pt.js';
import { checkCyclicProof } from '../../lib/prover/gtc-check.js';
import { loadILL } from '../../calculus/ill/index.js';
import { buildForwardParser } from '../../calculus/ill/lib/forward-parser.js';

const countRule = (tree, name) => {
  let n = 0;
  const w = (t) => { if (!t) return; if (t.rule === name) n++; (t.premises || []).forEach(w); };
  w(tree); return n;
};

describe('cyclic proofs — coinduction via GTC-certified back-edges (Inc-4)', () => {
  let calc, fp, prover, kernel, base, gtcOpts;
  before(async () => {
    calc = await loadILL();
    fp = buildForwardParser();
    const built = buildRuleSpecs(calc);
    prover = createProver(calc);
    kernel = createKernel(calc);
    base = { rules: built.specs, alternatives: built.alternatives };
    gtcOpts = { roles: calc.roles, contextStructure: calc.contextStructure, canonicalize: calc.canonicalize };
  });
  // linear ctx, persistent ctx, succedent
  const seq = (lin, cart, succ) => Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ));

  it('!a ⊢ νX.(a & X) — coinductive signal: fails plain, succeeds cyclic', () => {
    const g = () => seq([], ['a'], 'nu X. (a & X)');
    assert.equal(prover.prove(g(), { ...base, maxDepth: 200 }).success, false,
      'no finite proof (would grind forever without loop detection)');
    const r = prover.prove(g(), { ...base, maxDepth: 200, cyclicProofs: true });
    assert.equal(r.success, true, 'coinductive proof succeeds');
    assert.equal(countRule(r.proofTree, 'nu_cycle'), 1, 'closes via one coinductive back-edge');
  });

  it('the coinductive proof is FULLY kernel-verified (νR back-edge GTC-certified)', () => {
    const r = prover.prove(seq([], ['a'], 'nu X. (a & X)'), { ...base, maxDepth: 200, cyclicProofs: true });
    const v = kernel.verifyTree(r.proofTree);
    assert.equal(v.valid, true, `kernel accepts (${v.errors[0] || ''})`);
    assert.ok(!v.unverified || v.unverified.length === 0, 'no unverified residue');
    // the reconstructed back-edge carries a progressing νR step
    const cp = checkCyclicProof(r.proofTree, gtcOpts);
    assert.equal(cp.valid, true);
    assert.equal(cp.backEdges.length, 1);
    assert.ok(cp.backEdges[0].ruleNames.includes('nu_r'), 'progress is a νR unfold');
  });

  it('a two-signal body !a,!b ⊢ νX.(a & (b & X)) proves coinductively', () => {
    const r = prover.prove(seq([], ['a', 'b'], 'nu X. (a & (b & X))'), { ...base, maxDepth: 300, cyclicProofs: true });
    assert.equal(r.success, true);
    assert.equal(kernel.verifyTree(r.proofTree).valid, true);
  });

  it('a stream body νX.(a * X) is NOT provable from finite/persistent-less resources', () => {
    // tensor body demands a fresh linear `a` every tick — unavailable ⇒ fails
    // even coinductively (the a-branch of tensor_r is unprovable).
    assert.equal(prover.prove(seq([], [], 'nu X. (a * X)'), { ...base, maxDepth: 200, cyclicProofs: true }).success, false);
  });

  it('μ (inductive) loops stay conservatively refused under cyclicProofs', () => {
    // succedent I is not ν → no nu_cycle emitted → the loop fails (sound).
    assert.equal(prover.prove(seq(['mu X. X'], [], 'I'), { ...base, cyclicProofs: true }).success, false);
  });

  it('finite proofs are unaffected by cyclicProofs', () => {
    for (const [lin, succ] of [[['mu X. (a & X)'], 'a'], [[], 'mu X. (I + X)'], [['a -o b', 'a'], 'b']]) {
      assert.equal(prover.prove(seq(lin, [], succ), { ...base, cyclicProofs: true }).success, true, `${succ}`);
    }
  });

  it('the kernel rejects a nu_cycle bud with no matching companion ancestor', () => {
    const C = seq([], [], 'nu X. (a & X)');
    const lone = new ProofTree({ conclusion: C, rule: 'nu_cycle', proven: true, premises: [] });
    const v = kernel.verifyTree(lone);
    assert.equal(v.valid, false);
    assert.match(v.errors.join(' '), /companion/);
  });

  it('the kernel rejects a cycle with NO progressing step (structural-only loop)', () => {
    const C = seq([], [], 'nu X. (a & X)');
    const bud = new ProofTree({ conclusion: C, rule: 'nu_cycle', proven: true, premises: [] });
    // with_r companion → nu_cycle: the cycle rule set is {with_r}, no νR ⇒ reject.
    const forged = new ProofTree({ conclusion: C, rule: 'with_r', proven: true, premises: [bud, bud] });
    const v = kernel.verifyTree(forged);
    assert.equal(v.valid, false);
    assert.match(v.errors.join(' '), /progressing thread/);
  });
});
