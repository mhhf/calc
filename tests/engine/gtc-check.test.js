/**
 * TCB Global Trace Condition checker (TODO_0009 rung 3, Inc-3).
 *
 * checkGTC is trusted (a soundness hole here is a soundness hole in every
 * cyclic proof), so it is tested IN ISOLATION on hand-crafted back-edge records
 * — no search involved — exactly the SAX explicit-cut precedent (the kernel
 * checker is adversarially exercised before the untrusted search feeds it).
 *
 * These pins are the three canonical soundness holes from the theorem plus the
 * theory-modulo corner: (H-progress) a cycle with no νR/μL unfold; (H-side) the
 * WRONG side (μR / νL) claimed as progress; (H-resource) linear resources not
 * conserved across the back-edge; (H-succ) a different succedent; and the
 * positive controls (valid ν-cycle, nested μL+νR, theory-equal contexts).
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import { checkGTC } from '../../lib/prover/gtc-check.js';
import { loadFill } from '../../calculus/fill/index.js';
import { buildForwardParser } from '../../calculus/fill/lib/forward-parser.js';

describe('checkGTC — TCB cyclic-proof validity (Inc-3)', () => {
  let calc, fp, opts;
  before(async () => {
    calc = await loadFill();
    fp = buildForwardParser();
    // roles.lfp/gfp identify μ/ν by tag; contextStructure locates the linear pool.
    opts = { roles: calc.roles, contextStructure: calc.contextStructure, canonicalize: calc.canonicalize };
  });
  // sequent from linear + succedent formula strings (persistent empty)
  const S = (lin, succ) => Seq.fromArrays(lin.map(fp), [], fp(succ));
  const nuF = () => fp('nu X. (a & X)');
  const muF = () => fp('mu X. (a & X)');

  it('accepts a valid ν-cycle (νR unfold, contexts conserved)', () => {
    const C = S([], 'nu X. (a & X)');
    const be = { bud: C, companion: C, ruleNames: ['nu_r'], principals: [nuF()] };
    const r = checkGTC([be], opts);
    assert.equal(r.valid, true, r.errors.join('; '));
  });

  it('accepts a nested cycle carrying BOTH μL and νR progress steps', () => {
    const C = S(['mu X. (a & X)'], 'nu X. (a & X)');
    const be = { bud: C, companion: C, ruleNames: ['mu_l', 'with_l1', 'nu_r'], principals: [muF(), 0, nuF()] };
    assert.equal(checkGTC([be], opts).valid, true);
  });

  it('REJECTS a cycle with no progressing step (H-progress)', () => {
    const C = S([], 'nu X. (a & X)');
    const be = { bud: C, companion: C, ruleNames: ['with_r', 'id'], principals: [nuF(), 0] };
    const r = checkGTC([be], opts);
    assert.equal(r.valid, false);
    assert.match(r.errors.join(' '), /no progressing thread/);
  });

  it('REJECTS the WRONG side: μR (not μL) claimed as progress (H-side)', () => {
    const C = S([], 'mu X. (a & X)');
    const be = { bud: C, companion: C, ruleNames: ['mu_r'], principals: [muF()] };
    assert.equal(checkGTC([be], opts).valid, false);
  });

  it('REJECTS the WRONG side: νL (not νR) claimed as progress (H-side)', () => {
    const C = S(['nu X. (a & X)'], 'c');
    const be = { bud: C, companion: C, ruleNames: ['nu_l'], principals: [nuF()] };
    assert.equal(checkGTC([be], opts).valid, false);
  });

  it('REJECTS a νR step whose recorded principal is NOT a ν-formula (forged record)', () => {
    const C = S([], 'nu X. (a & X)');
    const be = { bud: C, companion: C, ruleNames: ['nu_r'], principals: [fp('a')] }; // atom, not ν
    assert.equal(checkGTC([be], opts).valid, false);
  });

  it('REJECTS a resource NOT conserved across the back-edge (H-resource)', () => {
    // valid νR progress, but the bud dropped a linear `b` the companion held.
    const companion = S(['b'], 'nu X. (a & X)');
    const bud = S([], 'nu X. (a & X)');
    const be = { bud, companion, ruleNames: ['nu_r'], principals: [nuF()] };
    const r = checkGTC([be], opts);
    assert.equal(r.valid, false);
    assert.match(r.errors.join(' '), /context conservation/);
  });

  it('REJECTS a different succedent across the back-edge (H-succ)', () => {
    const companion = S([], 'nu X. (a & X)');
    const bud = S([], 'nu X. (b & X)');
    const be = { bud, companion, ruleNames: ['nu_r'], principals: [nuF()] };
    const r = checkGTC([be], opts);
    assert.equal(r.valid, false);
    assert.match(r.errors.join(' '), /succedent differs/);
  });

  it('compares contexts MODULO THEORY, not by raw hash (state-canonicity)', () => {
    // Two distinct hashes the theory equates must NOT trip context conservation.
    const h1 = fp('a'), h2 = fp('b');
    const canon = (h) => (h === h2 ? h1 : h);           // theory: b ≡ a (test stub)
    const companion = Seq.fromArrays([h1], [], nuF());
    const bud = Seq.fromArrays([h2], [], nuF());          // b instead of a
    const be = { bud, companion, ruleNames: ['nu_r'], principals: [nuF()] };
    assert.equal(checkGTC([be], { ...opts, canonicalize: canon }).valid, true,
      'theory-equal contexts must be accepted');
    // control: without the theory, raw hashes differ → rejected
    assert.equal(checkGTC([be], { ...opts, canonicalize: null }).valid, false);
  });

  it('validates ALL back-edges — one bad edge fails the whole certificate', () => {
    const good = { bud: S([], 'nu X. (a & X)'), companion: S([], 'nu X. (a & X)'), ruleNames: ['nu_r'], principals: [nuF()] };
    const bad = { bud: S([], 'nu X. (a & X)'), companion: S([], 'nu X. (a & X)'), ruleNames: ['id'], principals: [0] };
    assert.equal(checkGTC([good], opts).valid, true);
    assert.equal(checkGTC([good, bad], opts).valid, false);
  });
});
