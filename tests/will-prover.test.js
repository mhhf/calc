/**
 * will sequent calculus — the ∃_ρ fragment by draw-token internalization
 * (TODO_0298 item 1; THY_0027).
 *
 * Backward provability over will.rules' three will-own rules:
 *   drawn_l      ∃_ρ-R(c) — consume a `drawn c s` token, witness the
 *                superposed existential with the token's member
 *   drawn_l2     ghost — weakening restricted to the token class
 *                (@affine: inserted by the prover at search boundaries)
 *   superpose_l  ∃-L — the standard eigenvariable rule
 *
 * Pins the THEOREMS of THY_0027 as executable facts:
 *   - weight lives in the endsequent: no token, no ∃_ρ (§1/§2)
 *   - witness = the token's member; member and sort mismatches refuted (§2)
 *   - ghost discharges tokens at the root, in additive branches (§3h
 *     lockstep-by-sharing + ghost), and before promotion — but NEVER
 *     leaks ordinary linear resources (§5)
 *   - no promotion through a draw: the token itself is not bangable (§3e)
 *   - ∃-L's eigenvariable cannot leak a witness (soundness)
 *   - bang_r3 requires an empty linear zone (the §3f′ audit repair)
 * Every found derivation passes the L1 kernel checker; only genuine
 * eigenvariable steps may report unverified:['binding'] (the standard
 * ILL exists_l degradation).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import Store from '../lib/kernel/store.js';
import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import { loadWillSequent } from '../calculus/will/calculus-config.js';

describe('will sequent calculus — ∃_ρ by draw-token internalization', () => {
  let calc, specs, alternatives, prover, kernel, P;

  before(() => {
    calc = loadWillSequent();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc);
    kernel = createKernel(calc);
    P = (s) => calc.parse(s);
  });

  // Lazy builders (hashes are interned inside it() bodies, after load)
  const atom = (n) => Store.put('atom', [n]);
  const bound0 = () => Store.put('bound', [0n]);
  const p = (x) => Store.put('p', [x]);
  const sup = (s, body) => Store.put('superpose', [atom(s), Store.put('exists', [body])]);
  const drawn = (c, s) => Store.put('drawn', [atom(c), atom(s)]);
  const tensor = (a, b) => Store.put('tensor', [a, b]);
  const withc = (a, b) => Store.put('with', [a, b]);
  const oplus = (a, b) => Store.put('oplus', [a, b]);
  const one = () => Store.put('one', []);

  const prove = (linear, succ, cart = []) =>
    prover.prove(Seq.fromArrays(linear, cart, succ), { rules: specs, alternatives });

  // mk builds [linear, succ, cart?] lazily; expectBinding allows the
  // standard eigenvariable degradation flag
  const provable = (desc, mk, { expectBinding = false } = {}) => it(desc, () => {
    const [linear, succ, cart] = mk();
    const r = prove(linear, succ, cart);
    assert.ok(r.success, `expected provable: ${desc}`);
    const v = kernel.verifyTree(r.proofTree);
    assert.ok(v.valid, `kernel rejected ${desc}: ${v.errors.join('; ')}`);
    if (expectBinding) assert.deepEqual(v.unverified, ['binding'], desc);
    else assert.equal(v.unverified, undefined, `unexpected unverified steps in ${desc}`);
  });
  const refuted = (desc, mk) => it(desc, () => {
    const [linear, succ, cart] = mk();
    assert.ok(!prove(linear, succ, cart).success, `expected refuted: ${desc}`);
  });

  it('setup sanity: the will-own rules load with the right shapes', () => {
    for (const n of ['drawn_l', 'drawn_l2', 'superpose_l', 'draw']) {
      assert.ok(calc.rules[n], `missing rule ${n}`);
    }
    assert.ok(specs.drawn_l && specs.drawn_l2 && specs.superpose_l);
    assert.ok(alternatives.drawn_l.includes('drawn_l2'));
    assert.equal(specs.drawn_l2.affine, true);
    assert.equal(specs.drawn_l._bindingMode, 'witness');
    assert.equal(specs.superpose_l._bindingMode, 'eigenvariable');
  });

  describe('∃_ρ-R (drawn_l): token discipline', () => {
    provable('gold, drawn c s ⊢ ∃ρX:s. gold',
      () => [[atom('gold'), drawn('c', 's')], sup('s', atom('gold'))]);
    refuted('no token ⟹ no ∃_ρ (weight lives in the endsequent)',
      () => [[atom('gold')], sup('s', atom('gold'))]);
    provable('witness substitution: p c, drawn c s ⊢ ∃ρX:s. p X',
      () => [[p(atom('c')), drawn('c', 's')], sup('s', p(bound0()))]);
    refuted('member mismatch: p d, drawn c s ⊬ ∃ρX:s. p X',
      () => [[p(atom('d')), drawn('c', 's')], sup('s', p(bound0()))]);
    refuted('sort mismatch: p c, drawn c s2 ⊬ ∃ρX:s. p X',
      () => [[p(atom('c')), drawn('c', 's2')], sup('s', p(bound0()))]);
    provable('token splits through ⊗ to the branch that needs it',
      () => [[atom('gold'), atom('silver'), drawn('c', 's')],
        tensor(atom('gold'), sup('s', atom('silver')))]);
    provable('1 ⊗ ∃ρ: the unit branch threads the token on',
      () => [[atom('silver'), drawn('c', 's')],
        tensor(one(), sup('s', atom('silver')))]);
    provable('two tokens: one ∃_ρ-R, one ghost',
      () => [[atom('gold'), drawn('c', 's'), drawn('c', 's')], sup('s', atom('gold'))]);
  });

  describe('ghost (drawn_l2): tokens are affine, Δ proper stays linear', () => {
    provable('root discharge: gold, drawn c s ⊢ gold',
      () => [[atom('gold'), drawn('c', 's')], atom('gold')]);
    provable('drawn c s ⊢ I (ghost then 1R)',
      () => [[drawn('c', 's')], one()]);
    provable('token id: drawn c s ⊢ drawn c s',
      () => [[drawn('c', 's')], drawn('c', 's')]);
    refuted('ghost never leaks ordinary resources: a, b ⊬ a',
      () => [[atom('a'), atom('b')], atom('a')]);
    provable('additive balancing (§3h): drawn, p c ⊢ (∃ρX. p X) & p c',
      () => [[drawn('c', 's'), p(atom('c'))], withc(sup('s', p(bound0())), p(atom('c')))]);
    provable('both branches ghost: drawn ⊢ I & I',
      () => [[drawn('c', 's')], withc(one(), one())]);
    refuted('balancing repairs tokens only: drawn, p c ⊬ (∃ρX. p X) & I',
      () => [[drawn('c', 's'), p(atom('c'))], withc(sup('s', p(bound0())), one())]);
    refuted('no additive leak of ordinary resources: a, b ⊬ a & a',
      () => [[atom('a'), atom('b')], withc(atom('a'), atom('a'))]);
  });

  describe('ghost-free ⊋ ⊆-minimal (paper Cor. 5.3, &-left form)', () => {
    // (p c) & (∃ρX.pX) ⊢ ∃ρX.pX has TWO ghost-free proofs at different
    // traces: Θ={c} via &L₁ + ∃ρR(c), and Θ=∅ via &L₂ + id — the id at
    // ∃_ρ is the SYNTHETIC-ATOM identity (§4: no expansion exists)
    provable('with token: (p c) & (∃ρX.pX), drawn c s ⊢ ∃ρX.pX',
      () => [[withc(p(atom('c')), sup('s', p(bound0()))), drawn('c', 's')],
        sup('s', p(bound0()))]);
    provable('without token: (p c) & (∃ρX.pX) ⊢ ∃ρX.pX (id at the synthetic atom)',
      () => [[withc(p(atom('c')), sup('s', p(bound0())))],
        sup('s', p(bound0()))]);
    refuted('the &L₁ branch alone needs the token: p c ⊬ ∃ρX.pX',
      () => [[p(atom('c'))], sup('s', p(bound0()))]);
    // the ⊕-right form (surface ⊕ is gill/will-only; till keeps woplus)
    provable('⊕-form at the empty trace: q ⊢ (∃ρX.pX) + q (+R₂)',
      () => [[atom('q')], oplus(sup('s', p(bound0())), atom('q'))]);
    provable('⊕-form at trace {c}: p c, drawn c s ⊢ (∃ρX.pX) + q (+R₁, ∃ρR)',
      () => [[p(atom('c')), drawn('c', 's')], oplus(sup('s', p(bound0())), atom('q'))]);
    provable('⊕L elim: a + a ⊢ a (both branches close)',
      () => [[oplus(atom('a'), atom('a'))], atom('a')]);
    refuted('⊕L needs both branches: a + b ⊬ a',
      () => [[oplus(atom('a'), atom('b'))], atom('a')]);
  });

  describe('∃-L (superpose_l): the eigenvariable rule', () => {
    provable('binder-free body: superpose(s, ∃X. a) ⊢ a',
      () => [[sup('s', atom('a'))], atom('a')]);
    provable('eigenvariable used opaquely: sup(∃X. pX ⊗ (pX ⊸ gold)) ⊢ gold',
      () => [[sup('s', tensor(p(bound0()), Store.put('loli', [p(bound0()), atom('gold')])))],
        atom('gold')],
      { expectBinding: true });
    refuted('eigenvariable soundness: sup(s, ∃X. p X) ⊬ p c',
      () => [[sup('s', p(bound0()))], p(atom('c'))]);
  });

  describe('splitting laws are structural (THY_0029 — T4-d(ii) dissolution)', () => {
    const bin = (n) => Store.put('binlit', [BigInt(n)]);
    const bangK = (k, a) => Store.put('bang', [bin(k), a]);
    // Leg (i): counts split additively via the counted bang — with exact
    // conservation (leak and mint both refuted)
    provable('!_5 a ⊢ !_2 a ⊗ !_3 a (count splitting)',
      () => [[bangK(5, atom('a'))], tensor(bangK(2, atom('a')), bangK(3, atom('a')))]);
    provable('!_2 a ⊗ !_3 a ⊢ !_5 a (merge converse)',
      () => [[tensor(bangK(2, atom('a')), bangK(3, atom('a')))], bangK(5, atom('a'))]);
    refuted('no count leak: !_5 a ⊬ !_2 a ⊗ !_2 a',
      () => [[bangK(5, atom('a'))], tensor(bangK(2, atom('a')), bangK(2, atom('a')))]);
    refuted('no count mint: !_4 a ⊬ !_2 a ⊗ !_3 a',
      () => [[bangK(4, atom('a'))], tensor(bangK(2, atom('a')), bangK(3, atom('a')))]);
    // Leg (ii): masses factorize multiplicatively — the token multiset
    // partitions across ⊗-premises; one token cannot serve two channels
    provable('token partition: p c, p d, drawn c s, drawn d s ⊢ (∃ρX.pX) ⊗ (∃ρX.pX)',
      () => [[p(atom('c')), p(atom('d')), drawn('c', 's'), drawn('d', 's')],
        tensor(sup('s', p(bound0())), sup('s', p(bound0())))]);
    refuted('no cloning: p c, p c, drawn c s ⊬ (∃ρX.pX) ⊗ (∃ρX.pX)',
      () => [[p(atom('c')), p(atom('c')), drawn('c', 's')],
        tensor(sup('s', p(bound0())), sup('s', p(bound0())))]);
    // §3: the box is the endsequent in disguise — tokens reassociate
    // freely over ⊗
    provable('token reassociation: t_c ⊗ (t_d ⊗ a) ⊢ (t_c ⊗ t_d) ⊗ a',
      () => [[tensor(drawn('c', 's'), tensor(drawn('d', 's'), atom('a')))],
        tensor(tensor(drawn('c', 's'), drawn('d', 's')), atom('a'))]);
    // §5: the synthetic-atom id repair the mass leg forced — provability
    // must not depend on ⊗-premise order
    provable('synthetic-atom id with leftovers: p c, a ⊢ p c ⊗ a',
      () => [[p(atom('c')), atom('a')], tensor(p(atom('c')), atom('a'))]);
    provable('token id in premise 1: drawn c s, a ⊢ drawn c s ⊗ a',
      () => [[drawn('c', 's'), atom('a')], tensor(drawn('c', 's'), atom('a'))]);
  });

  describe('structural theorems of THY_0027', () => {
    refuted('no promotion through a draw: drawn c s ⊬ !(drawn c s)',
      () => [[drawn('c', 's')], P('!(drawn c s)')]);
    provable('ghost before promotion: a ; drawn c s ⊢ !a (outcomes are bangable, the luck is not)',
      () => [[drawn('c', 's')], P('!a'), [atom('a')]]);
    // count-zero is binlit 0 (the surface `!_0` is the g0 compile-time
    // marker, which has no sequent rules) — build the peeled form directly
    refuted('bang_r3 audit repair (§3f′): a ⊬ !⁰b at count zero (no affine leak)',
      () => [[atom('a')], Store.put('bang', [Store.put('binlit', [0n]), atom('b')])]);
    provable('⊢ !⁰b at count zero still holds (the honest !_0 A ⊣⊢ I reading)',
      () => [[], Store.put('bang', [Store.put('binlit', [0n]), atom('b')])]);
    provable('count-zero bang threads like 1: a ⊢ !⁰b ⊗ a',
      () => [[atom('a')],
        tensor(Store.put('bang', [Store.put('binlit', [0n]), atom('b')]), atom('a'))]);
  });
});
