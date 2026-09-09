/**
 * sax prover guard (TODO_0309 P1) — pins the semi-axiomatic sequent
 * calculus over the SAX family's single-zone judgment Δ ⊢ C.
 *
 * Pins:
 *   - contextStructure: ONE zone, no copy source (the first family
 *     without a cartesian zone)
 *   - the X-rules: zero-premise axioms consume their companion formulas
 *     exactly (no silent weakening — extra context refutes)
 *   - invertible rules unchanged; additive branches balance
 *   - snip search: cut formulas from the proper subformula closure
 *     (⊗-associativity and ⊸-composition have NO snip-free proofs)
 *   - every successful proof passes L1 kernel verification with no
 *     unverified entries; doctored trees are REJECTED (adversarial pins
 *     for companion consumption and the cut split)
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import Seq from '../lib/kernel/sequent.js';
import { ProofTree } from '../lib/prover/pt.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import { loadSaxSequent } from '../calculus/sax/calculus-config.js';

describe('sax prover (TODO_0309 P1)', () => {
  let calc, specs, alternatives, prover, kernel, P;

  before(() => {
    calc = loadSaxSequent();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc);
    kernel = createKernel(calc);
    P = (s) => calc.parse(s);
  });

  const prove = (lin, succ) => prover.prove(
    Seq.seq({ linear: lin.map(P) }, P(succ)),
    { rules: specs, alternatives, maxDepth: 40 });

  const proveVerified = (lin, succ) => {
    const r = prove(lin, succ);
    assert.ok(r.success, `expected provable: ${lin.join(', ')} |- ${succ}`);
    const v = kernel.verifyTree(r.proofTree);
    assert.ok(v.valid, `kernel: ${JSON.stringify(v.errors)}`);
    assert.ok(!v.unverified, `unverified: ${v.unverified}`);
    return r;
  };

  const refute = (lin, succ) => {
    const r = prove(lin, succ);
    assert.ok(!r.success, `expected NOT provable: ${lin.join(', ')} |- ${succ}`);
  };

  it('contextStructure: single linear zone, no copy source', () => {
    const cs = calc.contextStructure;
    assert.deepEqual(cs.zones, ['linear']);
    assert.deepEqual(cs.consumableZones, ['linear']);
    assert.equal(cs.copySource, null);
    assert.equal(cs.copyTarget, null);
    assert.equal(cs.properties.linear.contraction, false);
    assert.equal(cs.properties.linear.weakening, false);
  });

  it('rule table: axioms compiled with companions, cut detected', () => {
    assert.ok(calc.rules.tensor_r.descriptor.template.companions.length === 2);
    assert.ok(calc.rules.loli_l.descriptor.template.companions.length === 1);
    assert.ok(calc.rules.oplus_r1.descriptor.template.companions.length === 1);
    assert.equal(calc.rules.with_l1.descriptor.template.companions, undefined);
    assert.equal(calc.rules.cut.descriptor.cut, true);
    assert.equal(specs.cut._premiseType, 'cut');
  });

  it('identity', () => {
    proveVerified(['a'], 'a');
    refute(['a'], 'b');
    refute(['a', 'b'], 'a');           // no weakening
  });

  it('⊗X consumes exactly its companions', () => {
    proveVerified(['a', 'b'], 'a * b');
    refute(['a', 'b', 'c'], 'a * b');  // leftover refutes
    refute(['a'], 'a * a');            // no contraction
  });

  it('⊗L is invertible; commutativity and associativity (snip)', () => {
    proveVerified(['a * b'], 'b * a');
    proveVerified(['a * (b * c)'], '(a * b) * c');   // needs cut on a*b
    proveVerified(['(a * b) * c'], 'a * (b * c)');
  });

  it('1X / 1L', () => {
    proveVerified([], 'I');
    proveVerified(['I', 'a'], 'a');
    proveVerified(['a'], 'a * I');
    refute(['a'], 'I');
  });

  it('⊸X / ⊸R; composition needs an atom snip', () => {
    proveVerified(['a', 'a -o b'], 'b');
    proveVerified([], 'a -o a');
    proveVerified(['a -o b', 'b -o c'], 'a -o c');   // cut on b
    proveVerified(['(a * b) -o c'], 'a -o (b -o c)'); // curry
    refute(['a -o b'], 'b');
  });

  it('&X projections / &R balanced branches', () => {
    proveVerified(['a & b'], 'a');
    proveVerified(['a & b'], 'b');
    proveVerified(['a & b'], 'b & a');
    refute(['a & b'], 'a * b');        // one projection only
  });

  it('⊕X injections / ⊕L', () => {
    proveVerified(['a'], 'a + b');
    proveVerified(['b'], 'a + b');
    proveVerified(['a + b'], 'b + a');
    refute(['a + b'], 'a');
  });

  it('mixed: distribution of ⊗ over ⊕', () => {
    proveVerified(['a * (b + c)'], '(a * b) + (a * c)');
  });

  it('kernel rejects a doctored axiom: companion not in context', () => {
    // forged: a ⊢ a ⊗ b via tensor_r without possessing b
    const seq = Seq.seq({ linear: [P('a')] }, P('a * b'));
    const tree = new ProofTree({ conclusion: seq, premises: [], rule: 'tensor_r', proven: true, state: null });
    const v = kernel.verifyTree(tree);
    assert.ok(!v.valid, 'forged axiom must be rejected');
  });

  it('kernel rejects a forged with projection: with_l1 claiming the right component', () => {
    // with_l1 is the A-projection axiom (A & B ⊢ A); forging it to
    // conclude b from a & b must fail the template succedent
    // re-derivation (rule-interpreter's succ check) — the projection
    // choice is data the kernel re-checks, not trusts.
    const seq = Seq.seq({ linear: [P('a & b')] }, P('b'));
    const tree = new ProofTree({ conclusion: seq, premises: [], rule: 'with_l1', proven: true, state: null });
    const v = kernel.verifyTree(tree);
    assert.ok(!v.valid, 'forged with projection must be rejected');
  });

  it('kernel rejects a doctored cut: premise 2 without the cut formula', () => {
    // forged: a ⊢ b by cut on c where premise 2 never carries c
    const seq = Seq.seq({ linear: [P('a')] }, P('b'));
    const p1 = new ProofTree({
      conclusion: Seq.seq({ linear: [P('a')] }, P('a')),
      premises: [], rule: 'id', proven: true, state: null,
    });
    const p2 = new ProofTree({
      conclusion: Seq.seq({ linear: [] }, P('b')),
      premises: [], rule: 'id', proven: true, state: null,
    });
    const tree = new ProofTree({ conclusion: seq, premises: [p1, p2], rule: 'cut', proven: true, state: null });
    const v = kernel.verifyTree(tree);
    assert.ok(!v.valid, 'forged cut must be rejected');
  });

  it('kernel rejects a laundered cut formula: manufactured but unconsumed', () => {
    // cut manufactures a⊗b, premise 2 carries it but "proves" b by id on
    // a leaked a — the unconsumed a⊗b must surface at the root
    const seq = Seq.seq({ linear: [P('a'), P('b')] }, P('a * b'));
    const p1 = new ProofTree({
      conclusion: Seq.seq({ linear: [P('a'), P('b')] }, P('a * b')),
      premises: [], rule: 'tensor_r', proven: true, state: null,
    });
    const p2 = new ProofTree({
      conclusion: Seq.seq({ linear: [P('a * b'), P('a * b')] }, P('a * b')),
      premises: [], rule: 'id', proven: true, state: null,
    });
    const tree = new ProofTree({ conclusion: seq, premises: [p1, p2], rule: 'cut', proven: true, state: null });
    const v = kernel.verifyTree(tree);
    assert.ok(!v.valid, 'leaked cut formula must be rejected');
  });
});
