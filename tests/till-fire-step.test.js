/**
 * @fire as a first-class checkable step — TODO_0294 B1.
 *
 * The kernel re-derives one timed firing from the PROGRAM'S DECLARED RULE
 * DATA (never by running settle): antecedent/consequent correspondence
 * under the recorded theta, the forced-join activation (every input stamp
 * ⊑ a, a attained), the done stamp via the partial residual (qsub — the
 * same ⊖ discipline as monad_l), read survival, persistent goals and
 * conclusions — plus full linear resource threading in verifyTree's lazy
 * delta discipline. Fire trees must reach FULL verification
 * (valid && !unverified) — the whole point of the todo.
 *
 * The `fire` rule is declared in till.rules (@fireStep); it has no
 * principal and is keyed by name, so tag-driven search never enumerates
 * it (check-only — the FFI-principle division: settle searches, the
 * kernel judges).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import Store from '../lib/kernel/store.js';
import Seq from '../lib/kernel/sequent.js';
import { createKernel } from '../lib/prover/kernel.js';
import { loadTillSequent } from '../calculus/till/calculus-config.js';

describe('@fire step (TODO_0294 B1)', () => {
  let calc, kernel, P;
  let A, B, C, G;                 // atoms a, b, c, g
  let at, stampOf;

  before(() => {
    calc = loadTillSequent();
    kernel = createKernel(calc);
    P = (s) => calc.parse(s);
    A = P('a'); B = P('b'); C = P('c'); G = P('g');
    stampOf = (s) => Store.child(P(s), 1);     // parse 'x@t', extract stamp term
    at = (inner, stamp) => Store.put('at', [inner, stamp]);
  });

  const node = (rule, linear, cart, succ, premises = [], state = null) =>
    ({ rule, conclusion: Seq.fromArrays(linear, cart, succ), premises, state });

  // closing leaf: at_l consumes its principal proving the stamped succedent
  const leafFor = (atHash) => node('at_l', [atHash], [], atHash);

  it('accepts a delayed firing and reaches FULL verification', () => {
    const t0 = stampOf('x@0'), t2 = stampOf('x@2'), d2 = stampOf('x@2');
    const a0 = at(A, t0), b2 = at(B, t2);
    const program = { rules: { step: {
      slots: [], consume: [A], read: [], produce: [B], producePers: [],
      goals: [], delay: d2, after: [], before: [],
    } } };
    const fire = { rule: 'step', activation: t0, done: t2, theta: [],
      consumed: { [a0]: 1 }, reserved: {}, produced: { [b2]: 1 }, producedPers: [] };
    const tree = node('fire', [a0], [], b2, [leafFor(b2)], { fire });
    const v = kernel.verifyTree(tree, { program });
    assert.ok(v.valid, v.errors.join('; '));
    assert.equal(v.unverified, undefined, 'fire must never enter unverified');
  });

  it('forced join: activation = max of input stamps, done = join ⊕ delay', () => {
    const t0 = stampOf('x@0'), t3 = stampOf('x@3'), t5 = stampOf('x@5'), d2 = stampOf('x@2');
    const a0 = at(A, t0), c3 = at(C, t3), b5 = at(B, t5);
    const program = { rules: { join2: {
      slots: [], consume: [A, C], read: [], produce: [B], producePers: [],
      goals: [], delay: d2, after: [], before: [],
    } } };
    const fire = { rule: 'join2', activation: t3, done: t5, theta: [],
      consumed: { [a0]: 1, [c3]: 1 }, reserved: {}, produced: { [b5]: 1 }, producedPers: [] };
    const tree = node('fire', [a0, c3], [], b5, [leafFor(b5)], { fire });
    const v = kernel.verifyTree(tree, { program });
    assert.ok(v.valid, v.errors.join('; '));
    assert.equal(v.unverified, undefined);
  });

  it('theta substitution: a metavar rule fires on the witnessed instance', () => {
    const mvX = Store.put('metavar', ['X']);
    const t0 = stampOf('x@0'), t2 = stampOf('x@2'), d2 = stampOf('x@2');
    const a0 = at(A, t0), a2 = at(A, t2);
    const program = { rules: { echo: {
      slots: [mvX], consume: [mvX], read: [], produce: [mvX], producePers: [],
      goals: [], delay: d2, after: [], before: [],
    } } };
    const fire = { rule: 'echo', activation: t0, done: t2, theta: [A],
      consumed: { [a0]: 1 }, reserved: {}, produced: { [a2]: 1 }, producedPers: [] };
    const tree = node('fire', [a0], [], a2, [leafFor(a2)], { fire });
    const v = kernel.verifyTree(tree, { program });
    assert.ok(v.valid, v.errors.join('; '));
  });

  it('reads survive: reserved fact stays in the premise context', () => {
    const t0 = stampOf('x@0'), t2 = stampOf('x@2'), d2 = stampOf('x@2');
    const a0 = at(A, t0), c0 = at(C, t0), b2 = at(B, t2);
    const program = { rules: { rstep: {
      slots: [], consume: [A], read: [C], produce: [B], producePers: [],
      goals: [], delay: d2, after: [], before: [],
    } } };
    const fire = { rule: 'rstep', activation: t0, done: t2, theta: [],
      consumed: { [a0]: 1 }, reserved: { [c0]: 1 }, produced: { [b2]: 1 }, producedPers: [] };
    // premise carries the read c0 onward; close it with tensor of both
    const succ = Store.put('tensor', [b2, c0]);
    const closing = node('tensor_r', [b2, c0], [], succ,
      [leafFor(b2), leafFor(c0)]);
    const tree = node('fire', [a0, c0], [], succ, [closing], { fire });
    const v = kernel.verifyTree(tree, { program });
    assert.ok(v.valid, v.errors.join('; '));
  });

  it('persistent goal: satisfied from the cartesian zone, refuted without it', () => {
    const t0 = stampOf('x@0'), t2 = stampOf('x@2'), d2 = stampOf('x@2');
    const a0 = at(A, t0), b2 = at(B, t2);
    const program = { rules: { gated: {
      slots: [], consume: [A], read: [], produce: [B], producePers: [],
      goals: [G], delay: d2, after: [], before: [],
    } } };
    const fire = { rule: 'gated', activation: t0, done: t2, theta: [],
      consumed: { [a0]: 1 }, reserved: {}, produced: { [b2]: 1 }, producedPers: [] };
    const leaf = node('at_l', [b2], [G], b2);
    const ok = node('fire', [a0], [G], b2, [leaf], { fire });
    assert.ok(kernel.verifyTree(ok, { program }).valid);
    const bad = node('fire', [a0], [], b2, [leafFor(b2)], { fire });
    const v = kernel.verifyTree(bad, { program });
    assert.ok(!v.valid);
    assert.match(v.errors.join(';'), /unprovable persistent goal/);
  });

  it('persistent conclusion must appear in the premise cartesian zone', () => {
    const t0 = stampOf('x@0'), t2 = stampOf('x@2'), d2 = stampOf('x@2');
    const a0 = at(A, t0), b2 = at(B, t2);
    const program = { rules: { learn: {
      slots: [], consume: [A], read: [], produce: [B], producePers: [G],
      goals: [], delay: d2, after: [], before: [],
    } } };
    const fire = { rule: 'learn', activation: t0, done: t2, theta: [],
      consumed: { [a0]: 1 }, reserved: {}, produced: { [b2]: 1 }, producedPers: [G] };
    const withPers = node('at_l', [b2], [G], b2);
    assert.ok(kernel.verifyTree(node('fire', [a0], [], b2, [withPers], { fire }),
      { program }).valid);
    const v = kernel.verifyTree(node('fire', [a0], [], b2, [leafFor(b2)], { fire }),
      { program });
    assert.ok(!v.valid);
    assert.match(v.errors.join(';'), /premise missing a persistent conclusion/);
  });

  describe('rejections', () => {
    let t0, t1, t2, t3, d2, a0, b2, program, mkFire;
    before(() => {
      t0 = stampOf('x@0'); t1 = stampOf('x@1'); t2 = stampOf('x@2'); t3 = stampOf('x@3');
      d2 = stampOf('x@2');
      a0 = at(A, t0); b2 = at(B, t2);
      program = { rules: { step: {
        slots: [], consume: [A], read: [], produce: [B], producePers: [],
        goals: [], delay: d2, after: [], before: [],
      } } };
      mkFire = (over) => ({ rule: 'step', activation: t0, done: t2, theta: [],
        consumed: { [a0]: 1 }, reserved: {}, produced: { [b2]: 1 },
        producedPers: [], ...over });
    });

    const reject = (fire, linear, succ, premises, pattern, prog = null) => {
      const v = kernel.verifyTree(node('fire', linear, [], succ, premises, { fire }),
        { program: prog || program });
      assert.ok(!v.valid, 'expected rejection');
      assert.match(v.errors.join(';'), pattern);
    };

    it('wrong done stamp (residual underivable)', () => {
      const b3 = at(B, t3);
      reject(mkFire({ done: t3, produced: { [b3]: 1 } }), [a0], b3,
        [leafFor(b3)], /done stamp/);
    });

    it('activation above all inputs but not attained', () => {
      const b3 = at(B, t3);
      reject(mkFire({ activation: t1, done: t3, produced: { [b3]: 1 } }),
        [a0], b3, [leafFor(b3)], /not attained/);
    });

    it('activation below an input stamp', () => {
      const a3 = at(A, t3);
      reject(mkFire({ consumed: { [a3]: 1 } }), [a3], b2, [leafFor(b2)],
        /below an input stamp/);
    });

    it('unknown program rule', () => {
      reject(mkFire({ rule: 'ghost' }), [a0], b2, [leafFor(b2)],
        /unknown program rule/);
    });

    it('consumed multiset differs from the rule antecedent', () => {
      const c0 = at(C, t0);
      reject(mkFire({ consumed: { [c0]: 1 } }), [c0], b2, [leafFor(b2)],
        /consumed multiset/);
    });

    it('consumed token not in the sequent context', () => {
      reject(mkFire({}), [], b2, [leafFor(b2)], /not in the available context/);
    });

    it('produced multiset at the wrong stamp', () => {
      const b3 = at(B, t3);
      reject(mkFire({ produced: { [b3]: 1 } }), [a0], b2, [leafFor(b2)],
        /produced multiset/);
    });

    it('missing witness record', () => {
      const v = kernel.verifyTree(node('fire', [a0], [], b2, [leafFor(b2)], null),
        { program });
      assert.ok(!v.valid);
      assert.match(v.errors.join(';'), /no state\.fire record/);
    });

    it('missing program', () => {
      const v = kernel.verifyTree(node('fire', [a0], [], b2, [leafFor(b2)],
        { fire: mkFire({}) }), {});
      assert.ok(!v.valid);
      assert.match(v.errors.join(';'), /requires a program/);
    });
  });

  it('verifyStep: data-level check without threading', () => {
    const t0 = stampOf('x@0'), t2 = stampOf('x@2'), d2 = stampOf('x@2');
    const a0 = at(A, t0), b2 = at(B, t2);
    const program = { rules: { step: {
      slots: [], consume: [A], read: [], produce: [B], producePers: [],
      goals: [], delay: d2, after: [], before: [],
    } } };
    const seq = Seq.fromArrays([a0], [], b2);
    const fire = { rule: 'step', activation: t0, done: t2, theta: [],
      consumed: { [a0]: 1 }, reserved: {}, produced: { [b2]: 1 }, producedPers: [] };
    assert.ok(kernel.verifyStep(seq, 'fire', [], { fire }, { program }).valid);
    const bad = kernel.verifyStep(seq, 'fire', [], { fire: { ...fire, done: stampOf('x@9') } },
      { program });
    assert.ok(!bad.valid);
  });

  it('fire is bound via calculus.stepCheckers, not enumerated in search', () => {
    // the rule exists, with NO annotation — the calculus config binds the
    // name to the checker (P1 slot routing); the kernel stays timed-blind
    assert.ok(calc.rules.fire);
    assert.equal(calc.rules.fire.descriptor.fireStep, undefined);
    assert.ok(calc.stepCheckers && typeof calc.stepCheckers.fire.tree === 'function');
    // no connective, so no formula tag ever resolves to it in search
    assert.equal(calc.rules.fire.descriptor.connective, null);
  });
});
