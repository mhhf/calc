/**
 * Trace elaboration — TODO_0294 B2/B3.
 *
 * End-to-end: a real till program is settled by the ENGINE, the event
 * trace is elaborated into an @fire proof tree, and the KERNEL fully
 * re-derives it against the program's declared rule data (fire-check) —
 * valid && !unverified, no modeSwitch trust. Elaboration is total on
 * legal traces of supported rules (THY_0018 §5): a failed elaboration
 * here is a found engine bug, not a test artifact.
 *
 * Also pins certifyRun (B3): settle → elaborate → verify for an
 * arbitrary run, goal = the residual state itself at the horizon.
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../lib/kernel/store.js';
import Seq from '../lib/kernel/sequent.js';
import mde from '../lib/engine/index.js';
import tillConfig, { loadTillSequent } from '../calculus/till/calculus-config.js';
import { createKernel } from '../lib/prover/kernel.js';
import { programFromCalc, elaborateTrace, certifyRun } from '../lib/prover/timed/elaborate-trace.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'till-elab-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));

const loadProgram = (name, src) => {
  const file = path.join(tmp, name);
  fs.writeFileSync(file, src);
  return mde.load(file, { calculusConfig: tillConfig, cache: false });
};

describe('trace elaboration (TODO_0294 B2)', () => {
  let seqCalc, kernel, P, atom;

  before(() => {
    seqCalc = loadTillSequent();
    kernel = createKernel(seqCalc);
    P = (s) => seqCalc.parse(s);
    atom = (n) => Store.put('atom', [n]);
  });

  const fullVerify = (tree, program) => {
    const v = kernel.verifyTree(tree, { program });
    assert.ok(v.valid, (v.errors || []).join('; '));
    assert.equal(v.unverified, undefined, 'elaborated trees must be FULLY verified');
    return v;
  };

  it('chain: two firings elaborate and fully verify', () => {
    const calc = loadProgram('chain.till', `
a: type.  b: type.  c: type.
r1: a -o { b }@2.
r2: b -o { c }@3.
`);
    const res = calc.settle({ linear: { [atom('a')]: 1 }, persistent: {} }, '10');
    assert.equal((res.events || []).length, 2, 'chain fires twice');
    const program = programFromCalc(calc);
    const sequent = Seq.fromArrays([atom('a')], [], P('{c@5}@10'));
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    fullVerify(elab.tree, program);
  });

  it('join: forced-max activation elaborates (c at max(2,3)+1 = 4)', () => {
    const calc = loadProgram('join.till', `
a: type.  b: type.  x: type.  y: type.  c: type.
r1: a -o { x }@2.
r2: b -o { y }@3.
r3: x * y -o { c }@1.
`);
    const res = calc.settle({ linear: { [atom('a')]: 1, [atom('b')]: 1 }, persistent: {} }, '10');
    assert.equal((res.events || []).length, 3);
    const program = programFromCalc(calc);
    const sequent = Seq.fromArrays([atom('a'), atom('b')], [], P('{c@4}@10'));
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    fullVerify(elab.tree, program);
  });

  it('persistent conclusion: grounds from the rule record and verifies', () => {
    const calc = loadProgram('pers.till', `
a: type.  b: type.  g: type.
mk: a -o { b * !g }@2.
`);
    const res = calc.settle({ linear: { [atom('a')]: 1 }, persistent: {} }, '10');
    assert.equal((res.events || []).length, 1);
    const program = programFromCalc(calc);
    const sequent = Seq.fromArrays([atom('a')], [], P('{b@2}@10'));
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    fullVerify(elab.tree, program);
  });

  it('stamped initial tokens heal across canon (parsed vs reified stamps)', () => {
    const calc = loadProgram('stamped.till', `
a: type.  b: type.
r1: a -o { b }@2.
`);
    const a3 = P('a@3');
    const res = calc.settle({ linear: { [a3]: 1 }, persistent: {} }, '10');
    assert.equal((res.events || []).length, 1);
    const program = programFromCalc(calc);
    const sequent = Seq.fromArrays([a3], [], P('{b@5}@10'));
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    fullVerify(elab.tree, program);
  });

  it('counted take + counted produce: !_3 g -o { !_2 h } fully verifies', () => {
    const calc = loadProgram('counted.till', `
g: type.  h: type.
trim: !_3 g -o { !_2 h }@1.
`);
    const res = calc.settle({ linear: { [atom('g')]: 7 }, persistent: {} }, '5');
    const program = programFromCalc(calc);
    // 7 g → two firings (RLE-batched or not), 1 g + 4 h remain
    const full = Seq.fromArrays(
      Array(7).fill(atom('g')), [], P('{g * h@1 * h@1 * h@1 * h@1}@5'));
    const elab = elaborateTrace({ sequent: full, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    fullVerify(elab.tree, program);
  });

  it('whole-bind: !_W g takes the whole cohort and fully verifies', () => {
    const calc = loadProgram('wbind.till', `
g: type.  w: bin -> type.
allg: !_W g -o { w W }@1.
`);
    const res = calc.settle({ linear: { [atom('g')]: 4 }, persistent: {} }, '5');
    assert.equal(res.events.length, 1);
    const program = programFromCalc(calc);
    const w4at1 = Object.keys(res.events[0].produced).map(Number)[0];
    const succ = Store.put('monad', [Store.child(P('x@5'), 1), w4at1]);
    const sequent = Seq.fromArrays(Array(4).fill(atom('g')), [], succ);
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    fullVerify(elab.tree, program);
  });

  it('whole-bind forgeries are rejected (count mismatch; partial take)', () => {
    const calc = loadProgram('wbind2.till', `
g: type.  w: bin -> type.
allg: !_W g -o { w W }@1.
`);
    const res = calc.settle({ linear: { [atom('g')]: 4 }, persistent: {} }, '5');
    const program = programFromCalc(calc);
    const ev = res.events[0];
    const consumedKey = Number(Object.keys(ev.consumed)[0]);
    // forge 1: claim W=3 while consuming 4 → count mismatch (data-level)
    const three = Store.put('binlit', [3n]);
    const forged1 = { ...ev, theta: [three] };
    const succ = Store.put('monad', [Store.child(P('x@5'), 1),
      Store.put('w', [three])]);
    const seq1 = Seq.fromArrays(Array(4).fill(atom('g')), [], succ);
    const e1 = elaborateTrace({ sequent: seq1, events: [forged1], program, calculus: seqCalc });
    // the forge must be rejected SOMEWHERE — pre-fix this silently passed
    // when elaboration refused (TODO_0296 P3: no vacuous forgery tests)
    if (e1.tree) {
      const v = kernel.verifyTree(e1.tree, { program });
      assert.ok(!v.valid, 'W≠take must not verify');
    } else {
      assert.ok(e1.unsupported, 'forge must fail elaboration if not kernel-rejected');
    }
    // forge 2: take only 3 of 4 (W=3, consistent) → none-left violation
    const forged2 = { ...ev, theta: [three],
      consumed: { [consumedKey]: 3 },
      produced: { [Store.put('at', [Store.put('w', [three]), Store.child(P('x@1'), 1)])]: 1 },
      done: Store.child(P('x@1'), 1) };
    const seq2 = Seq.fromArrays(Array(4).fill(atom('g')), [],
      Store.put('monad', [Store.child(P('x@5'), 1),
        Store.put('tensor', [Store.put('at', [Store.put('w', [three]), Store.child(P('x@1'), 1)]), atom('g')])]));
    const e2 = elaborateTrace({ sequent: seq2, events: [forged2], program, calculus: seqCalc });
    assert.ok(e2.tree, `elaboration failed: ${e2.unsupported}`);
    const v2 = kernel.verifyTree(e2.tree, { program });
    assert.ok(!v2.valid, 'partial whole-bind take must not verify');
    assert.match(v2.errors.join(';'), /whole cohort/);
  });

  it('possessed loli: a produced rule token fires and fully verifies', () => {
    const calc = loadProgram('loli.till', `
a: type.  b: type.  c: type.
mk: c -o { (a -o {b}@2) }@1.
`);
    const res = calc.settle({ linear: { [atom('a')]: 1, [atom('c')]: 1 }, persistent: {} }, '10');
    assert.equal(res.events.length, 2, 'mk then the possessed loli');
    const program = programFromCalc(calc);
    const sequent = Seq.fromArrays([atom('a'), atom('c')], [], P('{b@3}@10'));
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    fullVerify(elab.tree, program);
  });

  it('bang succedent: persistent conclusion closes via bang_r + copy', () => {
    const calc = loadProgram('bangsucc.till', `
a: type.  b: type.  g: type.
mk: a -o { b * !g }@2.
`);
    const res = calc.settle({ linear: { [atom('a')]: 1 }, persistent: {} }, '10');
    const program = programFromCalc(calc);
    const sequent = Seq.fromArrays([atom('a')], [], P('{b@2 * !g}@10'));
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    fullVerify(elab.tree, program);
  });

  it('counted-bang succedent: !_4 (h@1) closes via the bang_r2 peel chain', () => {
    const calc = loadProgram('cbgoal.till', `
g: type.  h: type.
trim: !_3 g -o { !_2 h }@1.
`);
    const res = calc.settle({ linear: { [atom('g')]: 6 }, persistent: {} }, '5');
    const program = programFromCalc(calc);
    // 6 g → 2 firings → 4 h@1; goal: the counted parcel !_4 (h@1)
    const h1 = Object.keys(res.events[0].produced).map(Number)[0];
    const goal = Store.put('bang', [Store.put('binlit', [4n]), h1]);
    const succ = Store.put('monad', [Store.child(P('x@5'), 1), goal]);
    const sequent = Seq.fromArrays(Array(6).fill(atom('g')), [], succ);
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    fullVerify(elab.tree, program);
  });

  it('clause-derived goal: SLD certificate checked, not trusted (0295)', () => {
    const calc = loadProgram('clausegoal.till', `
a: type.  b: type.  p: type.  q: type.
ax: p.
imp: q
  <- p.
use: a * !q -o { b }@1.
`);
    const res = calc.settle({ linear: { [atom('a')]: 1 }, persistent: {} }, '5');
    assert.equal(res.events.length, 1);
    const program = programFromCalc(calc);
    const sequent = Seq.fromArrays([atom('a')], [], P('{b@1}@5'));
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    // the fire node carries a checked certificate for q (imp ← ax)
    const fire = elab.tree.state.fire;
    assert.ok(fire.goalCerts && Object.keys(fire.goalCerts).length === 1,
      'goal certificate attached');
    fullVerify(elab.tree, program);
    // forgeries: tamper the certificate → kernel rejects
    const q = atom('q'), pA = atom('p');
    const goodCert = Object.values(fire.goalCerts)[0];
    const forge = (cert, pattern) => {
      const t = { ...elab.tree.state.fire, goalCerts: { [q]: cert } };
      const node = { ...elab.tree, state: { fire: t } };
      const v = kernel.verifyTree(node, { program });
      assert.ok(!v.valid, 'forged certificate must not verify');
      assert.match(v.errors.join(';'), pattern);
    };
    forge({ ...goodCert, rule: 'ghost' }, /unknown clause/);
    forge({ ...goodCert, premises: [] }, /premise/);
    forge({ rule: 'ffi', goal: q, premises: [] }, /ffi leaf/);
    forge({ ...goodCert, goal: pA }, /different goal/);
    forge({ ...goodCert, premises: [{ rule: 'ax', goal: q, premises: [] }] },
      /does not match its subderivation|not an instance/);
  });

  it('numeric-tower clause goal: cross-tag certificate (binlit vs i/o/e) verifies', () => {
    const calc = loadProgram('natgoal.till', `
a: type.  b: type.
e: bin.  i: bin -> bin.  o: bin -> bin.
nat: bin -> type.
nat/e: nat e.
nat/i: nat (i X)
  <- nat X.
nat/o: nat (o X)
  <- nat X.
use: a * !nat 5 -o { b }@1.
`);
    const res = calc.settle({ linear: { [atom('a')]: 1 }, persistent: {} }, '5');
    assert.equal(res.events.length, 1);
    const program = programFromCalc(calc);
    const sequent = Seq.fromArrays([atom('a')], [], P('{b@1}@5'));
    const elab = elaborateTrace({ sequent, events: res.events, program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    // the certificate is the nat/i→nat/o→nat/i→nat/e chain: canonical
    // binlit 5 matched against i/o/e clause patterns at EVERY node —
    // the checker's theory-aware matcher, not string luck
    const cert = Object.values(elab.tree.state.fire.goalCerts)[0];
    assert.equal(cert.rule, 'nat/i');
    assert.equal(cert.premises[0].premises[0].premises[0].rule, 'nat/e');
    fullVerify(elab.tree, program);
  });

  it('a forged trace is REJECTED by the kernel (tampered done stamp)', () => {
    const calc = loadProgram('forge.till', `
a: type.  b: type.
r1: a -o { b }@2.
`);
    const res = calc.settle({ linear: { [atom('a')]: 1 }, persistent: {} }, '10');
    const program = programFromCalc(calc);
    // tamper: claim b arrives at 1 instead of 2
    const ev = { ...res.events[0] };
    const b1 = P('b@1');
    ev.done = Store.child(b1, 1);
    ev.produced = { [b1]: 1 };
    const sequent = Seq.fromArrays([atom('a')], [], P('{b@1}@10'));
    const elab = elaborateTrace({ sequent, events: [ev], program, calculus: seqCalc });
    assert.ok(elab.tree, `elaboration failed: ${elab.unsupported}`);
    const v = kernel.verifyTree(elab.tree, { program });
    assert.ok(!v.valid, 'forged done stamp must not verify');
    assert.match(v.errors.join(';'), /done stamp/);
  });
});

describe('certifyRun (TODO_0294 B3)', () => {
  let seqCalc, kernel, atom;

  before(() => {
    seqCalc = loadTillSequent();
    kernel = createKernel(seqCalc);
    atom = (n) => Store.put('atom', [n]);
  });

  it('certifies an arbitrary run against its own residual state', () => {
    const calc = loadProgram('cert.till', `
a: type.  b: type.  c: type.
r1: a -o { b }@2.
r2: b -o { c }@3.
`);
    const horizonTerm = Store.child(seqCalc.parse('x@10'), 1);
    const r = certifyRun({
      engineCalc: calc, calculus: seqCalc, kernel,
      state: { linear: { [atom('a')]: 1 }, persistent: {} },
      horizon: '10', horizonTerm,
    });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    assert.equal(r.events.length, 2);
  });

  it('certifies a run with READ premises (adaptRule must not double-demand)', () => {
    // Regression (TODO_0296 P2, found by gill's depot certification):
    // read premises live inside antecedent.linear — adaptRule expanded
    // them into consume AND read, so the checker demanded the read token
    // twice and every read-rule certification failed.
    const calc = loadProgram('cert-read.till', `
a: type.  b: type.  g: type.
r1: read g * a -o { b }@2.
`);
    const horizonTerm = Store.child(seqCalc.parse('x@10'), 1);
    const r = certifyRun({
      engineCalc: calc, calculus: seqCalc, kernel,
      state: { linear: { [atom('a')]: 1, [atom('g')]: 1 }, persistent: {} },
      horizon: '10', horizonTerm,
    });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    assert.equal(r.events.length, 1);
  });
});

describe('sld-check undo discipline (TODO_0296 P0)', () => {
  it('checks hundreds of binding-heavy certificates without undo overflow', async () => {
    // matchIndexed logs slot bindings on unify's module-global undo stack
    // (capacity 128). Pre-fix, sld-check never discarded its span — the
    // 129th accumulated binding threw 'undo stack overflow' and leaked
    // entries could corrupt the ENGINE's backtracking theta. 300 checks
    // of a metavar-headed clause pin the discipline.
    const { checkSLD } = await import('../lib/prover/sld-check.js');
    const X = Store.put('metavar', ['X']);
    const clauses = new Map([['ax', { hash: Store.put('pp', [X]), premises: [] }]]);
    const goal = Store.put('pp', [Store.put('atom', ['aa'])]);
    for (let i = 0; i < 300; i++) {
      const r = checkSLD({ rule: 'ax', goal, premises: [] }, clauses, new Map());
      assert.equal(r.error, undefined);
    }
  });

  it('definition-branch forgeries are rejected (TODO_0296 P3)', async () => {
    const { checkSLD, checkGoalCert } = await import('../lib/prover/sld-check.js');
    const X = Store.put('metavar', ['X']);
    const defs = new Map([['fact', Store.put('qq', [X])]]);
    const good = Store.put('qq', [Store.put('atom', ['aa'])]);
    const other = Store.put('rr', [Store.put('atom', ['aa'])]);
    // sanity: the fact matches
    assert.equal(checkSLD({ rule: 'fact', goal: good, premises: [] },
      new Map(), defs).error, undefined);
    // a definition is a fact — premises are a forgery
    assert.match(checkSLD({ rule: 'fact', goal: good,
      premises: [{ rule: 'fact', goal: good, premises: [] }] },
      new Map(), defs).error, /is a fact — no premises/);
    // goal not an instance of the definition
    assert.match(checkSLD({ rule: 'fact', goal: other, premises: [] },
      new Map(), defs).error, /not an instance of definition/);
    // malformed node (no numeric goal)
    assert.match(checkSLD({ rule: 'fact' }, new Map(), defs).error, /malformed/);
    // missing certificate for a required goal
    assert.match(checkGoalCert(null, good, new Map(), defs).error, /missing certificate/);
  });
});
