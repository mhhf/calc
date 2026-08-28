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
});
