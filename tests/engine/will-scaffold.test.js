/**
 * will scaffold (TODO_0297 P0) — fast-suite guard for the new calculus.
 *
 * Pins:
 *   - will.calc @extends gill resolves ACROSS calculus directories (the
 *     first cross-calculus chain): will's connective table and sort
 *     edges are gill's, inherited not copied
 *   - gradeAlgebraFor routes over will's OWN tables: woplus → weight →
 *     weightGrades (measure class), haul → dist → distGrades, monad →
 *     delay → tillGrades
 *   - the sequent calculus loads with will's theory and binds the fire
 *     checker (kit.js makeSequentLoader)
 *   - a woplus firing under will elaborates and fully kernel-verifies
 *     end-to-end (certifyRun over the inherited verified chain — the
 *     weighted alternative draw is part of the checked record)
 */

import { describe, it, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import { tillGrades } from '../../calculus/till/calculus-config.js';
import gillConfig, { distGrades, weightGrades } from '../../calculus/gill/calculus-config.js';
import willConfig, { gradeAlgebraFor, loadWillSequent } from '../../calculus/will/calculus-config.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { certifyRun } from '../../lib/prover/timed/elaborate-trace.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'will-scaffold-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));

describe('will scaffold (TODO_0297 P0)', () => {
  it('@extends gill resolves cross-directory: the surface is inherited', () => {
    // Table equality IS the acceptance: will.calc declares no connective
    // of its own, so any divergence means the chain broke.
    assert.deepEqual(willConfig.connectives, gillConfig.connectives);
    const edges = willConfig.sorts.calc.edges;
    for (const s of ['delay', 'count', 'weight', 'dist']) {
      assert.ok(edges.some(([a, b]) => a === s && b === 'grade'), `${s} <: grade inherited`);
    }
  });

  it('gradeAlgebraFor routes over will tables: woplus → measure class', () => {
    assert.strictEqual(gradeAlgebraFor('woplus'), weightGrades);
    assert.strictEqual(gradeAlgebraFor('haul'), distGrades);
    assert.strictEqual(gradeAlgebraFor('monad'), tillGrades);
    assert.equal(weightGrades.aggregate.class, 'measure');
  });

  it('sequent calculus loads and binds the fire checker', () => {
    const seqCalc = loadWillSequent();
    assert.ok(seqCalc.fire && seqCalc.stepCheckers, 'will must bind the fire checker');
    assert.equal(seqCalc.fire.stampTag, 'at');
  });

  it('a woplus firing under will elaborates and fully kernel-verifies', () => {
    const file = path.join(tmp, 'sure.will');
    fs.writeFileSync(file, 'a: type.\nb: type.\nc: type.\nsure: a -o { b +[1] c }@1.\n');
    const engineCalc = mde.load(file, { calculusConfig: willConfig, cache: false });
    const seqCalc = loadWillSequent();
    const kernel = createKernel(seqCalc);
    const horizonTerm = Store.child(seqCalc.parse('x@2'), 1);
    const r = certifyRun({
      engineCalc, calculus: seqCalc, kernel,
      state: { linear: { [Store.put('atom', ['a'])]: 1 }, persistent: {} },
      horizon: '2', horizonTerm,
      settleOpts: { maxSteps: 100 },
    });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    assert.equal(r.events.length, 1);
    assert.equal(r.events[0].rule, 'sure');
  });
});
