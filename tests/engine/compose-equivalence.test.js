/**
 * Compose fusion equivalence pin (RES_0143 E2b).
 *
 * The compose pipeline's optimization passes (P5 basic-block fusion,
 * P5.5 chain fusion, P6 SROA) must be semantics-preserving: a program
 * executed with fusion ON must reach the same final state as with
 * fusion OFF. Before this pin, compose determinism was tested but
 * on/off equivalence was not — a fusion bug would have silently
 * changed runtime semantics.
 *
 * The program is the minimal shape on which P5 actually fires
 * (verified via onPhase diagnostics): grade-0 code facts specialized
 * per pc (P2), residual !plus resolved at compile time (P3+4, gives
 * ground pc producers), then the 1:1 pc-threaded producer→consumer
 * chain fuses into one mega-rule.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import illcc from '../../calculus/ill/calculus-config.js';
import { show } from '../../lib/engine/show.js';

const PROG =
  'pc : bin -> type.\n' +
  'ceq_acc : bin -> type.\n' +
  'ceq_done : bin -> type.\n' +
  'plus: (a: bin) -> (b: bin) -> (c: bin) -> type.\n' +
  'ceq_code: (a: bin) -> (op: bin) -> type.\n' +
  'ceq_code/c0: !_0 ceq_code 0 1.\n' +
  'ceq_code/c1: !_0 ceq_code 1 1.\n' +
  'ceq_code/c2: !_0 ceq_code 2 2.\n' +
  'istep: pc PC * !ceq_code PC 1 * ceq_acc X * !plus PC 1 PC2 -o { pc PC2 * ceq_acc X }.\n' +
  'ihalt: pc PC * !ceq_code PC 2 * ceq_acc X -o { ceq_done X }.\n' +
  '#symex pc 0 * ceq_acc 3.\n';

function runArm(fuse) {
  Store.clear();
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'compose-eq-'));
  const file = path.join(tmpDir, 'prog.ill');
  fs.writeFileSync(file, PROG);
  try {
    const calc = mde.load(file, {
      cache: false,
      fuseBasicBlocks: fuse,
      residualResolver: illcc.compose.residualResolver,
    });
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    const res = calc.exec(state, { maxSteps: 20 });
    return {
      ruleCount: calc.forwardRules.length,
      quiescent: res.quiescent,
      // Value-level final state (show renders by content, not by hash id —
      // Store ids differ across the two loads)
      finalLinear: Object.keys(res.state.linear).map(h => show(Number(h))).sort(),
    };
  } finally {
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  }
}

describe('compose fusion equivalence (RES_0143 E2b)', () => {
  it('fusion ON reaches the same final state as fusion OFF', () => {
    const off = runArm(false);
    const on = runArm(true);

    // The pin is non-vacuous: fusion must actually have fired.
    assert.equal(off.ruleCount, 3, 'unfused arm: 3 specialized rules');
    assert.equal(on.ruleCount, 1, 'fused arm: one mega-rule (P5 fired)');

    // Semantic equivalence.
    assert.equal(on.quiescent, off.quiescent, 'both quiescent');
    assert.deepEqual(on.finalLinear, off.finalLinear,
      'fused and unfused arms reach the same final state');
    assert.deepEqual(off.finalLinear, ['ceq_done(0x3)'], 'expected result');
  });
});
