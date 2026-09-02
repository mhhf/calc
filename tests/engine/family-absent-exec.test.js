/**
 * Family-absent forward execution (audit 2026-09-02).
 *
 * When cc.family is absent, the composition root builds matchOpts with
 * provePersistent = state-lookup-only and null dynamic-rule slots
 * (lib/engine/index.js: _fam = null). Until now no test EXECUTED that
 * configuration — a null-guard regression in a new engine hook would go
 * uncaught. This runs a real program (with a persistent premise proven
 * from state) through the full _buildMatchOpts → tryMatch pipeline with
 * family stripped from the config.
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import path from 'path';
import os from 'os';
import Store from '../../lib/kernel/store.js';
import engine from '../../lib/engine/index.js';
import illConfig from '../../calculus/ill/calculus-config.js';

const atom = (n) => Store.put('atom', [n]);

const PROGRAM = `
fa_a: type.
fa_b: type.
fa_p: type.

fa_step: fa_a * !fa_p -o { fa_b }.
`;

describe('family-absent forward execution', () => {
  let file;
  before(() => {
    file = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'calc-fa-')), 'fa.ill');
    fs.writeFileSync(file, PROGRAM);
  });
  after(() => { fs.rmSync(path.dirname(file), { recursive: true, force: true }); });

  it('cc without family executes via state-lookup-only persistent proving', async () => {
    const cc = { ...illConfig, family: undefined };
    const calc = await engine.load(file, { calculusConfig: cc });

    const a = atom('fa_a'), b = atom('fa_b'), p = atom('fa_p');
    const result = calc.exec(
      { linear: { [a]: 1 }, persistent: { [p]: 1 } },
      { maxSteps: 10 }
    );

    assert.ok(result.quiescent, 'should reach quiescence');
    assert.equal(result.steps, 1, 'fa_step fires exactly once');
    assert.equal(result.state.linear[b], 1, 'fa_b produced');
    assert.ok(!result.state.linear[a], 'fa_a consumed');
  });

  it('the same program with cc.family present agrees', async () => {
    const calc = await engine.load(file, { calculusConfig: illConfig });
    const a = atom('fa_a'), b = atom('fa_b'), p = atom('fa_p');
    const result = calc.exec(
      { linear: { [a]: 1 }, persistent: { [p]: 1 } },
      { maxSteps: 10 }
    );
    assert.ok(result.quiescent);
    assert.equal(result.state.linear[b], 1);
  });
});
