/**
 * certifyConfluence fuzz smoke (audit item 8) — a small seeded slice of
 * tools/fuzz-confluence.js in the fast suite. The full run (200 trials)
 * rides test:heavy; this pins the harness itself and the four property
 * legs (explore-diamond, exec rule-order invariance, certificate
 * pruning, D6 perturbation) on every fast run.
 *
 * Mutation-verified: neutering D6's duplicate-destination check makes
 * this fail on the perturbation leg (34/60 trials at seed 1).
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { runTrials } from '../../tools/fuzz-confluence.js';

describe('certifyConfluence fuzz smoke (audit item 8)', () => {
  it('25 seeded trials: certified ⇒ all interleavings converge; refusals stay in the taxonomy', () => {
    const res = runTrials({ count: 25, seed: 1 });
    assert.deepEqual(res.failures, [], res.failures.join('\n'));
    assert.ok(res.certified > 0, 'the generator must produce certifiable programs');
    assert.ok(res.refused > 0, 'the generator must produce refusable programs');
  });
});
