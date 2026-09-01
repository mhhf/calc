/**
 * till-shell --demo smoke test — round-15 F6.iv.
 *
 * The shell's scripted mode is its testable core (settle → frame →
 * click → settle, wall-clock = horizon). Spawns the real CLI on the
 * till-shell-smoke fixture and asserts on frame content: a costed-loli
 * click CUTS (output arrives at t+delay), a plain alternative projects,
 * and a click without the cost is REFUSED with the state untouched.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import { execFile } from 'node:child_process';

const ROOT = path.join(import.meta.dirname, '../..');
const FIXTURE = path.join(ROOT, 'tests/fixtures/till-shell-smoke.ill');

const runShell = (args) => new Promise((resolve, reject) => {
  execFile('node', [path.join(ROOT, 'tools/till-shell.js'), FIXTURE, ...args],
    { cwd: ROOT, timeout: 30000 }, (err, stdout, stderr) => {
      if (err) reject(new Error(`shell failed: ${err.message}\n${stderr}\n${stdout}`));
      else resolve(stdout);
    });
});

describe('till-shell --demo (scripted, headless)', () => {
  it('costed click cuts; plain click projects; frames track the state', async () => {
    const out = await runShell(['--init', 'expect_start', '--demo', '1:1,4:2']);
    // click 1 at t=1: accepted (no error suffix on the click line)
    assert.match(out, /══ click \[1\] at t=1 \n/, 'loli click accepted');
    // the job is in flight: farm_s arriving at 1+3
    assert.match(out, /arriving:\n\s+farm_s\s+@4\.0/, 'farm arriving at 4');
    // after click 2 at t=4: both tokens landed
    assert.match(out, /1 farm_s\s+1 wood_s/, 'final stocks');
    // the spent menu greys: cost gone ⇒ strict alternative unavailable
    assert.match(out, /2 spc_s ⊸ farm_s\s+\(3s\)\s+\(unavailable\)/);
  });

  it('without the cost the strict click is REFUSED and nothing enters', async () => {
    const out = await runShell(['--init', 'expect_nospc', '--demo', '1:1']);
    assert.match(out, /→ choose: alternative 0 cannot fire at the decision time/);
    assert.match(out, /0 spc_s\s+0 farm_s\s+0 wood_s/, 'state untouched');
  });
});

describe('till-shell collapse mode (TODO_0298, scripted headless)', () => {
  const WFC = path.join(ROOT, 'calculus/will/game/WFC.will');
  const runWfc = (args) => new Promise((resolve, reject) => {
    execFile('node', [path.join(ROOT, 'tools/till-shell.js'), WFC, ...args],
      { cwd: ROOT, timeout: 30000 }, (err, stdout, stderr) => {
        if (err) reject(new Error(`shell failed: ${err.message}\n${stderr}\n${stdout}`));
        else resolve(stdout);
      });
  });

  it('auto-detects suspended waves, draws to ground, frames show the wave menu', async () => {
    const out = await runWfc(['--demo', 'a,a,a,a', '--seed', '3']);
    // wave menu with the evar rendered as ? and posterior weights
    assert.match(out, /waves \(entropy-sorted — \[1\] is the driver's pick\):/);
    assert.match(out, /tile\(c\d, \?\)/, 'open wave facts render with a hole');
    // four auto draws reach ground
    assert.match(out, /waves: none — GROUND/);
    // the log carries member + exact weight per draw
    assert.match(out, /log: \w+ \d+\/\d+( → \w+ \d+\/\d+){3}/);
  });

  it('a bias-pruned wave shows fewer members and sorts first', async () => {
    // seed 3 draws coast then land (smoke-pinned): after the land draw the
    // biased neighbor lists only coast · land and leads the menu
    const out = await runWfc(['--demo', 'a,a', '--seed', '3']);
    assert.match(out, /\[1\] tile\(c\d, \?\)@?\d*\s+—\s+coast 1 · land 2\s+H=/,
      'pruned wave (sea excluded) leads the menu');
  });
});
