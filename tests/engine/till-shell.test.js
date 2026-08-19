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
