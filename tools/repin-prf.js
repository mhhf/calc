#!/usr/bin/env node
/**
 * Mechanical re-capture of the two-tier PRF golden pins (TODO_0272 M8).
 *
 * The till PRF chooser mixes the arena-layout-dependent state hash, so the
 * EXACT draw sequences (tier 2) legitimately re-roll on any interning shift
 * (a .calc edit, a new import in a pin test). This tool re-captures them
 * WITHOUT hand-editing: it runs the pin tests with REPIN_PRF=1, which writes
 * tests/engine/prf-pins.generated.json from each test's own load context (the
 * only context that reproduces the values `npm test` will later assert).
 *
 * Gating: each pin's tier-1 semantic assertion (e.g. "both outcomes reachable")
 * runs BEFORE the capture inside prfPin(); a tier-1 failure throws first, so a
 * run with already-broken semantics fails loudly and never rewrites that pin.
 *
 * --test-concurrency=1 serializes the two files so their shared JSON writes
 * cannot race. Usage: `npm run repin:prf` (or `node tools/repin-prf.js`).
 */

import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import path from 'node:path';

const ROOT = path.join(import.meta.dirname, '..');
const PIN_FILE = path.join(ROOT, 'tests/engine/prf-pins.generated.json');
const FILES = [
  'tests/engine/till-settle.test.js',
  'tests/engine/till-woplus.test.js',
];

console.log('Re-capturing PRF pins (tier-1 gated) …\n');

const res = spawnSync(
  process.execPath,
  ['--test', '--test-concurrency=1', ...FILES],
  { cwd: ROOT, env: { ...process.env, REPIN_PRF: '1' }, stdio: 'inherit' },
);

if (res.status !== 0) {
  console.error(
    '\n✗ A pin test FAILED under REPIN_PRF — tier-1 semantics are broken, so ' +
    'the affected pin was NOT re-captured. Fix the semantics first.');
  process.exit(res.status || 1);
}

console.log('\n✓ Pins re-captured to tests/engine/prf-pins.generated.json:\n');
console.log(readFileSync(PIN_FILE, 'utf8'));
console.log('Review the diff and commit the generated JSON.');
