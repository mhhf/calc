/**
 * Meta-test: every tests/**\/*.test.js must be registered in at least one
 * npm test suite. Self-enforcing guard against the blind spot that let two
 * real regressions hide in 14 unregistered files (TODO_0272 C1): `npm test`
 * and tools/test-bun.sh both derive their file list from package.json, so an
 * unregistered file is silently never run — passing OR failing.
 *
 * A deferred test that self-skips via feature detection STILL gets registered
 * here, so it auto-activates the day its feature lands. The allowlist is empty
 * by policy; add an entry only with a written reason and it must NOT be
 * registered (the "allowlist not stale" check enforces that).
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, statSync } from 'fs';
import path from 'path';

// file → reason. Empty by policy. An allowlisted file must be genuinely
// unregisterable (e.g. requires a runtime absent in CI); document why.
const ALLOWLIST = new Map([]);

const repoRoot = path.join(import.meta.dirname, '..');

function walk(dir) {
  let out = [];
  for (const entry of readdirSync(dir)) {
    const p = path.join(dir, entry);
    if (statSync(p).isDirectory()) out = out.concat(walk(p));
    else if (entry.endsWith('.test.js')) out.push(path.relative(repoRoot, p));
  }
  return out;
}

function registeredFiles() {
  const pkg = JSON.parse(readFileSync(path.join(repoRoot, 'package.json'), 'utf8'));
  const scripts = pkg.scripts || {};
  const suites = Object.keys(scripts).filter(s => s === 'test' || s.startsWith('test:'));
  const reg = new Set();
  for (const s of suites) {
    for (const m of (scripts[s].match(/tests\/[^\s'"]+\.test\.js/g) || [])) reg.add(m);
  }
  return reg;
}

describe('test-suite registration', () => {
  it('every tests/**/*.test.js is registered in an npm suite', () => {
    const reg = registeredFiles();
    const onDisk = walk(path.join(repoRoot, 'tests')).sort();
    const missing = onDisk.filter(f => !reg.has(f) && !ALLOWLIST.has(f));
    assert.deepEqual(
      missing, [],
      `Unregistered test files (add to a package.json test suite, or to the ` +
      `ALLOWLIST in this file with a reason):\n  ${missing.join('\n  ')}`
    );
  });

  it('ALLOWLIST is not stale', () => {
    const reg = registeredFiles();
    for (const [f] of ALLOWLIST) {
      assert.ok(!reg.has(f),
        `${f} is both allowlisted and registered — remove it from the ALLOWLIST`);
    }
  });
});
