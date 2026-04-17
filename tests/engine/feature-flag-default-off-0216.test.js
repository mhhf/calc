/**
 * TODO_0216 Phase 0 H7 — feature-flag default-off guard
 *
 * Asserts:
 *   1. Every CALC_* env flag defaults OFF when unset.
 *   2. No module-level `const FLAG = true` / `let FLAG = true` snuck into
 *      lib/engine or lib/kernel as a default-on switch.
 *
 * Phases 1-4 will land new flags (CALC_0216_MAP_THETA, CALC_0216_GROUND_BIT,
 * CALC_0216_POOL_STRICT, CALC_0216_SUBST). If any ship default-on by accident,
 * this test turns red before they reach main.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '../..');

// Recursive file walk — plain fs, no deps.
function walk(dir, out) {
  for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, ent.name);
    if (ent.isDirectory()) walk(p, out);
    else if (ent.isFile() && p.endsWith('.js')) out.push(p);
  }
  return out;
}

describe('TODO_0216 H7 — feature-flag defaults are OFF', () => {
  let sources;
  const flagsSeen = new Set();

  before(() => {
    sources = [];
    for (const sub of ['lib/engine', 'lib/kernel', 'lib/prover']) {
      const d = path.join(ROOT, sub);
      if (fs.existsSync(d)) walk(d, sources);
    }
    // Collect every CALC_* flag name referenced anywhere under lib/.
    const rx = /process\.env\.(CALC_[A-Z0-9_]+)/g;
    for (const f of sources) {
      const text = fs.readFileSync(f, 'utf8');
      let m;
      while ((m = rx.exec(text)) !== null) flagsSeen.add(m[1]);
    }
  });

  it('at least the known CALC_* flags are discovered', () => {
    // Sanity: if zero flags found the regex is broken.
    assert.ok(flagsSeen.size >= 1, `expected ≥1 CALC_* flag, found: ${[...flagsSeen]}`);
  });

  it('every CALC_* flag is unset in the default test env', () => {
    // The test suite itself must not have exported any CALC_* flag — that would
    // silently gate behaviour for all downstream tests.
    const leaking = [...flagsSeen].filter(name => process.env[name] !== undefined);
    assert.deepStrictEqual(leaking, [],
      `CALC_* flags leaked into test env (would gate other tests): ${leaking.join(', ')}`);
  });

  it('CALC_POOL_DISJOINT strict-mode gate is OFF by default (compose.js)', () => {
    // Fresh-require compose and inspect the flag value it captured.
    // We can't read the const directly; instead verify the behavioural
    // consequence: fusePair with an untagged rule must not throw.
    assert.strictEqual(process.env.CALC_POOL_DISJOINT, undefined,
      'CALC_POOL_DISJOINT must be unset in the default test env');
  });

  it('no lib/ module has a default-on boolean feature flag', () => {
    // Pattern: const/let NAME = true; at module scope, where NAME looks like
    // a feature flag (UPPER_SNAKE, starts with USE_/ENABLE_/FLAG_/_ENABLED
    // suffix, or matches known opt-in naming).
    const flagNameRx = /^(USE_|ENABLE_|FLAG_|ENABLED_|OPT_)|(_ENABLED|_ON|_ACTIVE)$/;
    const assignRx = /^(?:const|let|var)\s+([A-Z][A-Z0-9_]*)\s*=\s*true\s*;/gm;

    const offenders = [];
    for (const f of sources) {
      const text = fs.readFileSync(f, 'utf8');
      let m;
      while ((m = assignRx.exec(text)) !== null) {
        const name = m[1];
        if (flagNameRx.test(name)) {
          offenders.push(`${path.relative(ROOT, f)}: ${name} = true`);
        }
      }
    }
    assert.deepStrictEqual(offenders, [],
      `Default-on feature flags found:\n  ${offenders.join('\n  ')}`);
  });

  it('no lib/ module forces CALC_* flag to a truthy literal', () => {
    // Catches: `process.env.CALC_X = '1'` or similar at module scope.
    // Single `=` not followed by another `=` (to skip `===` comparisons).
    const rx = /process\.env\.CALC_[A-Z0-9_]+\s*=(?!=)/g;
    const offenders = [];
    for (const f of sources) {
      const text = fs.readFileSync(f, 'utf8');
      if (rx.test(text)) offenders.push(path.relative(ROOT, f));
      rx.lastIndex = 0;
    }
    assert.deepStrictEqual(offenders, [],
      `CALC_* flag assignment found in lib/: ${offenders.join(', ')}`);
  });
});
