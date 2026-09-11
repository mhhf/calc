/**
 * Shared helper for ZK golden fixture management.
 *
 * Usage:
 *   import { saveOrAssertFixture } from '../helpers/zk-fixture.js';
 *   saveOrAssertFixture(FIXTURE_DIR, 'identity', witness);
 *
 * Behaviour:
 *   - ZK_REGEN=1  → write/overwrite the golden file and return.
 *   - default      → if the golden exists: assert byte-equality against it (pins the fixture).
 *                    if the golden is MISSING: FAIL (a deleted golden must not silently
 *                    re-fulfil itself; create/regenerate deliberately under ZK_REGEN=1).
 *
 * On-disk format: JSON.stringify(data, null, 2) — 2-space indent, no trailing newline beyond
 * what JSON.stringify produces.
 */

import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert';

/**
 * @param {string} fixtureDir  - Directory to store/read fixtures.
 * @param {string} name        - Fixture name (without .json extension).
 * @param {unknown} data       - The freshly generated data to save or assert.
 * @returns {string}           - The full path to the fixture file.
 */
export function saveOrAssertFixture(fixtureDir, name, data) {
  const filepath = path.join(fixtureDir, `${name}.json`);

  if (process.env.ZK_REGEN) {
    // Regen mode: write unconditionally.
    fs.mkdirSync(fixtureDir, { recursive: true });
    fs.writeFileSync(filepath, JSON.stringify(data, null, 2));
    return filepath;
  }

  if (!fs.existsSync(filepath)) {
    // A MISSING golden in assert mode is a FAILURE, not a silent (re)creation
    // (audit 2026-09-11): silently writing on absent-file would let a DELETED
    // golden pass unnoticed and re-fulfil itself. Creating or regenerating a
    // golden is deliberate — do it under ZK_REGEN=1.
    assert.fail(`ZK golden missing: ${name}.json — run \`ZK_REGEN=1 npm run test:zk\` to create/regenerate it (deleted goldens are not silently recreated)`);
  }

  // Default: assert that freshly generated data matches the committed golden.
  // Normalize data through JSON serialization so that non-JSON types (Map, Set, etc.)
  // are represented the same way they appear on disk (Map → {}, etc.).
  const serialized = JSON.stringify(data, null, 2);
  const golden = fs.readFileSync(filepath, 'utf8');
  assert.strictEqual(serialized, golden, `ZK fixture mismatch: ${name}.json — run ZK_REGEN=1 npm run test:zk to regenerate`);
  return filepath;
}
