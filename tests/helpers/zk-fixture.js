/**
 * Shared helper for ZK golden fixture management.
 *
 * Usage:
 *   import { saveOrAssertFixture } from '../helpers/zk-fixture.js';
 *   saveOrAssertFixture(FIXTURE_DIR, 'identity', witness);
 *
 * Behaviour:
 *   - ZK_REGEN=1  → write/overwrite the golden file and return.
 *   - default      → if the golden exists: deepStrictEqual against it (pins the fixture).
 *                    if the golden does NOT exist: write it (first-time creation) and log a notice.
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
    // First-time creation: write the golden so the next run can pin against it.
    console.log(`  [zk-fixture] creating golden: ${filepath}`);
    fs.mkdirSync(fixtureDir, { recursive: true });
    fs.writeFileSync(filepath, JSON.stringify(data, null, 2));
    return filepath;
  }

  // Default: assert that freshly generated data matches the committed golden.
  // Normalize data through JSON serialization so that non-JSON types (Map, Set, etc.)
  // are represented the same way they appear on disk (Map → {}, etc.).
  const serialized = JSON.stringify(data, null, 2);
  const golden = fs.readFileSync(filepath, 'utf8');
  assert.strictEqual(serialized, golden, `ZK fixture mismatch: ${name}.json — run ZK_REGEN=1 npm run test:zk to regenerate`);
  return filepath;
}
