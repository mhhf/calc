/**
 * Two-tier PRF golden pins (TODO_0272 M8).
 *
 * The till within-instant chooser is a stateless PRF that mixes the arena-layout
 * -dependent state hash, so the EXACT draw sequence shifts on any interning
 * change (a .calc edit, a new earlier test, node-vs-bun module order). A single
 * hand-edited `assert.deepEqual([...], [...])` guarded only by human intent is
 * therefore high-churn and bun-invisible. This splits the concern:
 *
 *   • TIER 1 — a SEMANTIC invariant (e.g. "both outcomes reachable across a
 *     seed range"). Interning-independent, runs under node AND bun, NEVER
 *     re-pinned. This is the real guard.
 *   • TIER 2 — the exact draw for specific seeds. Interning-specific, node-only.
 *     Stored in `prf-pins.generated.json`, re-captured MECHANICALLY by
 *     `npm run repin:prf` (which runs the pin tests with REPIN_PRF=1) — never
 *     hand-edited — and only ever written when tier 1 passes in the same run.
 *
 * Usage in a test:
 *   prfPin('some/key', {
 *     tier1: () => { ...assert the semantic invariant... },
 *     compute: () => calc.settle(...).events.map(e => e.alt),
 *   });
 */

import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';

const PIN_FILE = path.join(import.meta.dirname, 'prf-pins.generated.json');
const REPIN = !!process.env.REPIN_PRF;

function readPins() {
  try { return JSON.parse(fs.readFileSync(PIN_FILE, 'utf8')); } catch { return {}; }
}

export function prfPin(key, { tier1, compute }) {
  // Tier 1 ALWAYS runs — the interning-independent guard, node and bun alike.
  // In REPIN mode a tier-1 failure throws HERE, before any capture: the pin is
  // never re-written from a run whose semantics are already broken.
  tier1();

  // Tier 2 is the exact interning-specific draw — node-only (bun interns in a
  // different order, so the sequence legitimately differs and is not pinned).
  if (typeof Bun !== 'undefined') return;

  const fresh = compute();

  if (REPIN) {
    const pins = readPins();
    pins[key] = fresh;
    // Stable key order for a clean diff.
    const ordered = {};
    for (const k of Object.keys(pins).sort()) ordered[k] = pins[k];
    fs.writeFileSync(PIN_FILE, JSON.stringify(ordered, null, 2) + '\n');
    return;
  }

  const pins = readPins();
  assert.ok(Object.prototype.hasOwnProperty.call(pins, key),
    `PRF pin '${key}' is missing from prf-pins.generated.json — run \`npm run repin:prf\``);
  assert.deepEqual(fresh, pins[key],
    `PRF pin '${key}' drifted (likely an interning shift or a PRF-internals ` +
    `change). Tier-1 semantics still hold, so verify intent, then re-capture ` +
    `mechanically with \`npm run repin:prf\` — do NOT hand-edit.`);
}
