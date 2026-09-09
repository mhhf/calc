/**
 * Minimal-essence enforcement ratchet (RES_0143 E1 + E3).
 *
 * Two mechanical guards that keep lib/ from re-accreting instance
 * knowledge after the 2026-09 audit:
 *
 * E1 — domain-literal lint: lib/ code (comments stripped) may not
 *   contain quoted instance vocabulary — calculus/program names that
 *   belong in calculus configs (EVM predicates, constraint predicate
 *   names, profile names). The allowlist freezes the audited residue
 *   per file and may only SHRINK; a new hit is smuggled calculus
 *   knowledge — thread the name through cc instead.
 *
 * E3 — engine tier manifest: every file under lib/engine/ must be
 *   classified. Adding a file without classifying it here fails loudly
 *   — the classification is the conscious act the audit demands:
 *     core    — matching / iteration / substitution / state / compile /
 *               load / SLD; the essence plus what it cannot run without
 *     opt     — semantics-free optimization (deletable; bare profile +
 *               profile-differential.test.js are the deletability gate)
 *     cache   — persistence/versioning infrastructure
 *     root    — the composition root (may import opt/, sibling layers)
 *     debug   — observability/tooling
 *   The timed and measure layers live OUTSIDE lib/engine (lib/timed/,
 *   lib/measure/) — layer-dag.test.js pins that direction.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import path from 'path';

const REPO = path.resolve(import.meta.dirname, '../..');
const LIB = path.join(REPO, 'lib');

function walkJs(dir, out = []) {
  for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
    if (ent.name === 'node_modules') continue;
    const full = path.join(dir, ent.name);
    if (ent.isDirectory()) walkJs(full, out);
    else if (ent.name.endsWith('.js') && !ent.name.endsWith('.test.js')) out.push(full);
  }
  return out;
}

const stripComments = (s) => s
  .replace(/\/\*[\s\S]*?\*\//g, '')
  .replace(/\/\/.*$/gm, '');

describe('minimal-essence ratchet (RES_0143)', () => {
  it('E1: lib/ holds no quoted instance vocabulary (shrink-only allowlist)', () => {
    // Instance names that live in calculus configs / program files, not lib/:
    // EVM state predicates, terminal atoms, constraint predicate names,
    // container-lookup predicates, the old profile name.
    const WORDS = ['evm', 'bytecode', 'calldata', 'stop', 'revert', 'arr_get',
      'pc', 'stack', 'eq', 'neq', 'multisig', 'sha3'];
    const RE = new RegExp(`'(${WORDS.join('|')})'`, 'g');
    // Audited residue (2026-09-08) — counts may only go DOWN:
    const ALLOWED = {
      // C2 Hypothesis-S advisory lint recognizes the qsub/div/mod/eq
      // bit-test MENU IDIOM over the shared numeric prelude's names.
      // Advisory-only (worst case: a spurious or missing warning, never
      // a semantic effect); a cc-declared idiom descriptor would be
      // over-engineering for a lint heuristic.
      'timed/timed-lint.js': { eq: 1 },
    };
    const found = {};
    for (const f of walkJs(LIB)) {
      const src = stripComments(fs.readFileSync(f, 'utf8'));
      const counts = {};
      for (const m of src.matchAll(RE)) counts[m[1]] = (counts[m[1]] || 0) + 1;
      if (Object.keys(counts).length) found[path.relative(LIB, f)] = counts;
    }
    assert.deepEqual(found, ALLOWED,
      'quoted instance vocabulary in lib/ — thread the name through the ' +
      'calculus config (cc) instead, or shrink the allowlist if you removed one');
  });

  it('E3: every lib/engine file is tier-classified', () => {
    const TIERS = {
      // ── core: the essence + what it cannot run without ──
      'match.js': 'core', 'forward.js': 'core', 'explore.js': 'core',
      'strategy.js': 'core', 'state-ops.js': 'core', 'fact-set.js': 'core',
      'compile.js': 'core', 'convert.js': 'core', 'backchain.js': 'core',
      'pattern-utils.js': 'core', 'formula-utils.js': 'core',
      'rule-analysis.js': 'core', 'resolve-all.js': 'core',
      'constraint.js': 'core', 'grades.js': 'core', 'prf.js': 'core',
      'reserved-preds.js': 'core', 'materialize.js': 'core',
      'cc-schema.js': 'core',       // the declared cc port contract (F1)
      'certify-confluence.js': 'core', // destination-discipline confluence certificate (P2, THY_0036)
      'sorts.js': 'core', 'type-check.js': 'core',
      'compose.js': 'core',            // P1-P4 = grade-0 erasure (SEMANTIC)
      'compose-profile.js': 'debug',
      // ── opt: deletable, profile-gated ──
      // (the opt-at-root tier dissolved in RES_0143 F4: deltaBypass rides
      // the matchOpts opt protocol, backward-cache's lifecycle lives at
      // the composition root — no generic file imports opt/ anymore)
      'optimizer.js': 'opt',
      'opt/backward-cache.js': 'opt', 'opt/delta-bypass.js': 'opt',
      'opt/fingerprint.js': 'opt', 'opt/disc-tree.js': 'opt',
      'opt/ffi.js': 'opt', 'opt/compiled-clauses.js': 'opt',
      'opt/existential-compile.js': 'opt', 'opt/prediction.js': 'opt',
      'opt/structural-memo.js': 'opt',
      'opt/compose-fuse.js': 'opt', 'opt/compose-sroa.js': 'opt',
      // ── cache ──
      'cache/store-binary.js': 'cache', 'cache/engine-version.js': 'cache',
      'cache/cache-flags.js': 'cache', 'cache/cache-evict.js': 'cache',
      'cache/compose-cache.js': 'cache', 'cache/load-cache.js': 'cache',
      // ── root / debug ──
      'index.js': 'root',
      'show.js': 'debug', 'tree-utils.js': 'debug',
    };
    const actual = walkJs(path.join(LIB, 'engine'))
      .map(f => path.relative(path.join(LIB, 'engine'), f)).sort();
    const listed = Object.keys(TIERS).sort();
    assert.deepEqual(actual, listed,
      'lib/engine file set drifted from the tier manifest — classify new ' +
      'files here (and ask: does it belong in lib/engine at all?)');
  });
});
