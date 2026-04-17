/**
 * prove-source — string source → proof-tree/v1 JSON, with on-disk cache.
 *
 * Thin glue between a `{proof <cal> <profile>}` code block and the rest of
 * the prover stack:
 *
 *   source (string) → parse sequent → prove → serialize → cache
 *
 * Used by the doc-compile pipeline (src/ui/lib/markdown.ts) to turn proof
 * blocks in markdown into embedded JSON for the client renderer. Calculus +
 * parser + prover instances are memoized per-process so repeated blocks in
 * the same build share one load.
 *
 * Cache key: sha256 of (calculus, profile, trimmed source). Miss → prove +
 * write; hit → read JSON off disk. Invalidation is by key: any change to
 * source / profile / calculus name produces a new key; stale entries simply
 * accumulate (callers may wipe the dir on a rebuild).
 *
 * Return shape: always `{ ok, key, cacheHit, tree?, error? }`. On prove
 * failure `ok` is false but `tree` may still be present (partial proof).
 * On parser or runtime errors, `tree` is null and `error` explains.
 *
 * NOTE: `profile` is a string pass-through in v1. TODO_0212 will introduce
 * real dispatch (execution profiles: default / guided / verified / …);
 * until then the field only affects cache keying.
 */

'use strict';

const path = require('path');
const fs = require('fs');
const crypto = require('crypto');

const calculusLoader = require('../calculus');
const proverAuto = require('./strategy/auto');
const { sequentParser } = require('../parser/sequent-parser');
const { serializeTree, FORMAT_VERSION } = require('./serialize-tree');

// Per-process memo: loading ILL hits the disk + runs the calc/rules
// pipeline; repeat-calls inside one build would otherwise be O(N*load).
const _calcCache = new Map();
const _parserCache = new Map();
const _proverCache = new Map();

async function getCalculus(name) {
  if (_calcCache.has(name)) return _calcCache.get(name);
  let cal;
  if (name === 'ill') {
    cal = await calculusLoader.loadILL();
  } else {
    throw new Error(`unknown calculus: ${name}`);
  }
  _calcCache.set(name, cal);
  _parserCache.set(name, sequentParser(cal));
  _proverCache.set(name, proverAuto.create(cal));
  return cal;
}

function hashKey(calcName, profile, source) {
  return crypto
    .createHash('sha256')
    .update(FORMAT_VERSION)
    .update('\0')
    .update(String(calcName))
    .update('\0')
    .update(String(profile))
    .update('\0')
    .update(String(source))
    .digest('hex')
    .slice(0, 16);
}

function readCache(cacheDir, key) {
  if (!cacheDir) return null;
  try {
    const raw = fs.readFileSync(path.join(cacheDir, key + '.json'), 'utf-8');
    const parsed = JSON.parse(raw);
    if (parsed && parsed.tree && parsed.tree.format === FORMAT_VERSION) return parsed;
  } catch {}
  return null;
}

function writeCache(cacheDir, key, payload) {
  if (!cacheDir) return;
  try {
    fs.mkdirSync(cacheDir, { recursive: true });
    fs.writeFileSync(
      path.join(cacheDir, key + '.json'),
      JSON.stringify(payload),
    );
  } catch {}
}

/**
 * @param {Object} opts
 * @param {string} [opts.calculus='ill'] - Calculus name
 * @param {string} [opts.profile='default'] - Execution profile (TODO_0212)
 * @param {string} opts.source - Sequent source ("A |- A")
 * @param {string} [opts.cacheDir] - Absolute path to on-disk cache directory
 * @param {number} [opts.maxDepth=50] - Prover depth cap
 * @returns {Promise<{ok: boolean, tree?: object, key: string, cacheHit: boolean, error?: string}>}
 */
async function proveSource(opts) {
  if (!opts || typeof opts.source !== 'string') {
    throw new TypeError('proveSource: { source: string } required');
  }
  const calcName = opts.calculus || 'ill';
  const profile = opts.profile || 'default';
  const source = opts.source.trim();
  const cacheDir = opts.cacheDir || null;

  const key = hashKey(calcName, profile, source);

  const cached = readCache(cacheDir, key);
  if (cached) return { ...cached, key, cacheHit: true };

  let parser, prover;
  try {
    await getCalculus(calcName);
    parser = _parserCache.get(calcName);
    prover = _proverCache.get(calcName);
  } catch (e) {
    return { ok: false, error: e.message, key, cacheHit: false };
  }

  let sequent;
  try {
    sequent = parser.parseSequent(source);
  } catch (e) {
    return { ok: false, error: `parse error: ${e.message}`, key, cacheHit: false };
  }

  let result;
  try {
    result = prover.prove(sequent, { maxDepth: opts.maxDepth || 50 });
  } catch (e) {
    return { ok: false, error: `prover error: ${e.message}`, key, cacheHit: false };
  }

  let tree = null;
  if (result && result.proofTree) {
    tree = serializeTree(result.proofTree, { calculus: calcName, profile });
  }

  const out = {
    ok: !!(result && result.success),
    tree,
    key,
    cacheHit: false,
  };

  if (tree) writeCache(cacheDir, key, { ok: out.ok, tree });
  return out;
}

/**
 * Purge all memoized calculus/parser/prover instances. Primarily for tests.
 */
function _resetCache() {
  _calcCache.clear();
  _parserCache.clear();
  _proverCache.clear();
}

module.exports = {
  proveSource,
  hashKey,
  _resetCache,
};
