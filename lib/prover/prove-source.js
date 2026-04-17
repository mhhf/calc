/**
 * prove-source — string source → proof-tree/v1 JSON, with on-disk cache.
 *
 * Two modes:
 *
 *   • `sequent` (default, `{proof ill}`) — parse the body as a sequent and
 *     prove it with the focused prover. No `#import` support in this
 *     release — user program clauses aren't threaded into focused search.
 *
 *   • `backchain` (`{proof ill backchain}`) — parse the body as a
 *     predicate atom (e.g. `plus (i e) (i e) R`), optionally preceded by
 *     a single `#import(path)` line. The atom is resolved via SLD
 *     backchaining against the imported program's clauses; the result
 *     is a proof-tree/v1 tree where each node is a clause / type /
 *     FFI resolution step.
 *
 * Sandbox:
 *   `#import(path)` is resolved relative to `calculus/ill/` (the sandbox
 *   root). Absolute paths and paths that escape the root are rejected.
 *   That root covers `programs/` and `prelude/` — everything a real
 *   proof block might want.
 *
 * Cache key: sha256 of (format_version, calculus, profile, mode,
 * imports_tree_hash, body). Editing any imported file changes the
 * transitive content hash → key changes → fresh prove. Stale entries
 * accumulate (callers wipe the dir on a clean rebuild).
 *
 * Return shape: `{ ok, key, cacheHit, tree?, error? }`. Parse / sandbox /
 * prover failures set `ok=false` with `error`; on prover-miss, `tree`
 * may still be null.
 */

'use strict';

const path = require('path');
const fs = require('fs');
const crypto = require('crypto');

const calculusLoader = require('../calculus');
const proverAuto = require('./strategy/auto');
const { sequentParser } = require('../parser/sequent-parser');
const { serializeTree, FORMAT_VERSION } = require('./serialize-tree');
const { backchainWithTree } = require('./backchain-tree');
const mde = require('../engine');
const convert = require('../engine/convert');
const { makeILLBackchainOpts } = require('../engine/ill/backchain-ill');

// Sandbox root — path containment is checked against this prefix. All
// imports must resolve inside. Covers both `programs/` and `prelude/`.
const SANDBOX_ROOT = path.resolve(__dirname, '..', '..', 'calculus', 'ill');

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

/**
 * Peel `#import(path)` lines (and blank/comment lines interleaved with
 * them) from the top of `source`; everything after the last import is
 * the body. Imports deeper in the source are left alone — they belong
 * to the calculus's own import mechanism and only fire when imported
 * files are themselves parsed.
 */
function parseHeader(source) {
  const lines = source.split(/\r?\n/);
  const imports = [];
  let i = 0;
  for (; i < lines.length; i++) {
    const line = lines[i].trim();
    if (line === '') continue;
    if (line.startsWith('%')) continue;
    const m = line.match(/^#import\s*\(\s*([^)]+?)\s*\)\s*$/);
    if (!m) break;
    imports.push(m[1]);
  }
  const body = lines.slice(i).join('\n').trim();
  return { imports, body };
}

/** Resolve a relative import path against the sandbox root. Throws on escape. */
function resolveImport(rel) {
  if (typeof rel !== 'string' || !rel) throw new Error('empty import path');
  if (path.isAbsolute(rel)) {
    throw new Error(`absolute imports rejected: ${rel}`);
  }
  const resolved = path.resolve(SANDBOX_ROOT, rel);
  if (resolved !== SANDBOX_ROOT && !resolved.startsWith(SANDBOX_ROOT + path.sep)) {
    throw new Error(`import escapes sandbox: ${rel}`);
  }
  if (!fs.existsSync(resolved)) {
    throw new Error(`import not found: ${rel}`);
  }
  return resolved;
}

/**
 * Content hash over an import's transitive dependency tree. Used in the
 * cache key so edits anywhere in the dep graph invalidate the entry.
 * Returns a hex-encoded 32-bit number (hashCombine output).
 */
function importTreeDigest(absPath) {
  const tree = convert.buildImportTree(absPath);
  const hashes = convert.computeTreeHashes(tree);
  const rootHash = hashes.get(absPath);
  return (rootHash >>> 0).toString(16);
}

function hashKey(calcName, profile, mode, importsDigest, body) {
  return crypto
    .createHash('sha256')
    .update(FORMAT_VERSION)
    .update('\0')
    .update(String(calcName))
    .update('\0')
    .update(String(profile))
    .update('\0')
    .update(String(mode))
    .update('\0')
    .update(String(importsDigest))
    .update('\0')
    .update(String(body))
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
 * Load an ILL program and all its transitive imports. Returns a calc
 * context with `clauses` + `definitions` + `backwardOpts`.
 *
 * Single-import case uses `mde.load(path, {cache:true})` — disk-cached.
 * Multi-import is rare enough that we punt: users who need it can
 * create a wrapper `.ill` file that `#import`s each dependency.
 */
function loadProgram(importPaths) {
  if (importPaths.length === 0) return null;
  if (importPaths.length > 1) {
    throw new Error(
      `multiple #import lines not supported in a proof block; ` +
      `create a wrapper .ill file that imports all dependencies`,
    );
  }
  return mde.load(importPaths[0], { cache: true });
}

/**
 * @param {Object} opts
 * @param {string} [opts.calculus='ill']
 * @param {string} [opts.profile='default']
 * @param {string} [opts.mode='sequent']  `sequent` | `backchain`
 * @param {boolean} [opts.useFFI=true] - backchain mode: false forces clause expansion
 * @param {string} opts.source - Raw block body (may contain leading `#import` lines)
 * @param {string} [opts.cacheDir]
 * @param {number} [opts.maxDepth=50] - sequent prover depth cap (backchain uses 200)
 * @returns {Promise<{ok, tree?, key, cacheHit, error?}>}
 */
async function proveSource(opts) {
  if (!opts || typeof opts.source !== 'string') {
    throw new TypeError('proveSource: { source: string } required');
  }
  const calcName = opts.calculus || 'ill';
  const profile = opts.profile || 'default';
  const mode = opts.mode || 'sequent';
  const cacheDir = opts.cacheDir || null;
  const rawSource = opts.source.trim();

  // Header split — imports live only in backchain mode for this release.
  const { imports: relImports, body } = parseHeader(rawSource);

  if (mode === 'sequent' && relImports.length > 0) {
    return {
      ok: false,
      error:
        `#import is only supported in backchain mode; ` +
        `use \`{proof ill backchain}\` or remove the import`,
      key: hashKey(calcName, profile, mode, '', rawSource),
      cacheHit: false,
    };
  }

  // Resolve + hash the import tree (sandboxed).
  let absImports;
  let importsDigest = '';
  try {
    absImports = relImports.map(resolveImport);
    if (absImports.length > 0) {
      importsDigest = absImports.map(importTreeDigest).join(',');
    }
  } catch (e) {
    return {
      ok: false,
      error: e.message,
      key: hashKey(calcName, profile, mode, '', rawSource),
      cacheHit: false,
    };
  }

  const key = hashKey(calcName, profile, mode, importsDigest, body);
  const cached = readCache(cacheDir, key);
  if (cached) return { ...cached, key, cacheHit: true };

  // Calculus load (cached per-process).
  try {
    await getCalculus(calcName);
  } catch (e) {
    return { ok: false, error: e.message, key, cacheHit: false };
  }

  if (mode === 'backchain') {
    return proveBackchain({ body, absImports, calcName, profile, key, cacheDir, opts });
  }
  return proveSequent({ body, calcName, profile, key, cacheDir, opts });
}

function proveSequent({ body, calcName, profile, key, cacheDir, opts }) {
  const parser = _parserCache.get(calcName);
  const prover = _proverCache.get(calcName);

  let sequent;
  try {
    sequent = parser.parseSequent(body);
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

  const out = { ok: !!(result && result.success), tree, key, cacheHit: false };
  if (tree) writeCache(cacheDir, key, { ok: out.ok, tree });
  return out;
}

function proveBackchain({ body, absImports, calcName, profile, key, cacheDir, opts }) {
  // Load the imported program (clauses + definitions + backwardOpts).
  let prog;
  try {
    prog = loadProgram(absImports);
  } catch (e) {
    return { ok: false, error: e.message, key, cacheHit: false };
  }
  if (!prog) {
    return {
      ok: false,
      error:
        `backchain mode requires an #import line naming the program to chain against`,
      key,
      cacheHit: false,
    };
  }

  // Parse the body as a predicate atom. parseExpr uses the engine
  // expression parser (same one convert.js uses for clause bodies), so
  // user-defined predicates from the imported program parse naturally.
  let goalHash;
  try {
    goalHash = convert.parseExpr(body);
  } catch (e) {
    return { ok: false, error: `parse error: ${e.message}`, key, cacheHit: false };
  }

  const illOpts = makeILLBackchainOpts();
  // `teaching` profile forces clause expansion — FFI is the fast path but
  // its proof tree is an opaque `ffi` leaf. Teaching mode is how users get
  // the full step-by-step derivation rendered.
  const useFFI = opts.useFFI !== undefined
    ? !!opts.useFFI
    : profile !== 'teaching';
  const runOpts = {
    ...illOpts,
    ...(prog.backwardOpts || {}),
    calculus: calcName,
    profile,
    maxDepth: opts.maxDepth || 200,
    useFFI,
  };

  let res;
  try {
    res = backchainWithTree(goalHash, prog.clauses, prog.definitions, runOpts);
  } catch (e) {
    return { ok: false, error: `prover error: ${e.message}`, key, cacheHit: false };
  }

  const out = {
    ok: !!(res && res.success),
    tree: res && res.tree ? res.tree : null,
    key,
    cacheHit: false,
  };
  if (out.tree) writeCache(cacheDir, key, { ok: out.ok, tree: out.tree });
  else if (!out.ok) out.error = out.error || 'backchain: no derivation found';
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
  parseHeader,
  resolveImport,
  SANDBOX_ROOT,
  _resetCache,
};
