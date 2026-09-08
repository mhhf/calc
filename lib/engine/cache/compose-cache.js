/**
 * Compose disk cache (RES_0143 M3 — extracted from index.js).
 *
 * Persists the full post-compose Store snapshot using the store-binary
 * format. On cache hit, Store.restore() replaces parsing AND compose —
 * cold E2E becomes ~40ms (restore + compileRule) instead of ~210ms
 * (parse + compile + compose).
 *
 * Cache key: SHA-256(canonical string of tree hashes, bytecode hex,
 * opts, engineVersion, cache-flag fingerprint, snapshot-format version).
 * Snapshot metadata contains definitions, clauses, queries, final rule
 * list, and SELL infrastructure so _buildCalc can run with
 * skipCompose: true — the builder is INJECTED (loadCSnap's buildCalc
 * parameter); this module holds no engine-construction knowledge.
 */

import fs from 'fs';
import path from 'path';
import zlib from 'zlib';
import crypto from 'crypto';
import Store from '../../kernel/store.js';
import { serialize, deserialize, compact } from './store-binary.js';
import { engineVersion } from './engine-version.js';
import { cacheFlagFingerprint } from './cache-flags.js';

const COMPOSE_DISK_VERSION = 4; // 3→4: lnl layer moved to family/lnl/ (TODO_0086)

// Read a snapshot file: open, gunzip-if-gzipped (magic 0x1f 0x8b), deserialize.
// Caller is responsible for Store.restore() and metadata validation.
function _readSnapshotFile(filePath) {
  let buf = fs.readFileSync(filePath);
  if (buf[0] === 0x1f && buf[1] === 0x8b) buf = zlib.gunzipSync(buf);
  return deserialize(buf);
}

/**
 * Compute compose disk cache key.
 *
 * Closes hazards H7 (bytecode API — content-hash of hex bytes, no
 * caller-declared scopeGuard ID), H8 (flag registry — cacheFlagFingerprint),
 * H9 (engine version — content-hash of lib/).
 *
 * @param {Map} treeHashes      manifest[path → contentHash]
 * @param {string} absPath      root file absolute path
 * @param {string|null} bcHex   bytecode hex (or null if no bytecode input)
 * @param {Object} flagOpts     compose-affecting opts (fuseBasicBlocks, cacheVersion)
 */
function _composeCacheKey(treeHashes, absPath, bcHex, flagOpts) {
  const parts = [
    'ev=' + engineVersion(),
    'file=' + String(treeHashes.get(absPath) | 0),
  ];
  if (bcHex) {
    const bcH = crypto.createHash('sha256').update(bcHex).digest('hex').slice(0, 16);
    parts.push('bc=' + bcH);
  }
  parts.push(cacheFlagFingerprint(flagOpts || {}));
  parts.push('v=' + COMPOSE_DISK_VERSION);
  return crypto.createHash('sha256').update(parts.join(';')).digest('hex').slice(0, 16);
}

// Priors table (BigInt pairs) ↔ JSON ('n/d' strings) for cache metadata.
const _serPriors = (m) => (m && m.size)
  ? Object.fromEntries([...m].map(([k, [n, d]]) => [k, `${n}/${d}`])) : {};
const _desPriors = (o) => new Map(Object.entries(o || {}).map(([k, v]) => {
  const [n, d] = v.split('/');
  return [k, [BigInt(n), BigInt(d)]];
}));

/**
 * Save full post-compose Store snapshot to disk.
 * Includes all metadata needed to reconstruct the calc context without
 * reparsing or recomposing.
 */
function _saveCSnap(cachePath, calc, definitions, clauses, queries,
    argNamesTable, querySettings, splitQueries, moduleDecls, rootLabel, labelDeps, sortVarsTable) {
  try {
    const metadata = {
      _composeCache: COMPOSE_DISK_VERSION,
      sortVarsTable: sortVarsTable ? Object.fromEntries(sortVarsTable) : {},
      types: Object.fromEntries(definitions),
      clauses: Object.fromEntries(
        Array.from(clauses.entries()).map(([k, v]) => [k, v])
      ),
      // Final rule list (post-compose): name + hash + sourceLabel
      forwardRules: calc._compiledRules.map(r => ({
        name: r.name, hash: r.hash, sourceLabel: r.sourceLabel || null
      })),
      queries: Object.fromEntries(queries),
      argNamesTable: argNamesTable ? Object.fromEntries(argNamesTable) : {},
      querySettings: querySettings
        ? Object.fromEntries([...querySettings].map(([k, v]) => [k, v])) : {},
      splitQueries: splitQueries
        ? Object.fromEntries([...splitQueries].map(([k, v]) => [k, v])) : {},
      moduleDecls: moduleDecls || [],
      rootLabel: rootLabel || null,
      priors: _serPriors(calc.priors),
      labelDeps: labelDeps
        ? Object.fromEntries([...labelDeps].map(([k, v]) => [k, [...v]])) : {}
    };
    const snap = Store.snapshot(metadata);
    const bin = compact(snap);
    const buf = serialize(bin);
    fs.mkdirSync(path.dirname(cachePath), { recursive: true });
    // Atomic write: tmpfile + rename. Prevents partial-write corruption when
    // concurrent readers race with a writer (rename() is atomic on POSIX).
    const tmpPath = `${cachePath}.tmp.${process.pid}.${Date.now()}`;
    fs.writeFileSync(tmpPath, buf);
    fs.renameSync(tmpPath, cachePath);
  } catch (e) {
    // Non-fatal — fresh parse+compose on next load
  }
}

/**
 * Load post-compose Store snapshot from disk.
 * Returns calc context or null on miss/corruption.
 */
function _loadCSnap(cachePath, sellOpts, buildCalc) {
  try {
    if (!fs.existsSync(cachePath)) return null;
    const data = _readSnapshotFile(cachePath);
    if (!data.metadata || data.metadata._composeCache !== COMPOSE_DISK_VERSION) return null;
    Store.restore(data);

    const meta = data.metadata;
    const definitions = new Map(Object.entries(meta.types));
    const clauses = new Map(Object.entries(meta.clauses));
    const queries = new Map(Object.entries(meta.queries));
    const argNamesTable = meta.argNamesTable
      ? new Map(Object.entries(meta.argNamesTable)) : new Map();
    const sortVarsTable = meta.sortVarsTable
      ? new Map(Object.entries(meta.sortVarsTable)) : new Map();
    const querySettings = meta.querySettings
      ? new Map(Object.entries(meta.querySettings)) : new Map();
    const splitQueries = meta.splitQueries
      ? new Map(Object.entries(meta.splitQueries)) : new Map();
    const moduleDecls = meta.moduleDecls || [];
    const rootLabel = meta.rootLabel || (sellOpts && sellOpts.rootLabel) || null;
    const labelDeps = meta.labelDeps
      ? new Map(Object.entries(meta.labelDeps).map(([k, v]) => [k, new Set(v)]))
      : (sellOpts && sellOpts.labelDeps) || new Map();

    // Reconstruct raw forward rules from stored name+hash pairs
    const forwardRules = meta.forwardRules.map(r => ({
      name: r.name,
      hash: r.hash,
      antecedent: Store.child(r.hash, 0),
      consequent: Store.child(r.hash, 1),
      sourceLabel: r.sourceLabel || null
    }));

    // Call _buildCalc with skipCompose — compose is already baked into forwardRules.
    // calculusConfig comes from the caller (audit 2026-09-02: previously
    // this rebuilt under the silent ILL default — a non-ILL compose cache
    // would have hydrated with the wrong config).
    return buildCalc(definitions, clauses, forwardRules, queries, {
      argNamesTable, sortVarsTable, rootLabel, labelDeps, querySettings, splitQueries, moduleDecls,
      priorsTable: _desPriors(meta.priors),
      calculusConfig: sellOpts && sellOpts.calculusConfig,
      skipCompose: true
    });
  } catch (e) {
    // Corrupted — delete and fall through to fresh load
    try { fs.unlinkSync(cachePath); } catch {}
    return null;
  }
}

/**
 * Verify that cold and cached loads agree on the compose output. Compares rule
 * names (rule order + identity) — the structural contract the cache depends on.
 * Hash equality is not required because restore may renumber Store IDs after
 * compact(); the rule-name sequence is the invariant.
 */
function _verifyEq(cold, cached) {
  const coldNames = cold._compiledRules.map(r => r.name);
  const cachedNames = cached._compiledRules.map(r => r.name);
  if (coldNames.length !== cachedNames.length) {
    throw new Error(`CALC_CACHE_VERIFY: rule count divergence — cold=${coldNames.length} cached=${cachedNames.length}`);
  }
  for (let i = 0; i < coldNames.length; i++) {
    if (coldNames[i] !== cachedNames[i]) {
      throw new Error(`CALC_CACHE_VERIFY: rule[${i}] name divergence — cold='${coldNames[i]}' cached='${cachedNames[i]}'`);
    }
  }
}


export { COMPOSE_DISK_VERSION, _readSnapshotFile, _composeCacheKey, _serPriors, _desPriors, _saveCSnap, _loadCSnap, _verifyEq };
export default { COMPOSE_DISK_VERSION, _readSnapshotFile, _composeCacheKey, _saveCSnap, _loadCSnap, _verifyEq };
