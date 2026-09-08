// @ts-check
/**
 * Two-tier file-hash load cache (RES_0143 M3 completion; audit item 7 —
 * extracted from index.js, where ~430 lines of cache machinery sat
 * beside the cache/ directory created for exactly this).
 *
 * Tier 1: full-program snapshot keyed by the content hash of the whole
 * import tree. Tier 2: imports-only (SDK) snapshot keyed by the
 * top-level import hashes — a top-file edit re-parses one file on top
 * of the restored SDK. Keys are epoch-qualified (cc.compile.cacheEpoch)
 * so .bin files compiled under one calculus never restore under
 * another.
 *
 * The compose-cache injection pattern: this module holds the cache
 * strategy; the composition root (index.js) injects what it may not
 * import — the calc builder, the fresh-load fallback, loadPrecompiled,
 * and the config-bound rule compiler — via `deps`:
 *
 *   { cc, compileRule, buildCalc, loadFresh, loadPrecompiled }
 */

import fs from 'fs';
import path from 'path';
import os from 'os';
import Store from '../../kernel/store.js';
import convert from '../convert.js';
import { serialize, compact } from './store-binary.js';
import { hashCombine, hashString } from '../../hash.js';
import { _readSnapshotFile, _serPriors } from './compose-cache.js';

// CACHE_VERSION: bump when parser/compiler changes affect binary output
// (e.g., bang arity 1→2 in SELL graded modality).
const CACHE_VERSION = 5;

/**
 * Rehydrate deserialized compiled rules: linearMeta Sets survive the
 * JSON round-trip as Arrays.
 */
function deserRules(rules) {
  return rules.map(r => {
    if (!r.linearMeta) return r;
    const lm = {};
    for (const k in r.linearMeta) {
      const m = r.linearMeta[k];
      lm[k] = {
        ...m,
        freevars: Array.isArray(m.freevars) ? new Set(m.freevars) : m.freevars,
        persistentDeps: Array.isArray(m.persistentDeps) ? new Set(m.persistentDeps) : m.persistentDeps,
      };
    }
    return { ...r, linearMeta: lm };
  });
}

/**
 * Write current Store state + metadata to binary cache file.
 * @returns {number} byte size of written file
 */
function snapToFile(cachePath, definitions, clauses, rawForwardRules, _compiledRules, queries, argNamesTable, sortVarsTable, priorsTable) {
  const metadata = {
    types: Object.fromEntries(definitions),
    clauses: Object.fromEntries(
      Array.from(clauses.entries()).map(([k, v]) => [k, v])
    ),
    forwardRules: rawForwardRules,
    // compiledRules omitted — recomputed on restore (~1.5ms, saves ~85KB)
    queries: Object.fromEntries(queries),
    argNamesTable: argNamesTable ? Object.fromEntries(argNamesTable) : {},
    sortVarsTable: sortVarsTable ? Object.fromEntries(sortVarsTable) : {},
    priors: _serPriors(priorsTable)
  };
  const snap = Store.snapshot(metadata);
  const bin = compact(snap);
  const buf = serialize(bin);
  // No gzip — compacted binary is small enough (~50KB) and gunzip costs 0.3ms
  fs.mkdirSync(path.dirname(cachePath), { recursive: true });
  fs.writeFileSync(cachePath, buf);
  return buf.length;
}

/**
 * Compute transitive closure of SDK paths from top-level imports.
 */
function _sdkPaths(tree, topLevelImports) {
  const sdkPaths = new Set();
  const nodeMap = new Map(tree.map(n => [n.path, n]));
  function add(p) {
    if (sdkPaths.has(p)) return;
    sdkPaths.add(p);
    const node = nodeMap.get(p);
    if (node) node.deps.forEach(add);
  }
  topLevelImports.forEach(add);
  return sdkPaths;
}

// ─── SELL label helpers ─────────────────────────────────────────────────────

/**
 * Build transitive dependency map from import tree: label → Set<label>.
 * Also detects label collisions (T8): two files with same stem → error.
 * @param {Array<{path: string, deps: string[]}>} tree - topo-sorted import tree
 * @returns {Map<string, Set<string>>} label → transitive dep labels
 */
function labelDeps(tree) {
  const deps = new Map();
  const labelToPath = new Map(); // for collision detection
  const nodeMap = new Map();     // path → node for O(1) lookup

  for (const node of tree) {
    const label = path.basename(node.path, path.extname(node.path));
    if (labelToPath.has(label)) {
      throw new Error(
        `Label collision: '${label}' matches both ${labelToPath.get(label)} and ${node.path}. ` +
        `Rename one of the files to disambiguate.`
      );
    }
    labelToPath.set(label, node.path);
    nodeMap.set(node.path, node);
  }

  function transitive(nodePath, visited) {
    const label = path.basename(nodePath, path.extname(nodePath));
    if (visited.has(label)) return visited;
    visited.add(label);
    const node = nodeMap.get(nodePath);
    if (node) {
      for (const dep of node.deps) transitive(dep, visited);
    }
    return visited;
  }

  for (const node of tree) {
    const label = path.basename(node.path, path.extname(node.path));
    const all = transitive(node.path, new Set());
    all.delete(label); // don't include self
    deps.set(label, all);
  }
  return deps;
}

// ─── Cache-aware load helpers ───────────────────────────────────────────────

/**
 * Try loading from a binary cache file. Returns calc context or null.
 * Deletes corrupted cache files gracefully.
 */
function _tryLoadFromCache(cachePath, sellOpts, deps) {
  try {
    if (fs.existsSync(cachePath)) return deps.loadPrecompiled(cachePath, sellOpts);
  } catch (e) {
    try { fs.unlinkSync(cachePath); } catch {}
  }
  return null;
}

/**
 * Restore SDK from binary cache, parse top file on top.
 * Returns intermediate result (raw data for further caching).
 */
function _loadCached(topFilePath, sdkCachePath, sdkPaths, deps) {
  const { cc, compileRule } = deps;
  Store.clear();
  const data = _readSnapshotFile(sdkCachePath);
  Store.restore(data);

  const meta = data.metadata;
  const definitions = new Map(Object.entries(meta.types));
  const clauses = new Map(Object.entries(meta.clauses));
  const rawForwardRules = [...meta.forwardRules];
  const sdkCompiledRules = meta.compiledRules
    ? deserRules(meta.compiledRules)
    : rawForwardRules.map(compileRule);
  const queries = new Map(Object.entries(meta.queries));
  const sdkRuleCount = rawForwardRules.length;
  const querySettings = new Map();
  const splitQueries = new Map();
  const moduleDecls = [];

  // Restore SDK argNamesTable from cache, then parse top file on top
  // T2: SDK rules already have sourceLabel from cache (survives JSON round-trip
  // via {...r} spread in _serRules). Only tag new rules from top file.
  const argNamesTable = meta.argNamesTable
    ? new Map(Object.entries(meta.argNamesTable)) : new Map();
  const sortVarsTable = meta.sortVarsTable
    ? new Map(Object.entries(meta.sortVarsTable)) : new Map();
  // Priors (@w) live in the TOP file's parse (SDK bundles carry none) —
  // a fresh table per load, filled by the loadFile below.
  const priorsTable = new Map();
  const prevRuleCount = rawForwardRules.length;
  const prevClauseNames = new Set(clauses.keys());
  convert.loadFile(topFilePath, definitions, clauses, rawForwardRules, queries, {
    alreadyImported: new Set(sdkPaths), argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls,
    priorsTable, loaderConfig: cc.loader
  });
  // T2: Tag top-file rules with root label
  const rootLabel = path.basename(topFilePath, path.extname(topFilePath));
  for (let i = prevRuleCount; i < rawForwardRules.length; i++) {
    rawForwardRules[i].sourceLabel = rootLabel;
  }
  for (const [name, clause] of clauses) {
    if (!prevClauseNames.has(name)) clause.sourceLabel = rootLabel;
  }

  // Compile only new forward rules
  const newRaw = rawForwardRules.slice(sdkRuleCount);
  const newCompiled = newRaw.map(compileRule);
  const allCompiled = [...sdkCompiledRules, ...newCompiled];

  return { definitions, clauses, rawForwardRules, compiledRules: allCompiled,
    queries, argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls, priorsTable };
}

/**
 * Parse from scratch with SDK caching. Parses SDK imports bottom-up,
 * snapshots imports cache, then parses top file.
 * Returns intermediate result (raw data for further caching).
 */
function _parseFresh(topFilePath, sdkNodes, importsCachePath, deps) {
  const { cc, compileRule } = deps;
  Store.clear();
  const definitions = new Map(), clauses = new Map(), rawForwardRules = [], queries = new Map();
  const alreadyImported = new Set();
  const argNamesTable = new Map();
  const sortVarsTable = new Map();
  const querySettings = new Map();
  const splitQueries = new Map();
  const moduleDecls = [];
  const priorsTable = new Map();

  // Phase 1: Parse SDK imports bottom-up (topo order)
  for (const node of sdkNodes) {
    const prevRuleCount = rawForwardRules.length;
    const prevClauseNames = new Set(clauses.keys());
    convert.loadFile(node.path, definitions, clauses, rawForwardRules, queries, {
      alreadyImported, argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls,
      priorsTable, loaderConfig: cc.loader
    });
    alreadyImported.add(node.path);
    // T1: Tag new forward rules with source label
    const label = path.basename(node.path, path.extname(node.path));
    for (let i = prevRuleCount; i < rawForwardRules.length; i++) {
      rawForwardRules[i].sourceLabel = label;
    }
    // Tag new clauses
    for (const [name, clause] of clauses) {
      if (!prevClauseNames.has(name)) clause.sourceLabel = label;
    }
  }

  // Compile SDK rules and write imports cache
  const sdkCompiled = rawForwardRules.map(compileRule);
  const sdkRuleCount = rawForwardRules.length;
  if (importsCachePath && sdkNodes.length > 0) {
    snapToFile(importsCachePath, definitions, clauses,
      [...rawForwardRules], sdkCompiled, new Map(queries), new Map(argNamesTable),
      new Map(sortVarsTable));
  }

  // Phase 2: Parse top file (SDK imports skipped via alreadyImported)
  const prevRuleCount = rawForwardRules.length;
  const prevClauseNames = new Set(clauses.keys());
  convert.loadFile(topFilePath, definitions, clauses, rawForwardRules, queries, {
    alreadyImported, argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls,
    priorsTable, loaderConfig: cc.loader
  });
  // T1: Tag top-file rules with root label
  const rootLabel = path.basename(topFilePath, path.extname(topFilePath));
  for (let i = prevRuleCount; i < rawForwardRules.length; i++) {
    rawForwardRules[i].sourceLabel = rootLabel;
  }
  for (const [name, clause] of clauses) {
    if (!prevClauseNames.has(name)) clause.sourceLabel = rootLabel;
  }

  // Compile only new forward rules
  const newRaw = rawForwardRules.slice(sdkRuleCount);
  const newCompiled = newRaw.map(compileRule);
  const allCompiled = [...sdkCompiled, ...newCompiled];

  return { definitions, clauses, rawForwardRules, compiledRules: allCompiled,
    queries, argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls, priorsTable };
}

/**
 * The two-tier auto-cache orchestration (`cache: true` / `'imports'`).
 * Called by index.js load() AFTER the compose-cache and no-cache
 * branches have been dispatched — filePath is a single path here.
 *
 * @param {string} filePath - absolute or relative single file path
 * @param {boolean|string} cacheMode - true | 'imports' (anything else → loadFresh)
 * @param {Object} opts - the original load opts (cacheDir read here)
 * @param {Object} deps - { cc, compileRule, buildCalc, loadFresh, loadPrecompiled }
 */
function loadTwoTier(filePath, cacheMode, opts, deps) {
  const { cc, buildCalc, loadFresh } = deps;
  const absPath = path.resolve(filePath);
  const cacheDir = opts.cacheDir || path.join(os.tmpdir(), 'calc-cache');

  // Cache keys are epoch-qualified: .bin files parsed/compiled under one
  // calculus config must not be restored under another (TODO_0265 Phase 3).
  const _epochHash = hashString(cc.compile.cacheEpoch || '');
  const tree = convert.buildImportTree(absPath);
  const hashes = convert.computeTreeHashes(tree);
  const topNode = tree[tree.length - 1];
  const fullHash = hashCombine(hashes.get(absPath), CACHE_VERSION, _epochHash);

  // Determine SDK imports (top-level imports + transitive deps)
  const topLevelImports = convert.extractTopLevelImports(topNode.source, absPath);
  const sdkPaths = _sdkPaths(tree, topLevelImports);
  const sdkNodes = tree.filter(n => sdkPaths.has(n.path));

  // Compute imports hash from top-level import file hashes
  let importsHash = null;
  if (topLevelImports.length > 0) {
    const sortedHashes = [...topLevelImports].sort().map(p => hashes.get(p));
    importsHash = hashCombine(...sortedHashes, CACHE_VERSION, _epochHash);
  }

  const fullCachePath = path.join(cacheDir, `${(fullHash >>> 0).toString(16)}.bin`);
  const importsCachePath = importsHash
    ? path.join(cacheDir, `${(importsHash >>> 0).toString(16)}.bin`)
    : null;

  // T6: Compute label infrastructure from tree (shared by all cache-mode branches)
  const rootLabel = path.basename(absPath, path.extname(absPath));
  const ld = labelDeps(tree);

  /** Thread SELL opts from intermediate result to buildCalc */
  function _sellOpts(result) {
    return {
      compiledRules: result.compiledRules,
      argNamesTable: result.argNamesTable,
      sortVarsTable: result.sortVarsTable,
      rootLabel,
      labelDeps: ld,
      querySettings: result.querySettings,
      splitQueries: result.splitQueries,
      moduleDecls: result.moduleDecls,
      priorsTable: result.priorsTable,
      calculusConfig: cc,
    };
  }

  // === cache: true (default) — two-tier auto-cache ===
  if (cacheMode === true) {
    // Tier 1: Try full cache hit
    const fullHit = _tryLoadFromCache(fullCachePath,
      { rootLabel, labelDeps: ld, calculusConfig: cc }, deps);
    if (fullHit) return fullHit;

    // Tier 2: Try imports cache + parse top file
    if (importsCachePath) {
      try {
        if (fs.existsSync(importsCachePath)) {
          const result = _loadCached(absPath, importsCachePath, sdkPaths, deps);
          // Write full cache for next time
          snapToFile(fullCachePath, result.definitions, result.clauses,
            result.rawForwardRules, result.compiledRules, result.queries, result.argNamesTable,
            result.sortVarsTable, result.priorsTable);
          return buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
            _sellOpts(result));
        }
      } catch (e) {
        try { fs.unlinkSync(importsCachePath); } catch {}
      }
    }

    // Full miss: parse everything, cache both tiers
    const result = _parseFresh(absPath, sdkNodes, importsCachePath, deps);
    snapToFile(fullCachePath, result.definitions, result.clauses,
      result.rawForwardRules, result.compiledRules, result.queries, result.argNamesTable,
      result.sortVarsTable, result.priorsTable);
    return buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
      _sellOpts(result));
  }

  // === cache: 'imports' — cache SDK only, always parse top file fresh ===
  if (cacheMode === 'imports') {
    // No imports → degrade to fresh load
    if (!importsCachePath) return loadFresh();

    // Try imports cache hit
    try {
      if (fs.existsSync(importsCachePath)) {
        const result = _loadCached(absPath, importsCachePath, sdkPaths, deps);
        return buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
          _sellOpts(result));
      }
    } catch (e) {
      try { fs.unlinkSync(importsCachePath); } catch {}
    }

    // Miss: parse everything, cache imports only
    const result = _parseFresh(absPath, sdkNodes, importsCachePath, deps);
    return buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
      _sellOpts(result));
  }

  // Unknown cache mode — fallback to fresh
  return loadFresh();
}

export { loadTwoTier, labelDeps, deserRules, snapToFile };
export default { loadTwoTier, labelDeps, deserRules, snapToFile };
