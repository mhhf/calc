/**
 * MDE Module - Load and work with MDE/Celf files
 *
 * Minimal API following Unix philosophy:
 * - load(filePath) - load MDE file, returns { definitions, clauses, forwardRules }
 * - parseExpr(src) - parse expression string to hash
 * - prove(goal) - backward chaining proof search
 * - exec(state, rules) - run forward chaining
 */

const convert = require('./convert');
const forward = require('./forward');
const explore = require('./explore');
const backward = require('./backchain');
const Store = require('../kernel/store');
const { serialize, deserialize, compactSnapshot } = require('./store-binary');
const { hashCombine } = require('../hash');
const { resolveProfile, createEngine } = require('./optimizer');
const zlib = require('zlib');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { ILL_CONNECTIVES } = require('./ill/connectives');
const { getModes: _illGetModes, getModeMeta: _illGetModeMeta } = require('./opt/ffi');
const _illCompileOpts = { connectives: ILL_CONNECTIVES, getModes: _illGetModes };

// ─── Shared helpers ─────────────────────────────────────────────────────────

/**
 * Build calc context from loaded data (shared by all load paths)
 * @param {Object} [opts]
 * @param {Array} [opts.compiledRules] - pre-compiled rules from cache
 * @param {string} [opts.rootLabel] - label for the root file (D3: always participates)
 * @param {Map} [opts.labelDeps] - label → Set<label> transitive deps
 * @param {Map} [opts.querySettings] - directive settings per query kind
 * @param {Map} [opts.splitQueries] - separated queries (|- or =>) per directive kind
 * @param {Array} [opts.moduleDecls] - @module declarations to resolve
 */
function _buildCalc(definitions, clauses, forwardRules, queries, opts = {}) {
  const connectives = opts.connectives || ILL_CONNECTIVES;
  const { compilePersistentSteps } = require('./opt/ffi');
  const argNamesTable = opts.argNamesTable || new Map();
  const querySettings = opts.querySettings || new Map();
  const splitQueries = opts.splitQueries || new Map();

  // Use cached compiled rules or compile from scratch
  let compiledRules = opts.compiledRules || forwardRules.map(r => forward.compileRule(r, { connectives, getModes: _illGetModes }));

  // Grade-0 cut elimination: compose grade-0 rules before runtime (THY_0015)
  // Two-pass: (1) linear composition via composePair, (2) persistent specialization via grade-0 clauses.
  const hasGrade0Rules = compiledRules.some(r => r.hasGrade0);
  const hasGrade0Clauses = clauses && [...clauses.values()].some(c => c.grade0);
  if (hasGrade0Rules || hasGrade0Clauses) {
    const { composeGrade0 } = require('./compose');
    const composeResult = composeGrade0(compiledRules, connectives, _illGetModeMeta, clauses, definitions);
    if (composeResult.diagnostics.errors.length > 0) {
      for (const e of composeResult.diagnostics.errors) {
        if (typeof process !== 'undefined') process.stderr.write(`compose: ${e}\n`);
        else console.error(`compose: ${e}`);
      }
      if (opts.strict) throw new Error(`Grade-0 composition failed: ${composeResult.diagnostics.errors.length} error(s)`);
    }
    if (composeResult.composedRules.length > 0) {
      const composedCompiled = composeResult.composedRules.map(
        r => forward.compileRule(r, _illCompileOpts)
      );
      compiledRules = [...compiledRules, ...composedCompiled];
    }
    // Remove original rules that were replaced by persistent specialization
    if (composeResult.removedNames && composeResult.removedNames.size > 0) {
      compiledRules = compiledRules.filter(r => !composeResult.removedNames.has(r.name));
    }
  }

  // Generate/regenerate persistent step closures (closures can't be serialized)
  for (const rule of compiledRules) compilePersistentSteps(rule);

  // Sort-check declarations + rules (load-time only, zero runtime cost)
  const { checkAll } = require('./type-check');
  const diagnostics = checkAll(definitions, compiledRules, clauses, opts);
  if (diagnostics.errors.length > 0) {
    for (const e of diagnostics.errors) {
      if (typeof process !== 'undefined') process.stderr.write(`type-check: ${e}\n`);
      else console.error(`type-check: ${e}`);
    }
    if (opts.strict) throw new Error(`Type checking failed: ${diagnostics.errors.length} error(s)`);
  }

  // Build backward prover index once at load time (2x speedup)
  const backchainIndex = backward.buildIndex(clauses, definitions);

  // Capture calc context for backward proving + engine dispatch
  const calcContext = { definitions, clauses, backchainIndex, connectives };

  // Create engine with profile-driven function pointers
  const profile = resolveProfile(opts.profile);
  const engine = createEngine(profile, compiledRules);

  // ── SELL label infrastructure (T7) ──
  const rootLabel = opts.rootLabel || null;
  const labelDeps = opts.labelDeps || new Map();

  // Build label index: label → [ruleName, ...]
  const labelIndex = new Map();
  for (const r of compiledRules) {
    const label = r.sourceLabel || 'unknown';
    if (!labelIndex.has(label)) labelIndex.set(label, []);
    labelIndex.get(label).push(r.name);
  }

  // resolveLabels(['evm']) → Set{'evm', 'bin', 'bool', ...} (+ transitive deps)
  function resolveLabels(requestedLabels) {
    const resolved = new Set();
    for (const label of requestedLabels) {
      resolved.add(label);
      for (const dep of labelDeps.get(label) || []) resolved.add(dep);
    }
    return resolved;
  }

  // ── Tier 2: Module resolution (T13) ──
  const moduleDecls = opts.moduleDecls || [];
  const modules = new Map(); // name → Set<ruleName>
  for (const decl of moduleDecls) {
    modules.set(decl.name, _resolveModuleExpr(decl.expr, labelIndex, modules, resolveLabels));
  }

  // ── Shared rule filtering — Tier 1 (label list) + Tier 2 (module name) + grade-0 exclusion ──
  function filterRules(execOpts) {
    let rules = compiledRules;

    // Grade-0 exclusion: rules with grade-0 antecedent/consequent patterns are
    // compile-time only (SELL/QTT convention). Grade-0 non-interference guarantees
    // these have no runtime effect (Choudhury et al. POPL 2021, Lemma 6.2).
    // See THY_0015 for stratified cut elimination by grade.
    rules = rules.filter(r => !r.hasGrade0);

    if (!execOpts.rules) return rules;

    if (Array.isArray(execOpts.rules)) {
      // Tier 1: list of labels → resolve transitive deps → filter by sourceLabel
      const allowedLabels = resolveLabels(execOpts.rules);
      // Validate labels
      for (const label of execOpts.rules) {
        if (!labelIndex.has(label) && !labelDeps.has(label)) {
          const known = [...labelIndex.keys()].join(', ');
          throw new Error(`Unknown rule label: '${label}'. Known labels: ${known}`);
        }
      }
      if (rootLabel) allowedLabels.add(rootLabel); // D3: root always participates
      return rules.filter(r => allowedLabels.has(r.sourceLabel));
    }

    if (typeof execOpts.rules === 'string') {
      // D7: check modules first, fall back to label
      const moduleNames = modules.get(execOpts.rules);
      if (moduleNames) {
        // Tier 2: module name → resolved set of rule names
        const allowedNames = new Set(moduleNames); // copy — don't mutate canonical set
        // D3: root file rules always participate
        if (rootLabel) {
          for (const n of (labelIndex.get(rootLabel) || [])) allowedNames.add(n);
        }
        return rules.filter(r => allowedNames.has(r.name));
      }
      // Fallback: treat as single label (Tier 1)
      if (!labelIndex.has(execOpts.rules) && !labelDeps.has(execOpts.rules)) {
        const known = [...labelIndex.keys(), ...modules.keys()].join(', ');
        throw new Error(`Unknown rule label or module: '${execOpts.rules}'. Known: ${known}`);
      }
      const allowedLabels = resolveLabels([execOpts.rules]);
      if (rootLabel) allowedLabels.add(rootLabel);
      return rules.filter(r => allowedLabels.has(r.sourceLabel));
    }

    return rules;
  }

  return {
    definitions,
    clauses,
    queries,
    querySettings,
    splitQueries,
    forwardRules: compiledRules.filter(r => !r.hasGrade0),
    _compiledRules: compiledRules,
    argNamesTable,
    engine,
    labelIndex,
    modules,

    // Backward chaining proof search
    prove: (goal, opts) => backward.prove(goal, clauses, definitions, opts),

    // Forward chaining execution (auto-injects calc + engine, supports rule filtering) (T15)
    exec: (state, execOpts = {}) => {
      const rules = filterRules(execOpts);
      return forward.run(state, rules, { ...execOpts, calc: calcContext, engine });
    },

    // Exhaustive exploration (same filtering as exec) (T16)
    explore: (state, execOpts = {}) => {
      const rules = filterRules(execOpts);
      return explore.explore(state, rules, { ...execOpts, calc: calcContext, engine });
    }
  };
}

/**
 * Resolve a module algebra expression to a set of rule names.
 */
function _resolveModuleExpr(expr, labelIndex, modules, resolveLabels) {
  switch (expr.type) {
    case 'label': {
      // D7: modules shadow labels — check modules first
      if (modules.has(expr.name)) {
        return new Set(modules.get(expr.name));
      }
      // Otherwise treat as import label → all rule names + transitive deps
      const labels = resolveLabels([expr.name]);
      const names = new Set();
      for (const l of labels)
        for (const n of (labelIndex.get(l) || [])) names.add(n);
      return names;
    }
    case 'names': return new Set(expr.names);
    case 'union': {
      const l = _resolveModuleExpr(expr.left, labelIndex, modules, resolveLabels);
      const r = _resolveModuleExpr(expr.right, labelIndex, modules, resolveLabels);
      return new Set([...l, ...r]);
    }
    case 'subtract': {
      const l = _resolveModuleExpr(expr.left, labelIndex, modules, resolveLabels);
      const r = _resolveModuleExpr(expr.right, labelIndex, modules, resolveLabels);
      return new Set([...l].filter(x => !r.has(x)));
    }
    case 'intersect': {
      const l = _resolveModuleExpr(expr.left, labelIndex, modules, resolveLabels);
      const r = _resolveModuleExpr(expr.right, labelIndex, modules, resolveLabels);
      return new Set([...l].filter(x => r.has(x)));
    }
    default:
      throw new Error(`Unknown module expression type: ${expr.type}`);
  }
}

/**
 * Serialize compiled rules for JSON storage.
 * Converts Set fields (freevars, persistentDeps) to arrays.
 */
function _serializeCompiledRules(rules) {
  return rules.map(r => {
    if (!r.linearMeta) return r;
    const lm = {};
    for (const k in r.linearMeta) {
      const m = r.linearMeta[k];
      lm[k] = {
        ...m,
        freevars: m.freevars instanceof Set ? [...m.freevars] : m.freevars,
        persistentDeps: m.persistentDeps instanceof Set ? [...m.persistentDeps] : m.persistentDeps,
      };
    }
    return { ...r, linearMeta: lm };
  });
}

/**
 * Deserialize compiled rules from JSON storage.
 * Converts array fields (freevars, persistentDeps) back to Sets.
 */
function _deserializeCompiledRules(rules) {
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
function _snapshotToFile(cachePath, definitions, clauses, rawForwardRules, compiledRules, queries, argNamesTable) {
  const metadata = {
    types: Object.fromEntries(definitions),
    clauses: Object.fromEntries(
      Array.from(clauses.entries()).map(([k, v]) => [k, v])
    ),
    forwardRules: rawForwardRules,
    // compiledRules omitted — recomputed on restore (~1.5ms, saves ~85KB)
    queries: Object.fromEntries(queries),
    argNamesTable: argNamesTable ? Object.fromEntries(argNamesTable) : {}
  };
  const snap = Store.snapshot(metadata);
  const compact = compactSnapshot(snap);
  const buf = serialize(compact);
  // No gzip — compacted binary is small enough (~50KB) and gunzip costs 0.3ms
  fs.mkdirSync(path.dirname(cachePath), { recursive: true });
  fs.writeFileSync(cachePath, buf);
  return buf.length;
}

/**
 * Compute transitive closure of SDK paths from top-level imports.
 */
function _computeSdkPaths(tree, topLevelImports) {
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
function buildLabelDeps(tree) {
  const labelDeps = new Map();
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
    labelDeps.set(label, all);
  }
  return labelDeps;
}

// ─── Cache-aware load helpers ───────────────────────────────────────────────

/**
 * Try loading from a binary cache file. Returns calc context or null.
 * Deletes corrupted cache files gracefully.
 * @param {Object} [sellOpts] - SELL label opts to thread to _buildCalc
 */
function _tryLoadFromCache(cachePath, sellOpts) {
  try {
    if (fs.existsSync(cachePath)) return loadPrecompiled(cachePath, sellOpts);
  } catch (e) {
    try { fs.unlinkSync(cachePath); } catch {}
  }
  return null;
}

/**
 * Restore SDK from binary cache, parse top file on top.
 * Returns intermediate result (raw data for further caching).
 */
function _loadWithCachedImports(topFilePath, sdkCachePath, sdkPaths) {
  Store.clear();
  let buf = fs.readFileSync(sdkCachePath);
  if (buf[0] === 0x1f && buf[1] === 0x8b) buf = zlib.gunzipSync(buf);
  const data = deserialize(buf);
  Store.restore(data);

  const meta = data.metadata;
  const definitions = new Map(Object.entries(meta.types));
  const clauses = new Map(Object.entries(meta.clauses));
  const rawForwardRules = [...meta.forwardRules];
  const sdkCompiledRules = meta.compiledRules
    ? _deserializeCompiledRules(meta.compiledRules)
    : rawForwardRules.map(r => forward.compileRule(r, _illCompileOpts));
  const queries = new Map(Object.entries(meta.queries));
  const sdkRuleCount = rawForwardRules.length;
  const querySettings = new Map();
  const splitQueries = new Map();
  const moduleDecls = [];

  // Restore SDK argNamesTable from cache, then parse top file on top
  // T2: SDK rules already have sourceLabel from cache (survives JSON round-trip
  // via {...r} spread in _serializeCompiledRules). Only tag new rules from top file.
  const argNamesTable = meta.argNamesTable
    ? new Map(Object.entries(meta.argNamesTable)) : new Map();
  const prevRuleCount = rawForwardRules.length;
  const prevClauseNames = new Set(clauses.keys());
  convert.loadFile(topFilePath, definitions, clauses, rawForwardRules, queries, {
    alreadyImported: new Set(sdkPaths), argNamesTable, querySettings, splitQueries, moduleDecls
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
  const newCompiled = newRaw.map(r => forward.compileRule(r, _illCompileOpts));
  const allCompiled = [...sdkCompiledRules, ...newCompiled];

  return { definitions, clauses, rawForwardRules, compiledRules: allCompiled,
    queries, argNamesTable, querySettings, splitQueries, moduleDecls };
}

/**
 * Parse from scratch with SDK caching. Parses SDK imports bottom-up,
 * snapshots imports cache, then parses top file.
 * Returns intermediate result (raw data for further caching).
 */
function _parseFreshWithSdk(topFilePath, sdkNodes, sdkPaths, importsCachePath) {
  Store.clear();
  const definitions = new Map(), clauses = new Map(), rawForwardRules = [], queries = new Map();
  const alreadyImported = new Set();
  const argNamesTable = new Map();
  const querySettings = new Map();
  const splitQueries = new Map();
  const moduleDecls = [];

  // Phase 1: Parse SDK imports bottom-up (topo order)
  for (const node of sdkNodes) {
    const prevRuleCount = rawForwardRules.length;
    const prevClauseNames = new Set(clauses.keys());
    convert.loadFile(node.path, definitions, clauses, rawForwardRules, queries, {
      alreadyImported, argNamesTable, querySettings, splitQueries, moduleDecls
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
  const sdkCompiled = rawForwardRules.map(r => forward.compileRule(r, _illCompileOpts));
  const sdkRuleCount = rawForwardRules.length;
  if (importsCachePath && sdkNodes.length > 0) {
    _snapshotToFile(importsCachePath, definitions, clauses,
      [...rawForwardRules], sdkCompiled, new Map(queries), new Map(argNamesTable));
  }

  // Phase 2: Parse top file (SDK imports skipped via alreadyImported)
  const prevRuleCount = rawForwardRules.length;
  const prevClauseNames = new Set(clauses.keys());
  convert.loadFile(topFilePath, definitions, clauses, rawForwardRules, queries, {
    alreadyImported, argNamesTable, querySettings, splitQueries, moduleDecls
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
  const newCompiled = newRaw.map(r => forward.compileRule(r, _illCompileOpts));
  const allCompiled = [...sdkCompiled, ...newCompiled];

  return { definitions, clauses, rawForwardRules, compiledRules: allCompiled,
    queries, argNamesTable, querySettings, splitQueries, moduleDecls };
}

/**
 * Load without caching (old behavior).
 */
function _loadFresh(filePath) {
  const { definitions, clauses, forwardRules, queries, argNamesTable,
    querySettings, splitQueries, moduleDecls, importTree } = convert.load(filePath);
  const absPath = path.resolve(Array.isArray(filePath) ? filePath[0] : filePath);
  const rootLabel = path.basename(absPath, path.extname(absPath));
  const labelDeps = importTree ? buildLabelDeps(importTree) : new Map();
  return _buildCalc(definitions, clauses, forwardRules, queries, {
    argNamesTable, rootLabel, labelDeps, querySettings, splitQueries, moduleDecls
  });
}

// ─── Public API ─────────────────────────────────────────────────────────────

/**
 * Load MDE file and prepare for execution.
 *
 * Auto-caching (default): computes content hashes of source files, uses
 * two-tier cache (full program + imports-only) in a temp directory.
 *
 * @param {string|string[]} filePath - file path(s) to load
 * @param {Object} [opts]
 * @param {boolean|string} [opts.cache=true] - true (auto-cache), 'imports' (cache SDK only), false (no cache)
 * @param {string} [opts.cacheDir] - cache directory (default: os.tmpdir()/calc-cache/)
 * @returns {Object} calc context
 */
function load(filePath, opts = {}) {
  const cacheMode = opts.cache === undefined ? true : opts.cache;

  // No caching or array input — use simple path
  if (cacheMode === false || Array.isArray(filePath)) {
    return _loadFresh(filePath);
  }

  const absPath = path.resolve(filePath);
  const cacheDir = opts.cacheDir || path.join(os.tmpdir(), 'calc-cache');

  // Build import tree and compute content hashes
  // CACHE_VERSION: bump when parser/compiler changes affect binary output
  // (e.g., bang arity 1→2 in SELL graded modality).
  const CACHE_VERSION = 3;
  const tree = convert.buildImportTree(absPath);
  const hashes = convert.computeTreeHashes(tree);
  const topNode = tree[tree.length - 1];
  const fullHash = hashCombine(hashes.get(absPath), CACHE_VERSION);

  // Determine SDK imports (top-level imports + transitive deps)
  const topLevelImports = convert.extractTopLevelImports(topNode.source, absPath);
  const sdkPaths = _computeSdkPaths(tree, topLevelImports);
  const sdkNodes = tree.filter(n => sdkPaths.has(n.path));

  // Compute imports hash from top-level import file hashes
  let importsHash = null;
  if (topLevelImports.length > 0) {
    const sortedHashes = [...topLevelImports].sort().map(p => hashes.get(p));
    importsHash = hashCombine(...sortedHashes, CACHE_VERSION);
  }

  const fullCachePath = path.join(cacheDir, `${(fullHash >>> 0).toString(16)}.bin`);
  const importsCachePath = importsHash
    ? path.join(cacheDir, `${(importsHash >>> 0).toString(16)}.bin`)
    : null;

  // T6: Compute label infrastructure from tree (shared by all cache-mode branches)
  const rootLabel = path.basename(absPath, path.extname(absPath));
  const labelDeps = buildLabelDeps(tree);

  /** Thread SELL opts from intermediate result to _buildCalc */
  function _sellOpts(result) {
    return {
      compiledRules: result.compiledRules,
      argNamesTable: result.argNamesTable,
      rootLabel,
      labelDeps,
      querySettings: result.querySettings,
      splitQueries: result.splitQueries,
      moduleDecls: result.moduleDecls,
    };
  }

  // === cache: true (default) — two-tier auto-cache ===
  if (cacheMode === true) {
    // Tier 1: Try full cache hit
    const fullHit = _tryLoadFromCache(fullCachePath, { rootLabel, labelDeps });
    if (fullHit) return fullHit;

    // Tier 2: Try imports cache + parse top file
    if (importsCachePath) {
      try {
        if (fs.existsSync(importsCachePath)) {
          const result = _loadWithCachedImports(absPath, importsCachePath, sdkPaths);
          // Write full cache for next time
          _snapshotToFile(fullCachePath, result.definitions, result.clauses,
            result.rawForwardRules, result.compiledRules, result.queries, result.argNamesTable);
          return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
            _sellOpts(result));
        }
      } catch (e) {
        try { fs.unlinkSync(importsCachePath); } catch {}
      }
    }

    // Full miss: parse everything, cache both tiers
    const result = _parseFreshWithSdk(absPath, sdkNodes, sdkPaths, importsCachePath);
    _snapshotToFile(fullCachePath, result.definitions, result.clauses,
      result.rawForwardRules, result.compiledRules, result.queries, result.argNamesTable);
    return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
      _sellOpts(result));
  }

  // === cache: 'imports' — cache SDK only, always parse top file fresh ===
  if (cacheMode === 'imports') {
    // No imports → degrade to fresh load
    if (!importsCachePath) return _loadFresh(filePath);

    // Try imports cache hit
    try {
      if (fs.existsSync(importsCachePath)) {
        const result = _loadWithCachedImports(absPath, importsCachePath, sdkPaths);
        return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
          _sellOpts(result));
      }
    } catch (e) {
      try { fs.unlinkSync(importsCachePath); } catch {}
    }

    // Miss: parse everything, cache imports only
    const result = _parseFreshWithSdk(absPath, sdkNodes, sdkPaths, importsCachePath);
    return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
      _sellOpts(result));
  }

  // Unknown cache mode — fallback to fresh
  return _loadFresh(filePath);
}

/**
 * Precompile MDE files to binary cache.
 * Includes compiled forward rules for fast restore.
 * @param {string|string[]} filePaths - source files to precompile
 * @param {string} cachePath - output binary file path
 * @returns {{ definitions, clauses, forwardRules, queries, byteSize }}
 */
function precompile(filePaths, cachePath) {
  Store.clear();
  const { definitions, clauses, forwardRules, queries, argNamesTable } = convert.load(filePaths);
  const compiledRules = forwardRules.map(r => forward.compileRule(r, _illCompileOpts));
  const byteSize = _snapshotToFile(cachePath, definitions, clauses, forwardRules, compiledRules, queries, argNamesTable);
  return { definitions, clauses, forwardRules, queries, argNamesTable, byteSize };
}

/**
 * Load from precompiled binary cache.
 * Restores Store state and uses cached compiled rules.
 * @param {string} cachePath - binary cache file path
 * @param {Object} [sellOpts] - SELL label opts (rootLabel, labelDeps) to thread
 * @returns {Object} calc context (same shape as load())
 */
function loadPrecompiled(cachePath, sellOpts) {
  let buf = fs.readFileSync(cachePath);
  // Detect gzip (magic bytes 0x1f 0x8b)
  if (buf[0] === 0x1f && buf[1] === 0x8b) buf = zlib.gunzipSync(buf);
  const data = deserialize(buf);
  Store.restore(data);

  const { types: defsObj, clauses: clausesObj, forwardRules, compiledRules, queries: queriesObj } = data.metadata;

  const definitions = new Map(Object.entries(defsObj));
  const clauses = new Map(Object.entries(clausesObj));
  const queries = new Map(Object.entries(queriesObj));
  const argNamesTable = data.metadata.argNamesTable
    ? new Map(Object.entries(data.metadata.argNamesTable)) : new Map();

  const opts = { argNamesTable, ...(sellOpts || {}) };
  // Use cached compiledRules if present, otherwise recompile from forwardRules
  if (compiledRules) opts.compiledRules = _deserializeCompiledRules(compiledRules);
  return _buildCalc(definitions, clauses, forwardRules, queries, opts);
}

/**
 * Convert `code PC V` linear facts into a single `bytecode` arrlit fact.
 * Operates on plain state objects { linear: {hash:count}, persistent: {hash:true} }.
 * Returns a new state with code facts replaced by a bytecode fact.
 * No-op if no code facts found or bytecode fact already exists.
 */
function codeToArrlit(state) {
  const { binToInt } = require('./ill/ffi/convert');
  const codeTagId = Store.TAG['code'];
  const bcTagId = Store.TAG['bytecode'];
  if (codeTagId === undefined) return state;

  // Check if bytecode already exists
  if (bcTagId !== undefined) {
    for (const h of Object.keys(state.linear)) {
      if (Store.tagId(Number(h)) === bcTagId) return state;
    }
  }

  // Collect code facts: { pc: int, val: hash, factHash: number }
  const codeFacts = [];
  for (const hStr of Object.keys(state.linear)) {
    const h = Number(hStr);
    if (Store.tagId(h) === codeTagId && state.linear[hStr] > 0) {
      const pcHash = Store.child(h, 0);
      const valHash = Store.child(h, 1);
      const pcInt = binToInt(pcHash);
      if (pcInt !== null) {
        codeFacts.push({ pc: Number(pcInt), val: valHash, hash: h });
      }
    }
  }

  if (codeFacts.length === 0) return state;

  // Build sparse arrlit: fill gaps with 0 (intToBin(0))
  const maxPC = Math.max(...codeFacts.map(f => f.pc));
  const elements = new Uint32Array(maxPC + 1);
  for (const f of codeFacts) {
    elements[f.pc] = f.val;
  }

  const arrHash = Store.putArray(elements);
  const bytecodeHash = Store.put('bytecode', [arrHash]);

  // Build new linear state: remove code facts, add bytecode
  const newLinear = {};
  for (const [hStr, count] of Object.entries(state.linear)) {
    if (Store.tagId(Number(hStr)) !== codeTagId) {
      newLinear[hStr] = count;
    }
  }
  newLinear[bytecodeHash] = 1;

  return { linear: newLinear, persistent: state.persistent };
}

/**
 * Convert byte-by-byte bytecode arrlit → semantic arrlit.
 * Walks the byte array identifying PUSH opcodes (0x60-0x7f) and combining
 * their N data bytes (N = opcode - 0x5f) into single big-endian values.
 *
 * Guard: all elements must be ground binlit with value <= 0xFF.
 * Returns new state with semantic bytecode, or original if already semantic.
 */
function bytesToSemantic(state) {
  const { binToInt, intToBin } = require('./ill/ffi/convert');
  const bcTagId = Store.TAG['bytecode'];
  if (bcTagId === undefined) return state;

  // Find bytecode fact
  let bcFactHash = null;
  for (const hStr of Object.keys(state.linear)) {
    const h = Number(hStr);
    if (Store.tagId(h) === bcTagId) { bcFactHash = h; break; }
  }
  if (bcFactHash === null) return state;

  const arrHash = Store.child(bcFactHash, 0);
  const elems = Store.getArrayElements(arrHash);
  if (!elems || elems.length === 0) return state;

  // Guard: check all elements are ground binlit with value <= 0xFF
  let isByteLevel = true;
  for (let i = 0; i < elems.length; i++) {
    const t = Store.tag(elems[i]);
    if (t !== 'binlit') { isByteLevel = false; break; }
    const v = Store.child(elems[i], 0);
    if (typeof v !== 'bigint' || v > 0xFFn) { isByteLevel = false; break; }
  }
  if (!isByteLevel) return state; // already semantic or mixed

  // Pre-scan to find required array length (PUSH data may extend beyond bytecode)
  let requiredLen = elems.length;
  {
    let scanPc = 0;
    while (scanPc < elems.length) {
      const opVal = Number(Store.child(elems[scanPc], 0));
      if (opVal >= 0x60 && opVal <= 0x7f) {
        const n = opVal - 0x5f;
        // Need opcode + 1 data slot + implicit STOP if PUSH lands beyond bytecode
        const nextPc = scanPc + 1 + n;
        const needed = nextPc >= elems.length ? nextPc + 1 : scanPc + 2;
        if (needed > requiredLen) requiredLen = needed;
        scanPc = nextPc;
      } else {
        scanPc++;
      }
    }
  }

  // Walk bytes, group PUSHn data
  const semantic = new Uint32Array(requiredLen);
  const zeroBinlit = intToBin(0n);
  let pc = 0;
  while (pc < elems.length) {
    const opVal = Number(Store.child(elems[pc], 0));
    semantic[pc] = elems[pc]; // opcode itself
    if (opVal >= 0x60 && opVal <= 0x7f) {
      const n = opVal - 0x5f;
      // Combine next n bytes into a single big-endian value
      // EVM spec: bytes beyond bytecode length are treated as 0x00
      let combined = 0n;
      const available = Math.min(n, elems.length - (pc + 1));
      for (let j = 0; j < available; j++) {
        combined = (combined << 8n) | Store.child(elems[pc + 1 + j], 0);
      }
      combined <<= BigInt((n - available) * 8); // pad missing bytes with 0
      semantic[pc + 1] = intToBin(combined);
      // Fill remaining in-bounds positions with 0
      for (let j = 2; j <= n && pc + j < elems.length; j++) {
        semantic[pc + j] = zeroBinlit;
      }
      pc += 1 + n;
    } else {
      pc++;
    }
  }
  // EVM spec: bytes beyond bytecode are 0x00 (STOP opcode)
  for (let i = elems.length; i < requiredLen; i++) {
    if (semantic[i] === 0) semantic[i] = zeroBinlit;
  }

  const newArrHash = Store.putArray(semantic);
  const newBcHash = Store.put('bytecode', [newArrHash]);

  const newLinear = {};
  for (const [hStr, count] of Object.entries(state.linear)) {
    if (Number(hStr) === bcFactHash) {
      newLinear[newBcHash] = count;
    } else {
      newLinear[hStr] = count;
    }
  }

  return { linear: newLinear, persistent: state.persistent };
}

/**
 * Normalize bytecode state: convert old code facts → arrlit, then byte→semantic.
 * Wraps decomposeQuery for backward compatibility.
 */
function normalizeQuery(hash) {
  let state = convert.decomposeQuery(hash);
  state = codeToArrlit(state);
  state = bytesToSemantic(state);
  return state;
}

module.exports = {
  load,
  precompile,
  loadPrecompiled,
  parseExpr: convert.parseExpr,
  hasMonad: convert.hasMonad,
  decomposeQuery: normalizeQuery,
  codeToArrlit,
  bytesToSemantic,
  // Backward chaining
  prove: backward.prove,
  // Forward chaining
  exec: forward.run,
  createState: forward.createState,
  compileRule: forward.compileRule,
  Store
};
