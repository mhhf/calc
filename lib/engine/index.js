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
const { serialize, deserialize, compact } = require('./store-binary');
const { hashCombine } = require('../hash');
const { profile, engine } = require('./optimizer');
const crypto = require('crypto');
const zlib = require('zlib');
const fs = require('fs');
const path = require('path');
const os = require('os');
const _defaultCalcConfig = require('./ill/calculus-config');
const _illCompileOpts = { connectives: _defaultCalcConfig.connectives, getModes: _defaultCalcConfig.compile.getModes };

// ─── Compose disk cache ─────────────────────────────────────────────────────
//
// Persists full post-compose Store snapshot to disk using store-binary format.
// On cache hit, Store.restore() replaces parsing AND compose — cold E2E becomes
// ~40ms (restore + compileRule) instead of ~210ms (parse + compile + compose).
//
// Cache key: SHA-256(canonical string of tree hashes, bytecode hashes, opts, version).
// Snapshot metadata contains definitions, clauses, queries, final rule list,
// and SELL infrastructure so _buildCalc can run with skipCompose: true.

const COMPOSE_DISK_VERSION = 2;

/**
 * Compute compose disk cache key from file tree hashes + bytecode facts.
 * Uses SHA-256 on a canonical string — collision-free for disk cache (C30).
 * Called before parsing to enable early cache check.
 */
function _composeCacheKey(treeHashes, absPath, extraGrade0Facts, fuseBasicBlocks) {
  const parts = [String(treeHashes.get(absPath) | 0)];
  if (extraGrade0Facts) {
    const fParts = [];
    for (const [, facts] of extraGrade0Facts) {
      for (const f of facts) fParts.push(String(f.hash));
    }
    parts.push(fParts.join(','));
  }
  if (fuseBasicBlocks) parts.push('F');
  parts.push('v' + COMPOSE_DISK_VERSION);
  return crypto.createHash('sha256').update(parts.join(';')).digest('hex').slice(0, 16);
}

/**
 * Save full post-compose Store snapshot to disk.
 * Includes all metadata needed to reconstruct the calc context without
 * reparsing or recomposing.
 */
function _saveCSnap(cachePath, calc, definitions, clauses, queries,
    argNamesTable, querySettings, splitQueries, moduleDecls, rootLabel, labelDeps) {
  try {
    const metadata = {
      _composeCache: COMPOSE_DISK_VERSION,
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
      labelDeps: labelDeps
        ? Object.fromEntries([...labelDeps].map(([k, v]) => [k, [...v]])) : {}
    };
    const snap = Store.snapshot(metadata);
    const bin = compact(snap);
    const buf = serialize(bin);
    fs.mkdirSync(path.dirname(cachePath), { recursive: true });
    fs.writeFileSync(cachePath, buf);
  } catch (e) {
    // Non-fatal — fresh parse+compose on next load
  }
}

/**
 * Load post-compose Store snapshot from disk.
 * Returns calc context or null on miss/corruption.
 */
function _loadCSnap(cachePath, sellOpts) {
  try {
    if (!fs.existsSync(cachePath)) return null;
    let buf = fs.readFileSync(cachePath);
    if (buf[0] === 0x1f && buf[1] === 0x8b) buf = zlib.gunzipSync(buf);
    const data = deserialize(buf);
    if (!data.metadata || data.metadata._composeCache !== COMPOSE_DISK_VERSION) return null;
    Store.restore(data);

    const meta = data.metadata;
    const definitions = new Map(Object.entries(meta.types));
    const clauses = new Map(Object.entries(meta.clauses));
    const queries = new Map(Object.entries(meta.queries));
    const argNamesTable = meta.argNamesTable
      ? new Map(Object.entries(meta.argNamesTable)) : new Map();
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

    // Call _buildCalc with skipCompose — compose is already baked into forwardRules
    return _buildCalc(definitions, clauses, forwardRules, queries, {
      argNamesTable, rootLabel, labelDeps, querySettings, splitQueries, moduleDecls,
      skipCompose: true
    });
  } catch (e) {
    // Corrupted — delete and fall through to fresh load
    try { fs.unlinkSync(cachePath); } catch {}
    return null;
  }
}

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
  const cc = opts.calculusConfig || _defaultCalcConfig;
  const connectives = opts.connectives || cc.connectives;
  const { compilePS: _compilePS, execPS: _execPS } = require('./opt/ffi');
  const argNamesTable = opts.argNamesTable || new Map();
  const querySettings = opts.querySettings || new Map();
  const splitQueries = opts.splitQueries || new Map();

  // Initialize calculus-specific atoms + equational theories (idempotent)
  if (cc.init) cc.init();

  // Use cached compiled rules or compile from scratch
  // Derive canonicalize + theoryLookup from calculus config theories
  const { buildTheoryLookup, buildCanonicalizer, defaultTheories: _defaultTh } = require('../kernel/eq-theory');
  const _allTheories = [..._defaultTh, ...(cc.theories || [])];
  const canonicalize = buildCanonicalizer(_allTheories);

  let compiledRules = opts.compiledRules || forwardRules.map(r => forward.compileRule(r, { connectives, getModes: cc.compile.getModes }));

  // Grade-0 cut elimination: compose grade-0 rules before runtime (THY_0015)
  // skipCompose: set by compose disk cache when restoring pre-composed rules
  if (!opts.skipCompose) {
    const hasGrade0Rules = compiledRules.some(r => r.hasGrade0);
    const hasGrade0Clauses = clauses && [...clauses.values()].some(c => c.grade0);
    if (hasGrade0Rules || hasGrade0Clauses || opts.extraGrade0Facts) {
      const { compose0 } = require('./compose');
      const composeOpts = {};
      if (opts.residualResolver) {
        composeOpts.residualResolver = opts.residualResolver;
      } else if (opts.extraGrade0Facts) {
        composeOpts.residualResolver = cc.compose.residualResolver;
      }
      // Compose pipeline config from calculus config
      if (opts.fuseBasicBlocks) composeOpts.fuseBasicBlocks = opts.fuseBasicBlocks;
      if (opts.fusionBarriers) composeOpts.fusionBarriers = opts.fusionBarriers;
      composeOpts.chainFusionPredicates = opts.chainFusionPredicates || cc.compose.chainConfigs;
      composeOpts.linearFusionPredicate = opts.linearFusionPredicate || cc.compose.linearFusionPredicate;
      composeOpts.sroaConfig = opts.sroaConfig || cc.compose.sroaConfig;
      composeOpts.canonicalize = canonicalize;
      composeOpts.backchainOpts = { theories: _allTheories };
      const composeResult = compose0(compiledRules, connectives, cc.compile.getModeMeta, clauses, definitions, opts.extraGrade0Facts || null, opts.scopeGuard || null, composeOpts);
      if (composeResult.diagnostics.errors.length > 0) {
        for (const e of composeResult.diagnostics.errors) {
          if (typeof process !== 'undefined') process.stderr.write(`compose: ${e}\n`);
          else console.error(`compose: ${e}`);
        }
        if (opts.strict) throw new Error(`Grade-0 composition failed: ${composeResult.diagnostics.errors.length} error(s)`);
      }
      if (composeResult.composedRules.length > 0) {
        const _compileOpts = { connectives, getModes: cc.compile.getModes };
        const composedCompiled = composeResult.composedRules.map(
          r => forward.compileRule(r, _compileOpts)
        );
        compiledRules = [...compiledRules, ...composedCompiled];
      }
      if (composeResult.removedNames && composeResult.removedNames.size > 0) {
        compiledRules = compiledRules.filter(r => !composeResult.removedNames.has(r.name));
      }
    }
  }

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

  // Build FFI context from calculus config (injected into compile + runtime)
  const ffiContext = cc.ffi ? {
    meta: cc.ffi.meta,
    parsedModes: cc.ffi.parsedModes,
    get: cc.ffi.get,
    isFFIGround: cc.ffi.isFFIGround,
  } : null;
  const _ffiPM = ffiContext ? ffiContext.parsedModes : null;
  // Validate FFI arity bounds at build time (moved from opt/ffi.js lazy path)
  if (_ffiPM) {
    const { _validateArity } = require('./opt/ffi');
    _validateArity(_ffiPM);
  }

  // Build compiled clause dispatch (Tier 1 base cases + Tier 2 recursive)
  const { clauseDispatch } = require('./opt/compiled-clauses');
  const theoryLookup = buildTheoryLookup(_allTheories);
  const dispatch = clauseDispatch(backchainIndex, _ffiPM);

  // Backward opts from calculus config (threaded to backchain.js)
  const backwardOpts = cc.backward ? {
    normalize: cc.backward.normalize,
    tryFFI: cc.backward.tryFFI,
    getFFIMeta: cc.backward.getFFIMeta,
    buildClauseTerm: cc.backward.buildClauseTerm,
    buildFFITerm: cc.backward.buildFFITerm,
    buildTypeTerm: cc.backward.buildTypeTerm,
    theories: _allTheories,
  } : null;

  // Domain config from calculus config (EVM-specific)
  const domainConfig = cc.domain || null;

  // Capture calc context for backward proving + engine dispatch
  const calcContext = {
    definitions, clauses, backchainIndex, connectives,
    clauseDispatch: dispatch, theoryLookup, canonicalize,
    ffiContext, backwardOpts, domainConfig,
    theories: _allTheories,
  };

  // Generate compiled persistent steps per rule (after calcContext — specs need dispatch table)
  for (const rule of compiledRules) {
    const persistentPats = rule.antecedent.persistent || [];
    if (persistentPats.length === 0) continue;
    const steps = persistentPats.map(p => _compilePS(p, rule.metavarSlots, calcContext, ffiContext));
    if (steps.some(s => s !== null)) rule.persistentSteps = steps;
  }

  // Compile existential chains (direct FFI for ∃-goals, bypasses provePersistent)
  const { compileExChain, execExStep: _execExStep } = require('./opt/existential-compile');
  for (const rule of compiledRules) {
    const chain = compileExChain(rule, ffiContext);
    if (chain) rule._compiledExChain = chain;
  }

  // ── Composition root: resolve ALL layer callbacks ──
  // The orchestrator (this module) is the single point that has visibility
  // into all layers. By pre-resolving these callbacks, forward.js/explore.js
  // receive fully-configured opts and never need cross-layer requires —
  // achieving the LCF kernel property that inner layers are parameterized
  // by, not dependent on, outer layers.
  const { resolveConn: _resolveConn } = require('./formula-utils');
  const _match = require('./match');
  // LNL layer
  const { drainLolis: _drainLolis } = require('./lnl/loli-drain');
  const { matchLoli: _matchLoli } = require('./lnl/loli');
  const { resolveEx: _resolveEx } = require('./lnl/existential');
  const { proveNaive: _proveNaive } = require('./lnl/persistent');
  // opt layer
  const { proveWithFFI: _proveWithFFI } = require('./opt/ffi');
  const { tryCCDispatch: _tryCCDispatch } = require('./opt/compiled-clauses');
  const { predictNext: _predictNext } = require('./opt/prediction');
  const _structuralMemoFns = require('./opt/structural-memo');
  const { fpDetect: _fpDetect, fpLayer: _fpLayer, attachPred: _attachPred } = require('./opt/fingerprint');
  const _rc = _resolveConn(connectives);

  /** Build per-call matchOpts with all layer callbacks injected.
   *  Layer provenance: each protocol factory documents which layer provides which fields.
   */
  function _buildMatchOpts(execOpts) {
    const useFFI = execOpts.dangerouslyUseFFI || false;
    return _match.buildMatchOpts({
      ..._match.buildGenericProtocol({
        optimizePreserved: execOpts.optimizePreserved !== false,
        evidence: execOpts.evidence || false,
        canonicalize,
        onProveFail: execOpts.onProveFail,
        onProveSuccess: execOpts.onProveSuccess,
        // Route the persistent-proving interface: FFI-accelerated vs naive clause prover.
        // Wiring decision belongs at the composition root, not a single-field factory.
        provePersistent: useFFI ? _proveWithFFI : _proveNaive,
      }),
      ..._match.buildLnlProtocol({
        matchLoli: _matchLoli,
        resolveEx: _resolveEx,
        drainLolis: _drainLolis,
        rc: _rc,
        backchainUseFFI: execOpts.useFFI,
      }),
      ..._match.buildOptProtocol({
        execPS: _execPS,
        execExStep: _execExStep,
        tryCCDispatch: _tryCCDispatch,
        useCompiledSteps: useFFI,
      }),
      ..._match.buildFfiProtocol(ffiContext),
    });
  }

  // Create engine with profile-driven function pointers (fingerprint injected)
  const prof = profile(opts.profile);
  const eng = engine(prof, compiledRules, {
    fpDetect: _fpDetect, fpLayer: _fpLayer, attachPred: _attachPred,
  });

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
    modules.set(decl.name, _resolveModule(decl.expr, labelIndex, modules, resolveLabels));
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
    engine: eng,
    labelIndex,
    modules,

    // Backward chaining proof search (merges calculus-level backwardOpts)
    prove: (goal, opts) => backward.prove(goal, clauses, definitions, { ...backwardOpts, ...opts }),

    // Forward chaining execution (auto-injects calc + engine, supports rule filtering) (T15)
    exec: (state, execOpts = {}) => {
      const rules = filterRules(execOpts);
      const matchOpts = execOpts.matchOpts || _buildMatchOpts(execOpts);
      return forward.run(state, rules, { ...execOpts, calc: calcContext, engine: eng, matchOpts });
    },

    // Exhaustive exploration (same filtering as exec) (T16)
    explore: (state, execOpts = {}) => {
      const rules = filterRules(execOpts);
      const matchOpts = execOpts.matchOpts || _buildMatchOpts(execOpts);
      return explore.explore(state, rules, {
        ...execOpts, calc: calcContext, engine: eng, matchOpts,
        predictNext: _predictNext,
        structuralMemoFns: _structuralMemoFns,
      });
    },

    // Exposed for direct callers that need pre-built matchOpts
    _calcContext: calcContext,
    _buildMatchOpts,
  };
}

/**
 * Resolve a module algebra expression to a set of rule names.
 */
function _resolveModule(expr, labelIndex, modules, resolveLabels) {
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
      const l = _resolveModule(expr.left, labelIndex, modules, resolveLabels);
      const r = _resolveModule(expr.right, labelIndex, modules, resolveLabels);
      return new Set([...l, ...r]);
    }
    case 'subtract': {
      const l = _resolveModule(expr.left, labelIndex, modules, resolveLabels);
      const r = _resolveModule(expr.right, labelIndex, modules, resolveLabels);
      return new Set([...l].filter(x => !r.has(x)));
    }
    case 'intersect': {
      const l = _resolveModule(expr.left, labelIndex, modules, resolveLabels);
      const r = _resolveModule(expr.right, labelIndex, modules, resolveLabels);
      return new Set([...l].filter(x => r.has(x)));
    }
    default:
      throw new Error(`Unknown module expression type: ${expr.type}`);
  }
}

/**
 * Deserialize compiled rules from JSON storage.
 * Converts array fields (freevars, persistentDeps) back to Sets.
 */
function _deserRules(rules) {
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
function _snapToFile(cachePath, definitions, clauses, rawForwardRules, _compiledRules, queries, argNamesTable) {
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
function _loadCached(topFilePath, sdkCachePath, sdkPaths) {
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
    ? _deserRules(meta.compiledRules)
    : rawForwardRules.map(r => forward.compileRule(r, _illCompileOpts));
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
function _parseFresh(topFilePath, sdkNodes, importsCachePath) {
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
    _snapToFile(importsCachePath, definitions, clauses,
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
function _loadFresh(filePath, extraOpts) {
  const { definitions, clauses, forwardRules, queries, argNamesTable,
    querySettings, splitQueries, moduleDecls, importTree } = convert.load(filePath);
  const absPath = path.resolve(Array.isArray(filePath) ? filePath[0] : filePath);
  const rootLabel = path.basename(absPath, path.extname(absPath));
  const ld = importTree ? labelDeps(importTree) : new Map();
  return _buildCalc(definitions, clauses, forwardRules, queries, {
    argNamesTable, rootLabel, labelDeps: ld, querySettings, splitQueries, moduleDecls,
    ...extraOpts
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

  // Extract compose opts to pass through to compose0
  const { extraGrade0Facts, scopeGuard, residualResolver,
          chainFusionPredicates, linearFusionPredicate, sroaConfig,
          composeDiskCache, fusionBarriers } = opts;
  // Default fuseBasicBlocks on when external grade-0 facts are provided —
  // compose is always beneficial with concrete fact sets (5x execution speedup).
  const fuseBasicBlocks = opts.fuseBasicBlocks !== undefined
    ? opts.fuseBasicBlocks
    : !!extraGrade0Facts;
  const composeOpts = extraGrade0Facts || scopeGuard || residualResolver || fuseBasicBlocks
      || chainFusionPredicates || linearFusionPredicate || sroaConfig || composeDiskCache || fusionBarriers
    ? { extraGrade0Facts, scopeGuard, residualResolver, fuseBasicBlocks,
        chainFusionPredicates, linearFusionPredicate, sroaConfig,
        composeDiskCache, fusionBarriers } : undefined;

  // ── Compose disk cache: check before parsing (saves parse + compose) ──
  if (composeDiskCache && !Array.isArray(filePath)) {
    const absPathForCache = path.resolve(filePath);
    const tree = convert.buildImportTree(absPathForCache);
    const treeHashes = convert.computeTreeHashes(tree);
    const composeCacheDir = typeof composeDiskCache === 'string'
      ? composeDiskCache
      : path.join(os.tmpdir(), 'calc-cache');
    const composeCacheKey = _composeCacheKey(treeHashes, absPathForCache, extraGrade0Facts, fuseBasicBlocks);
    const composeCachePath = path.join(composeCacheDir, `compose-${composeCacheKey}.bin`);
    const rootLabel = path.basename(absPathForCache, path.extname(absPathForCache));
    const ld = labelDeps(tree);

    const cached = _loadCSnap(composeCachePath, { rootLabel, labelDeps: ld });
    if (cached) return cached;

    // Cache miss — parse + compose, then save snapshot
    const loaded = convert.load(filePath);
    const calc = _buildCalc(loaded.definitions, loaded.clauses, loaded.forwardRules, loaded.queries, {
      argNamesTable: loaded.argNamesTable, rootLabel, labelDeps: ld,
      querySettings: loaded.querySettings, splitQueries: loaded.splitQueries,
      moduleDecls: loaded.moduleDecls, ...composeOpts
    });
    _saveCSnap(composeCachePath, calc,
      calc.definitions, calc.clauses, calc.queries,
      loaded.argNamesTable, loaded.querySettings, loaded.splitQueries,
      loaded.moduleDecls, rootLabel, ld);
    return calc;
  }

  // No caching or array input — use simple path
  if (cacheMode === false || Array.isArray(filePath)) {
    return _loadFresh(filePath, composeOpts);
  }

  const absPath = path.resolve(filePath);
  const cacheDir = opts.cacheDir || path.join(os.tmpdir(), 'calc-cache');

  // Build import tree and compute content hashes
  // CACHE_VERSION: bump when parser/compiler changes affect binary output
  // (e.g., bang arity 1→2 in SELL graded modality).
  const CACHE_VERSION = 5;
  const tree = convert.buildImportTree(absPath);
  const hashes = convert.computeTreeHashes(tree);
  const topNode = tree[tree.length - 1];
  const fullHash = hashCombine(hashes.get(absPath), CACHE_VERSION);

  // Determine SDK imports (top-level imports + transitive deps)
  const topLevelImports = convert.extractTopLevelImports(topNode.source, absPath);
  const sdkPaths = _sdkPaths(tree, topLevelImports);
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
  const ld = labelDeps(tree);

  /** Thread SELL opts from intermediate result to _buildCalc */
  function _sellOpts(result) {
    return {
      compiledRules: result.compiledRules,
      argNamesTable: result.argNamesTable,
      rootLabel,
      labelDeps: ld,
      querySettings: result.querySettings,
      splitQueries: result.splitQueries,
      moduleDecls: result.moduleDecls,
    };
  }

  // === cache: true (default) — two-tier auto-cache ===
  if (cacheMode === true) {
    // Tier 1: Try full cache hit
    const fullHit = _tryLoadFromCache(fullCachePath, { rootLabel, labelDeps: ld });
    if (fullHit) return fullHit;

    // Tier 2: Try imports cache + parse top file
    if (importsCachePath) {
      try {
        if (fs.existsSync(importsCachePath)) {
          const result = _loadCached(absPath, importsCachePath, sdkPaths);
          // Write full cache for next time
          _snapToFile(fullCachePath, result.definitions, result.clauses,
            result.rawForwardRules, result.compiledRules, result.queries, result.argNamesTable);
          return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
            _sellOpts(result));
        }
      } catch (e) {
        try { fs.unlinkSync(importsCachePath); } catch {}
      }
    }

    // Full miss: parse everything, cache both tiers
    const result = _parseFresh(absPath, sdkNodes, importsCachePath);
    _snapToFile(fullCachePath, result.definitions, result.clauses,
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
        const result = _loadCached(absPath, importsCachePath, sdkPaths);
        return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
          _sellOpts(result));
      }
    } catch (e) {
      try { fs.unlinkSync(importsCachePath); } catch {}
    }

    // Miss: parse everything, cache imports only
    const result = _parseFresh(absPath, sdkNodes, importsCachePath);
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
  const byteSize = _snapToFile(cachePath, definitions, clauses, forwardRules, compiledRules, queries, argNamesTable);
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
  if (compiledRules) opts.compiledRules = _deserRules(compiledRules);
  return _buildCalc(definitions, clauses, forwardRules, queries, opts);
}

// Bytecode normalization — delegated to ill/bytecode-normalize.js
const _bcNorm = require('./ill/bytecode-normalize');

function bytesToSemantic(state) { return _bcNorm.bytesToSemantic(state); }

function bytecodeToTrie(state) { return _bcNorm.bytecodeToTrie(state); }
function normalizeQuery(hash) { return _bcNorm.normalizeQuery(hash); }

module.exports = {
  load,
  precompile,
  loadPrecompiled,
  parseExpr: convert.parseExpr,
  hasMonad: convert.hasMonad,
  decomposeQuery: normalizeQuery,
  bytesToSemantic,
  bytecodeToTrie,
  // Backward chaining
  prove: backward.prove,
  // Forward chaining
  exec: forward.run,
  createState: forward.createState,
  compileRule: forward.compileRule,
  Store,
  // Cache key (exported for testing — C30)
  _composeCacheKey,
};
