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
const backward = require('./backchain');
const Store = require('../kernel/store');
const { serialize, deserialize } = require('./store-binary');
const { hashCombine } = require('../hash');
const { resolveProfile, createEngine } = require('./optimizer');
const fs = require('fs');
const path = require('path');
const os = require('os');

// ─── Shared helpers ─────────────────────────────────────────────────────────

/**
 * Build calc context from loaded data (shared by all load paths)
 * @param {Object} [opts]
 * @param {Array} [opts.compiledRules] - pre-compiled rules from cache
 */
function _buildCalc(definitions, clauses, forwardRules, queries, opts = {}) {
  const { DEFAULT_ROLES } = require('./compile');
  const roles = opts.roles ? { ...DEFAULT_ROLES, ...opts.roles } : DEFAULT_ROLES;

  // Use cached compiled rules or compile from scratch
  const compiledRules = opts.compiledRules || forwardRules.map(r => forward.compileRule(r));

  // Regenerate persistent step closures (closures can't be serialized)
  const { compilePersistentSteps } = require('./compile');
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

  // Capture calc context for backward proving
  const calcContext = { definitions, clauses, backchainIndex, roles };

  // Create engine with profile-driven function pointers
  const profile = resolveProfile(opts.profile);
  const engine = createEngine(profile, compiledRules);

  return {
    definitions,
    clauses,
    queries,
    forwardRules: compiledRules,
    engine,

    // Backward chaining proof search
    prove: (goal, opts) => backward.prove(goal, clauses, definitions, opts),

    // Forward chaining execution (auto-injects calc + engine for backward proving)
    exec: (state, opts = {}) => forward.run(state, compiledRules, { ...opts, calc: calcContext, engine })
  };
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
function _snapshotToFile(cachePath, definitions, clauses, rawForwardRules, compiledRules, queries) {
  const metadata = {
    types: Object.fromEntries(definitions),
    clauses: Object.fromEntries(
      Array.from(clauses.entries()).map(([k, v]) => [k, v])
    ),
    forwardRules: rawForwardRules,
    compiledRules: _serializeCompiledRules(compiledRules),
    queries: Object.fromEntries(queries)
  };
  const snap = Store.snapshot(metadata);
  const buf = serialize(snap);
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

// ─── Cache-aware load helpers ───────────────────────────────────────────────

/**
 * Try loading from a binary cache file. Returns calc context or null.
 * Deletes corrupted cache files gracefully.
 */
function _tryLoadFromCache(cachePath) {
  try {
    if (fs.existsSync(cachePath)) return loadPrecompiled(cachePath);
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
  const buf = fs.readFileSync(sdkCachePath);
  const data = deserialize(buf);
  Store.restore(data);

  const meta = data.metadata;
  const definitions = new Map(Object.entries(meta.types));
  const clauses = new Map(Object.entries(meta.clauses));
  const rawForwardRules = [...meta.forwardRules];
  const sdkCompiledRules = _deserializeCompiledRules(meta.compiledRules);
  const queries = new Map(Object.entries(meta.queries));
  const sdkRuleCount = rawForwardRules.length;

  // Parse top file with SDK paths pre-imported
  convert.loadFile(topFilePath, definitions, clauses, rawForwardRules, queries, {
    alreadyImported: new Set(sdkPaths)
  });

  // Compile only new forward rules
  const newRaw = rawForwardRules.slice(sdkRuleCount);
  const newCompiled = newRaw.map(r => forward.compileRule(r));
  const allCompiled = [...sdkCompiledRules, ...newCompiled];

  return { definitions, clauses, rawForwardRules, compiledRules: allCompiled, queries };
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

  // Phase 1: Parse SDK imports bottom-up (topo order)
  for (const node of sdkNodes) {
    convert.loadFile(node.path, definitions, clauses, rawForwardRules, queries, {
      alreadyImported
    });
    alreadyImported.add(node.path);
  }

  // Compile SDK rules and write imports cache
  const sdkCompiled = rawForwardRules.map(r => forward.compileRule(r));
  const sdkRuleCount = rawForwardRules.length;
  if (importsCachePath && sdkNodes.length > 0) {
    _snapshotToFile(importsCachePath, definitions, clauses,
      [...rawForwardRules], sdkCompiled, new Map(queries));
  }

  // Phase 2: Parse top file (SDK imports skipped via alreadyImported)
  convert.loadFile(topFilePath, definitions, clauses, rawForwardRules, queries, {
    alreadyImported
  });

  // Compile only new forward rules
  const newRaw = rawForwardRules.slice(sdkRuleCount);
  const newCompiled = newRaw.map(r => forward.compileRule(r));
  const allCompiled = [...sdkCompiled, ...newCompiled];

  return { definitions, clauses, rawForwardRules, compiledRules: allCompiled, queries };
}

/**
 * Load without caching (old behavior).
 */
function _loadFresh(filePath) {
  const { definitions, clauses, forwardRules, queries } = convert.load(filePath);
  return _buildCalc(definitions, clauses, forwardRules, queries);
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
  const tree = convert.buildImportTree(absPath);
  const hashes = convert.computeTreeHashes(tree);
  const topNode = tree[tree.length - 1];
  const fullHash = hashes.get(absPath);

  // Determine SDK imports (top-level imports + transitive deps)
  const topLevelImports = convert.extractTopLevelImports(topNode.source, absPath);
  const sdkPaths = _computeSdkPaths(tree, topLevelImports);
  const sdkNodes = tree.filter(n => sdkPaths.has(n.path));

  // Compute imports hash from top-level import file hashes
  let importsHash = null;
  if (topLevelImports.length > 0) {
    const sortedHashes = [...topLevelImports].sort().map(p => hashes.get(p));
    importsHash = hashCombine(...sortedHashes);
  }

  const fullCachePath = path.join(cacheDir, `${(fullHash >>> 0).toString(16)}.bin`);
  const importsCachePath = importsHash
    ? path.join(cacheDir, `${(importsHash >>> 0).toString(16)}.bin`)
    : null;

  // === cache: true (default) — two-tier auto-cache ===
  if (cacheMode === true) {
    // Tier 1: Try full cache hit
    const fullHit = _tryLoadFromCache(fullCachePath);
    if (fullHit) return fullHit;

    // Tier 2: Try imports cache + parse top file
    if (importsCachePath) {
      try {
        if (fs.existsSync(importsCachePath)) {
          const result = _loadWithCachedImports(absPath, importsCachePath, sdkPaths);
          // Write full cache for next time
          _snapshotToFile(fullCachePath, result.definitions, result.clauses,
            result.rawForwardRules, result.compiledRules, result.queries);
          return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries, {
            compiledRules: result.compiledRules
          });
        }
      } catch (e) {
        try { fs.unlinkSync(importsCachePath); } catch {}
      }
    }

    // Full miss: parse everything, cache both tiers
    const result = _parseFreshWithSdk(absPath, sdkNodes, sdkPaths, importsCachePath);
    _snapshotToFile(fullCachePath, result.definitions, result.clauses,
      result.rawForwardRules, result.compiledRules, result.queries);
    return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries, {
      compiledRules: result.compiledRules
    });
  }

  // === cache: 'imports' — cache SDK only, always parse top file fresh ===
  if (cacheMode === 'imports') {
    // No imports → degrade to fresh load
    if (!importsCachePath) return _loadFresh(filePath);

    // Try imports cache hit
    try {
      if (fs.existsSync(importsCachePath)) {
        const result = _loadWithCachedImports(absPath, importsCachePath, sdkPaths);
        return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries, {
          compiledRules: result.compiledRules
        });
      }
    } catch (e) {
      try { fs.unlinkSync(importsCachePath); } catch {}
    }

    // Miss: parse everything, cache imports only
    const result = _parseFreshWithSdk(absPath, sdkNodes, sdkPaths, importsCachePath);
    return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries, {
      compiledRules: result.compiledRules
    });
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
  const { definitions, clauses, forwardRules, queries } = convert.load(filePaths);
  const compiledRules = forwardRules.map(r => forward.compileRule(r));
  const byteSize = _snapshotToFile(cachePath, definitions, clauses, forwardRules, compiledRules, queries);
  return { definitions, clauses, forwardRules, queries, byteSize };
}

/**
 * Load from precompiled binary cache.
 * Restores Store state and uses cached compiled rules.
 * @param {string} cachePath - binary cache file path
 * @returns {Object} calc context (same shape as load())
 */
function loadPrecompiled(cachePath) {
  const buf = fs.readFileSync(cachePath);
  const data = deserialize(buf);
  Store.restore(data);

  const { types: defsObj, clauses: clausesObj, forwardRules, compiledRules, queries: queriesObj } = data.metadata;

  const definitions = new Map(Object.entries(defsObj));
  const clauses = new Map(Object.entries(clausesObj));
  const queries = new Map(Object.entries(queriesObj));

  return _buildCalc(definitions, clauses, forwardRules, queries, {
    compiledRules: _deserializeCompiledRules(compiledRules)
  });
}

/**
 * Convert `code PC V` linear facts into a single `bytecode` arrlit fact.
 * Operates on plain state objects { linear: {hash:count}, persistent: {hash:true} }.
 * Returns a new state with code facts replaced by a bytecode fact.
 * No-op if no code facts found or bytecode fact already exists.
 */
function codeToArrlit(state) {
  const { binToInt } = require('./ffi/convert');
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
  const { binToInt, intToBin } = require('./ffi/convert');
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

  // Walk bytes, group PUSHn data
  const semantic = new Uint32Array(elems.length);
  const zeroBinlit = intToBin(0n);
  let pc = 0;
  while (pc < elems.length) {
    const opVal = Number(Store.child(elems[pc], 0));
    semantic[pc] = elems[pc]; // opcode itself
    if (opVal >= 0x60 && opVal <= 0x7f) {
      const n = opVal - 0x5f;
      if (pc + 1 + n <= elems.length) {
        // Combine next n bytes into a single big-endian value
        let combined = 0n;
        for (let j = 0; j < n; j++) {
          combined = (combined << 8n) | Store.child(elems[pc + 1 + j], 0);
        }
        semantic[pc + 1] = intToBin(combined);
        // Fill remaining positions with 0
        for (let j = 2; j <= n; j++) {
          semantic[pc + 1 + j - 1] = zeroBinlit;
        }
        pc += 1 + n;
      } else {
        pc++;
      }
    } else {
      pc++;
    }
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
