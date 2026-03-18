/**
 * MDE → Content-Addressed Hash Converter
 *
 * Uses calculus-generated Pratt parser + declaration parser.
 * No tree-sitter dependency.
 *
 * Complexity: O(n) where n = source length
 */

const Store = require('../kernel/store');
const fs = require('fs');
const path = require('path');
const { expandHexNotation } = require('./hex');
const { parseDeclarations } = require('../parser/declarations');
const { buildParserFromTables } = require('../calculus/builders');
const { hashString, hashCombine } = require('../hash');

// ─── Expression parser ─────────────────────────────────────────────────────

// ILL operator tables (static, derived from ill.calc connective definitions).
// Embedded directly to avoid async calculus loader dependency.
const ILL_ENGINE_TABLES = {
  operators: [
    { name: 'tensor', op: '*', precedence: 60, assoc: 'left' },
    { name: 'concat', op: '++', precedence: 55, assoc: 'left' },
    { name: 'with', op: '&', precedence: 70, assoc: 'left' },
    { name: 'oplus', op: '+', precedence: 65, assoc: 'left' },
  ],
  nullary: { I: 'one', zero: 'zero' },
  unaryPrefix: {
    '!': { name: 'bang', precedence: 80, keyword: false },
    exists: { name: 'exists', precedence: 45, keyword: true },
    forall: { name: 'forall', precedence: 45, keyword: true },
  },
  binders: { exists: 'exists', forall: 'forall' },
  multiCharFreevars: true,
  numbers: true,
  application: true,
  arrows: true,
  forwardRules: true,
  binaryNormalization: true,
};

const _exprParser = buildParserFromTables(ILL_ENGINE_TABLES);

/**
 * Resolve #import(path) directives by inlining file contents (recursive)
 * @param {string} source
 * @param {string} basePath - absolute path of the file containing the imports
 * @returns {string}
 */
function resolveImports(source, basePath, imported = new Set()) {
  return source.replace(/#import\(([^)]+)\)/g, (match, relPath) => {
    const resolved = path.resolve(path.dirname(basePath), relPath.trim());
    if (imported.has(resolved)) return '';  // dedup: skip already-imported files
    imported.add(resolved);
    let imported_content = fs.readFileSync(resolved, 'utf8');
    return resolveImports(imported_content, resolved, imported);
  });
}

// ─── Import tree & content hashing ──────────────────────────────────────────

/**
 * Build import tree from file. Returns topo-sorted list [{path, source, deps}].
 * Reads all files but does NOT parse. Used for hash computation + cache lookup.
 * @param {string} filePath - path to root file
 * @returns {Array<{path: string, source: string, deps: string[]}>}
 */
function buildImportTree(filePath) {
  const absPath = path.resolve(filePath);
  const visited = new Map();
  const order = [];

  function visit(fp) {
    if (visited.has(fp)) return;
    visited.set(fp, null); // mark in-progress
    const source = fs.readFileSync(fp, 'utf8');
    const deps = [];
    const importRegex = /#import\(([^)]+)\)/g;
    let match;
    while ((match = importRegex.exec(source)) !== null) {
      const resolved = path.resolve(path.dirname(fp), match[1].trim());
      if (!deps.includes(resolved)) deps.push(resolved);
      if (!visited.has(resolved)) visit(resolved);
    }
    const node = { path: fp, source, deps };
    visited.set(fp, node);
    order.push(node);
  }

  visit(absPath);
  return order;
}

/**
 * Compute cumulative content hashes for each node in the import tree.
 * Each file's hash includes its source + transitive dependency hashes.
 * @param {Array<{path: string, source: string, deps: string[]}>} tree
 * @returns {Map<string, number>} absPath → 32-bit hash
 */
function computeTreeHashes(tree) {
  const hashes = new Map();
  for (const node of tree) {
    const sourceHash = hashString(node.source);
    if (node.deps.length === 0) {
      hashes.set(node.path, sourceHash);
    } else {
      const depHashes = [...node.deps].sort().map(d => hashes.get(d));
      hashes.set(node.path, hashCombine(sourceHash, ...depHashes));
    }
  }
  return hashes;
}

/**
 * Extract top-level #import directives (before any declarations).
 * Only these imports form the SDK cache tier; inline imports (e.g. inside
 * #symex blocks) are part of the top file's content.
 * @param {string} source - file source text
 * @param {string} basePath - absolute path of the file
 * @returns {string[]} absolute paths of top-level imports
 */
function extractTopLevelImports(source, basePath) {
  const imports = [];
  for (const line of source.split('\n')) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('%')) continue;
    const m = trimmed.match(/^#import\(([^)]+)\)/);
    if (m) {
      imports.push(path.resolve(path.dirname(basePath), m[1].trim()));
    } else {
      break;
    }
  }
  return imports;
}

// ─── Expression helpers ─────────────────────────────────────────────────────

/**
 * Check if expression contains monad (forward rule)
 * @param {number} hash
 * @returns {boolean}
 */
function hasMonad(hash, computationTag = 'monad') {
  const node = Store.get(hash);
  if (!node) return false;
  if (node.tag === computationTag) return true;
  for (const c of node.children) {
    if (typeof c === 'number' && hasMonad(c, computationTag)) return true;
  }
  return false;
}

/**
 * Extract antecedent from lollipop: A -o B → A
 * @param {number} hash
 * @returns {number}
 */
function extractAntecedent(hash) {
  const node = Store.get(hash);
  if (node?.tag === 'loli') return node.children[0];
  return hash;
}

/**
 * Extract consequent from lollipop: A -o B → B
 * @param {number} hash
 * @returns {number}
 */
function extractConsequent(hash) {
  const node = Store.get(hash);
  if (node?.tag === 'loli') return node.children[1];
  return hash;
}

/**
 * Load single MDE file into existing collections
 */
function loadFile(filePath, types, clauses, forwardRules, queries, opts = {}) {

  let source = fs.readFileSync(filePath, 'utf8');

  // Resolve #import(path) directives first (before hex expansion,
  // so imported content gets hex-expanded too)
  const imported = opts.alreadyImported || new Set();
  source = resolveImports(source, filePath, imported);

  // Expand N_XX hex notation to binary if enabled (default: true)
  if (opts.expandHex !== false) {
    source = expandHexNotation(source);
  }

  const decls = parseDeclarations(source, _exprParser);

  for (const decl of decls) {
    if (decl.type === 'query') {
      if (decl.kind && decl.bodyHash) {
        queries.set(decl.kind, decl.bodyHash);
      }
      continue;
    }

    if (decl.type !== 'declaration') continue;

    const { name, bodyHash, premises } = decl;
    if (!bodyHash) continue;

    if (hasMonad(bodyHash)) {
      // Forward rule — check for duplicate
      if (forwardRules.some(r => r.name === name)) {
        throw new Error(`Duplicate forward rule '${name}' (already defined)`);
      }
      forwardRules.push({
        name,
        hash: bodyHash,
        antecedent: extractAntecedent(bodyHash),
        consequent: extractConsequent(bodyHash)
      });
    } else if (premises.length > 0) {
      // Backward chaining clause — check for duplicate
      if (clauses.has(name)) {
        throw new Error(`Duplicate clause '${name}' (already defined)`);
      }
      clauses.set(name, { hash: bodyHash, premises });
    } else {
      // Type or constructor — check for duplicate
      if (types.has(name)) {
        throw new Error(`Duplicate type/constructor '${name}' (already defined)`);
      }
      types.set(name, bodyHash);
    }
  }
}

/**
 * Load MDE file(s)
 * @param {string|string[]} filePaths - single path or array of paths
 * @returns {{ types: Map, clauses: Map, forwardRules: Array, queries: Map }}
 */
function load(filePaths) {
  const types = new Map();
  const clauses = new Map();
  const forwardRules = [];
  const queries = new Map();

  const paths = Array.isArray(filePaths) ? filePaths : [filePaths];
  for (const p of paths) {
    loadFile(p, types, clauses, forwardRules, queries);
  }

  return { types, clauses, forwardRules, queries };
}

// ─── Quantifier elimination for queries ─────────────────────────────────────

/**
 * Substitute bound variables (de Bruijn indices) with replacement terms.
 * @param {number} h - Term hash
 * @param {Map<number, number>} subs - bound(N) hash → replacement hash
 * @returns {number} Term with bound vars replaced
 */
function _substituteBound(h, subs) {
  if (subs.has(h)) return subs.get(h);
  const t = Store.tag(h);
  if (!t) return h;
  if (t === 'atom' || t === 'freevar' || t === 'metavar' || t === 'binlit' || t === 'bound') return h;

  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (!elems || elems.length === 0) return h;
    let changed = false;
    const newElems = new Uint32Array(elems.length);
    for (let i = 0; i < elems.length; i++) {
      const ne = _substituteBound(elems[i], subs);
      newElems[i] = ne;
      if (ne !== elems[i]) changed = true;
    }
    return changed ? Store.putArray(newElems) : h;
  }

  const a = Store.arity(h);
  if (a === 0) return h;
  let changed = false;
  const nc = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) {
      const r = _substituteBound(c, subs);
      if (r !== c) changed = true;
      nc.push(r);
    } else {
      nc.push(c);
    }
  }
  return changed ? Store.put(t, nc) : h;
}

/**
 * Collect all metavar hashes in a term (for unbound variable detection).
 * @param {number} h - Term hash
 * @param {Set<number>} found - Accumulator set of metavar hashes
 */
function _collectMetavars(h, found) {
  const t = Store.tag(h);
  if (!t) return;
  if (t === 'metavar') { found.add(h); return; }
  if (t === 'atom' || t === 'freevar' || t === 'binlit' || t === 'bound') return;

  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (elems) for (let i = 0; i < elems.length; i++) _collectMetavars(elems[i], found);
    return;
  }

  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) _collectMetavars(c, found);
  }
}

/**
 * Decompose a query expression into linear and persistent facts.
 *
 * Processes quantifiers via standard proof-theoretic elimination:
 *   forall X. A(X) → eigenvariable (freevar) — "for all X"
 *   exists X. A(X) → witness variable (metavar) — "find some X"
 *
 * Then walks the tensor tree, splitting !X into persistent and X into linear.
 * Throws if any metavars remain unbound (not introduced by exists).
 *
 * @param {number} hash
 * @returns {{ linear: Object, persistent: Object }}
 */
function decomposeQuery(hash) {
  // Phase 1: Strip quantifiers, collect binder list (outer → inner order).
  // Parser uses de Bruijn: forall(body) where body has bound(N).
  // De Bruijn index 0 = innermost binder, N = outermost.
  const binders = []; // [{kind: 'forall'|'exists'}] in outer→inner order
  let body = hash;

  while (true) {
    const t = Store.tag(body);
    if (t === 'forall' || t === 'exists') {
      binders.push({ kind: t });
      body = Store.child(body, 0);
    } else {
      break;
    }
  }

  // Build bound→replacement substitution.
  // De Bruijn: outermost binder has index (depth-1), innermost has index 0.
  const subs = new Map();
  const existsVars = new Set();
  const totalDepth = binders.length;

  for (let i = 0; i < totalDepth; i++) {
    const dbIndex = BigInt(totalDepth - 1 - i); // outer=highest, inner=0
    const boundHash = Store.put('bound', [dbIndex]);
    if (binders[i].kind === 'forall') {
      const eigen = Store.put('freevar', [`_q${i}`]);
      subs.set(boundHash, eigen);
    } else {
      const witness = Store.put('metavar', [`_q${i}`]);
      subs.set(boundHash, witness);
      existsVars.add(witness);
    }
  }

  // Phase 2: Substitute bound variables with eigenvars/witnesses
  if (subs.size > 0) {
    body = _substituteBound(body, subs);
  }

  // Phase 3: Decompose tensor into linear/persistent
  const linear = {}, persistent = {};
  function walk(h) {
    const t = Store.tag(h);
    if (t === 'tensor') {
      walk(Store.child(h, 0));
      walk(Store.child(h, 1));
    } else if (t === 'bang') {
      persistent[Store.child(h, 0)] = true;
    } else {
      linear[h] = (linear[h] || 0) + 1;
    }
  }
  walk(body);

  // Phase 4: Validate — no unbound metavars
  const allMetavars = new Set();
  _collectMetavars(body, allMetavars);
  const unbound = [];
  for (const mv of allMetavars) {
    if (!existsVars.has(mv)) unbound.push(mv);
  }
  if (unbound.length > 0) {
    const names = unbound.map(h => Store.child(h, 0));
    throw new Error(
      `Query has unbound variables: ${names.join(', ')}. ` +
      `Bind them with forall (eigenvariable) or exists (witness).`
    );
  }

  return { linear, persistent };
}

/**
 * Parse a single expression string
 * @param {string} source
 * @returns {number} hash
 */
function parseExpr(source, opts = {}) {
  // Expand N_XX hex notation to binary if enabled (default: true)
  let expandedSource = source;
  if (opts.expandHex !== false) {
    expandedSource = expandHexNotation(source);
  }

  return _exprParser(expandedSource);
}

module.exports = {
  load,
  loadFile,
  parseExpr,
  hasMonad,
  decomposeQuery,
  buildImportTree,
  computeTreeHashes,
  extractTopLevelImports
};
