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

// ─── Expression parser ─────────────────────────────────────────────────────

// ILL operator tables (static, derived from ill.calc connective definitions).
// Embedded directly to avoid async calculus loader dependency.
const ILL_ENGINE_TABLES = {
  operators: [
    { name: 'tensor', op: '*', precedence: 60, assoc: 'left' },
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

/**
 * Check if expression contains monad (forward rule)
 * @param {number} hash
 * @returns {boolean}
 */
function hasMonad(hash) {
  const node = Store.get(hash);
  if (!node) return false;
  if (node.tag === 'monad') return true;
  for (const c of node.children) {
    if (typeof c === 'number' && hasMonad(c)) return true;
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
  source = resolveImports(source, filePath);

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

/**
 * Decompose a tensor expression hash into linear and persistent facts
 * Walks tensor tree, splitting !X into persistent and X into linear
 * @param {number} hash
 * @returns {{ linear: Object, persistent: Object }}
 */
function decomposeQuery(hash) {
  const linear = {}, persistent = {};
  function walk(h) {
    const node = Store.get(h);
    if (node.tag === 'tensor') {
      walk(node.children[0]);
      walk(node.children[1]);
    } else if (node.tag === 'bang') {
      persistent[node.children[0]] = true;
    } else {
      linear[h] = (linear[h] || 0) + 1;
    }
  }
  walk(hash);
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
  parseExpr,
  hasMonad,
  extractAntecedent,
  extractConsequent,
  decomposeQuery
};
