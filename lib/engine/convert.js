/**
 * MDE → Content-Addressed Hash Converter
 *
 * Uses calculus-generated Earley parser + declaration parser.
 *
 * Complexity: O(n) where n = source length
 */

const Store = require('../kernel/store');
const fs = require('fs');
const path = require('path');
const { collectMetavars } = require('./pattern-utils');
const { parseDeclarations } = require('../parser/declarations');
const { computeParserTables, buildParserFromTables } = require('../calculus/builders');
const { hashString, hashCombine } = require('../hash');
const { GRADE_0 } = require('./grades');

// ─── Expression parser ─────────────────────────────────────────────────────

// ILL engine parser: formula operators derived from .calc constructors,
// plus engine-specific extras (concat) and .ill format opts.
const _exprParser = (() => {
  const ill = require('../calculus').loadILL();
  const tables = computeParserTables(ill.constructors);
  // Filter to formula-returning constructors only (exclude structural: comma, hyp, seq)
  // and remove loli (re-added by forwardRules with special -o { } handling)
  tables.operators = tables.operators
    .filter(o => ill.constructors[o.name]?.returnType === 'formula' && o.name !== 'loli');
  // concat (++) is a term-level operator used in EVM programs, not in the calculus
  tables.operators.push({ name: 'concat', op: '++', precedence: 55, assoc: 'left' });
  return buildParserFromTables({
    ...tables,
    binders: { exists: 'exists', forall: 'forall' },
    multiCharFreevars: true,
    numbers: true,
    application: true,
    arrows: true,
    forwardRules: true,
    binaryNormalization: true,
  });
})();

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

// ─── Preserved resource sugar ($prefix) desugaring ──────────────────────────
//
// The $ prefix marks a linear resource as preserved across a forward rule:
// consumed from the LHS and re-produced identically on the RHS. The parser
// wraps $P as preserved(P). This function desugars it by:
//   1. Stripping preserved() wrappers from the antecedent
//   2. Injecting the unwrapped resources into the consequent body
//   3. Returning a clean loli(ante, monad(conseq)) hash — identical to longhand
//
// Errors:
//   $!P — persistent resources are never consumed, so $ is meaningless.
//   $P in consequent — $ only applies to antecedent resources.

/**
 * Desugar preserved($) wrappers in a forward rule formula.
 *
 * @param {number} bodyHash - Parsed formula hash (may contain preserved() nodes)
 * @returns {number} Desugared formula hash (no preserved() nodes)
 */
function desugarPreserved(bodyHash) {
  if (Store.tag(bodyHash) !== 'loli') return bodyHash;

  const ante = Store.child(bodyHash, 0);
  const conseq = Store.child(bodyHash, 1);

  // Collect preserved resources while stripping wrappers from antecedent tensor
  const preserved = [];

  function stripPreserved(h) {
    const t = Store.tag(h);
    if (t === 'preserved') {
      const inner = Store.child(h, 0);
      if (Store.tag(inner) === 'bang') {
        throw new Error(
          '$!P is not allowed: persistent resources (!) are never consumed, ' +
          'so $ (preserved) is meaningless. Use !P instead.'
        );
      }
      preserved.push(inner);
      return inner;
    }
    if (t === 'tensor') {
      const left = stripPreserved(Store.child(h, 0));
      const right = stripPreserved(Store.child(h, 1));
      if (left === Store.child(h, 0) && right === Store.child(h, 1)) return h;
      return Store.put('tensor', [left, right]);
    }
    // !$P: preserved inside bang is meaningless (persistent resources are never consumed)
    if (t === 'bang' && Store.tag(Store.child(h, 1)) === 'preserved') {
      throw new Error(
        '!$P is not allowed: persistent resources (!) are never consumed, ' +
        'so $ (preserved) is meaningless. Use !P instead.'
      );
    }
    return h;
  }

  const cleanAnte = stripPreserved(ante);
  if (preserved.length === 0) return bodyHash;

  // Validate: no stray preserved() nodes in either side.
  // stripPreserved handles tensor and top-level preserved; this catches
  // deep nesting (e.g., preserved inside oplus, with, or other connectives).
  _assertNoPreserved(cleanAnte, 'antecedent');
  _assertNoPreserved(conseq, 'consequent');

  // Inject preserved resources into the consequent body.
  // Forward rules have shape loli(ante, monad(body)). Tensor preserved
  // resources at the front of the body, preserving left-to-right order.
  if (Store.tag(conseq) !== 'monad') {
    throw new Error('$ (preserved) can only be used in forward rules (A -o { B })');
  }
  let conseqBody = Store.child(conseq, 0);
  for (let i = preserved.length - 1; i >= 0; i--) {
    conseqBody = Store.put('tensor', [preserved[i], conseqBody]);
  }

  return Store.put('loli', [cleanAnte, Store.put('monad', [conseqBody])]);
}

/** Throw if any preserved() wrapper remains in a hash tree. */
function _assertNoPreserved(h, location) {
  const t = Store.tag(h);
  if (!t) return;
  if (t === 'preserved') {
    throw new Error(location === 'antecedent'
      ? '$ (preserved) can only appear on top-level antecedent resources, not inside ! or other connectives'
      : '$ (preserved) can only be used on antecedent resources, not in the consequent');
  }
  if (t === 'atom' || t === 'freevar' || t === 'metavar' ||
      t === 'binlit' || t === 'bound' || t === 'strlit') return;
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && Store.isTerm(c)) _assertNoPreserved(c, location);
  }
}

// ─── Named argument helpers ──────────────────────────────────────────────────

/**
 * Strip named_arg sentinels from an arrow chain (type declaration).
 * arrow(named_arg(atom('a'), sort), rest) → arrow(sort, rest) + collects names.
 * @param {number} hash
 * @returns {{ cleanHash: number, argNames: string[] }}
 */
function stripNamedArgsFromArrowChain(hash) {
  const argNames = [];
  let hasNamed = false;

  // First pass: collect names and check if any exist
  let current = hash;
  while (Store.tag(current) === 'arrow') {
    const left = Store.child(current, 0);
    if (Store.tag(left) === 'named_arg') {
      argNames.push(Store.child(Store.child(left, 0), 0)); // atom name
      hasNamed = true;
    } else {
      argNames.push(null);
    }
    current = Store.child(current, 1);
  }

  if (!hasNamed) return { cleanHash: hash, argNames: [] };

  // Second pass: rebuild arrow chain with named_arg stripped
  function rebuild(h) {
    if (Store.tag(h) !== 'arrow') return h;
    const left = Store.child(h, 0);
    const right = Store.child(h, 1);
    const cleanLeft = Store.tag(left) === 'named_arg' ? Store.child(left, 1) : left;
    const cleanRight = rebuild(right);
    if (cleanLeft === left && cleanRight === right) return h;
    return Store.put('arrow', [cleanLeft, cleanRight]);
  }

  return { cleanHash: rebuild(hash), argNames };
}

/**
 * Resolve named_arg sentinels in a term tree (call sites in rules/clauses).
 * Walks the tree; for predicates with named_arg children, resolves to positional.
 * @param {number} hash
 * @param {Map<string, string[]>} argNamesTable
 * @returns {number} clean hash
 */
function resolveNamedArgSentinels(hash, argNamesTable) {
  return _resolveWalk(hash, argNamesTable, Store.TAG['named_arg']);
}

function _resolveWalk(h, argNamesTable, namedArgTag) {
  const t = Store.tag(h);
  if (!t) return h;
  // Leaf tags: no children to walk
  if (t === 'atom' || t === 'freevar' || t === 'metavar' || t === 'binlit' ||
      t === 'bound' || t === 'strlit' || t === 'charlit') return h;

  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (!elems || elems.length === 0) return h;
    let changed = false;
    const newElems = new Uint32Array(elems.length);
    for (let i = 0; i < elems.length; i++) {
      newElems[i] = _resolveWalk(elems[i], argNamesTable, namedArgTag);
      if (newElems[i] !== elems[i]) changed = true;
    }
    return changed ? Store.putArray(newElems) : h;
  }

  const tid = Store.tagId(h);
  const a = Store.arity(h);

  // Predicate application with named_arg children — resolve to positional.
  // Only predicates (tid >= PRED_BOUNDARY) can have named call-site args;
  // named_arg itself is below PRED_BOUNDARY so bare sentinels skip this branch.
  if (tid >= Store.PRED_BOUNDARY && a > 0) {
    let hasNamedChild = false;
    for (let i = 0; i < a; i++) {
      const c = Store.child(h, i);
      if (typeof c === 'number' && Store.tagId(c) === namedArgTag) {
        hasNamedChild = true;
        break;
      }
    }

    if (hasNamedChild) {
      const predName = Store.TAG_NAMES[tid];
      const argNames = argNamesTable.get(predName);
      if (!argNames) {
        throw new Error(
          `Named arguments used for '${predName}', but '${predName}' has no named declarations`
        );
      }
      return _resolveNamedCallSite(predName, h, a, argNames, argNamesTable, namedArgTag);
    }
  }

  // Recurse into children
  if (a === 0) return h;
  let changed = false;
  const nc = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && Store.isTerm(c)) {
      const r = _resolveWalk(c, argNamesTable, namedArgTag);
      if (r !== c) changed = true;
      nc.push(r);
    } else {
      nc.push(c);
    }
  }
  return changed ? Store.put(t, nc) : h;
}

/**
 * Resolve a single predicate call with named_arg children.
 * Implements the positional-then-named convention (D5).
 */
function _resolveNamedCallSite(predName, h, arity, argNames, argNamesTable, namedArgTag) {
  const result = new Array(argNames.length);
  const filled = new Set();

  // Collect children
  const children = [];
  for (let i = 0; i < arity; i++) {
    children.push(Store.child(h, i));
  }

  // Phase 1: positional args (before first named)
  let posIdx = 0;
  let namedStarted = false;
  for (let i = 0; i < children.length; i++) {
    const c = children[i];
    const isNamed = typeof c === 'number' && Store.tagId(c) === namedArgTag;

    if (isNamed) {
      namedStarted = true;
      const name = Store.child(Store.child(c, 0), 0); // atom name
      const expr = Store.child(c, 1);

      const idx = argNames.indexOf(name);
      if (idx === -1) {
        throw new Error(
          `'${predName}' has no argument '${name}' (known: ${argNames.filter(n => n !== null).join(', ')})`
        );
      }
      if (filled.has(idx)) {
        throw new Error(
          `Duplicate named argument '${name}' in call to '${predName}'`
        );
      }
      // Recurse into the expression
      result[idx] = _resolveWalk(expr, argNamesTable, namedArgTag);
      filled.add(idx);
    } else {
      if (namedStarted) {
        throw new Error(
          `Positional argument after named argument in call to '${predName}'`
        );
      }
      // Recurse into positional arg
      result[posIdx] = typeof c === 'number' && Store.isTerm(c)
        ? _resolveWalk(c, argNamesTable, namedArgTag) : c;
      filled.add(posIdx);
      posIdx++;
    }
  }

  // Phase 2: check completeness
  if (filled.size !== argNames.length) {
    const missingNames = argNames
      .map((n, i) => filled.has(i) ? null : (n || `arg${i}`))
      .filter(n => n !== null);
    throw new Error(
      `Missing arguments for '${predName}': ${missingNames.join(', ')}`
    );
  }

  return Store.put(predName, result);
}

/**
 * Load single MDE file into existing collections.
 * Two-pass: definitions first (building argNamesTable), then rules/clauses.
 *
 * @param {Object} [opts]
 * @param {Set} [opts.alreadyImported] - skip already-imported files
 * @param {Map} [opts.argNamesTable] - named argument registry
 * @param {Map} [opts.querySettings] - directive settings (rules: ...) per query kind
 * @param {Map} [opts.splitQueries] - separated queries (|- or =>) per directive kind
 * @param {Array} [opts.moduleDecls] - collects @module declarations
 */
function loadFile(filePath, definitions, clauses, forwardRules, queries, opts = {}) {

  let source = fs.readFileSync(filePath, 'utf8');

  // Resolve #import(path) directives
  const imported = opts.alreadyImported || new Set();
  source = resolveImports(source, filePath, imported);

  const decls = parseDeclarations(source, _exprParser);
  const argNamesTable = opts.argNamesTable || new Map();

  // ── Pass 1: definitions (no premises, no monad) ──
  for (const decl of decls) {
    if (decl.type === 'query') continue; // queries resolved in pass 2
    if (decl.type !== 'declaration') continue;
    const { name, bodyHash, premises } = decl;
    if (!bodyHash) continue;

    // Only process definitions in pass 1
    if (hasMonad(bodyHash) || premises.length > 0) continue;

    // Strip named_arg sentinels from arrow chain
    const { cleanHash, argNames } = stripNamedArgsFromArrowChain(bodyHash);
    if (argNames.length > 0) {
      argNamesTable.set(name, argNames);
    }

    if (definitions.has(name)) {
      throw new Error(`Duplicate definition '${name}' (already defined)`);
    }
    definitions.set(name, cleanHash);
  }

  // ── Pass 2: queries + forward rules + backward clauses + directives ──
  for (const decl of decls) {
    if (decl.type === 'query') {
      if (decl.kind) {
        if (decl.separator) {
          // Split query: |- (backward entailment) or => (forward reachability)
          const entry = {
            separator: decl.separator,
            lhsHash: decl.lhsHash ? resolveNamedArgSentinels(decl.lhsHash, argNamesTable) : null,
            rhsHash: decl.rhsHash ? resolveNamedArgSentinels(decl.rhsHash, argNamesTable) : null,
          };
          if (!opts.splitQueries) opts.splitQueries = new Map();
          opts.splitQueries.set(decl.kind, entry);
        } else if (decl.bodyHash) {
          queries.set(decl.kind, resolveNamedArgSentinels(decl.bodyHash, argNamesTable));
        }
        // T10: Store query settings (rules: ...) if present
        if (decl.settings && opts.querySettings) {
          opts.querySettings.set(decl.kind, decl.settings);
        }
      }
      continue;
    }
    // T12: Collect @module directives
    if (decl.type === 'directive' && decl.key === 'module' && opts.moduleDecls) {
      opts.moduleDecls.push(decl.args);
      continue;
    }
    if (decl.type !== 'declaration') continue;
    const { name, bodyHash, premises } = decl;
    if (!bodyHash) continue;

    // Skip definitions (handled in pass 1)
    if (!hasMonad(bodyHash) && premises.length === 0) continue;

    // Resolve named_arg sentinels (no-op when named_arg tag never registered),
    // then desugar $-preserved resources in forward rules (TODO_0149)
    let cleanBodyHash = resolveNamedArgSentinels(bodyHash, argNamesTable);
    cleanBodyHash = desugarPreserved(cleanBodyHash);
    const cleanPremises = premises.map(p => resolveNamedArgSentinels(p, argNamesTable));

    if (hasMonad(cleanBodyHash)) {
      // Forward rule
      if (forwardRules.some(r => r.name === name)) {
        throw new Error(`Duplicate forward rule '${name}' (already defined)`);
      }
      forwardRules.push({
        name,
        hash: cleanBodyHash,
        antecedent: extractAntecedent(cleanBodyHash),
        consequent: extractConsequent(cleanBodyHash)
      });
    } else {
      // Backward chaining clause
      if (clauses.has(name)) {
        throw new Error(`Duplicate clause '${name}' (already defined)`);
      }
      clauses.set(name, { hash: cleanBodyHash, premises: cleanPremises });
    }
  }
}

/**
 * Lightweight scan for declaration names in source text.
 * Uses regex, not full parse — avoids failures on files that depend on imported types.
 * Finds: `name: ...` declarations and `#kind ...` query directives.
 */
function _scanDeclNames(source, label, nameToLabel) {
  // Match lines like: `name: body.` or `name/case: body.`
  // Declaration: identifier (with optional /) at start of line, followed by ':'
  const declRe = /^[ \t]*([A-Za-z_][A-Za-z0-9_/]*)\s*:/gm;
  let m;
  while ((m = declRe.exec(source)) !== null) {
    nameToLabel.set(m[1], label);
  }
  // Match query directives: `#kind ...`
  const queryRe = /^[ \t]*#([A-Za-z_][A-Za-z0-9_]*)/gm;
  while ((m = queryRe.exec(source)) !== null) {
    if (m[1] !== 'import') { // skip #import
      nameToLabel.set('#' + m[1], label);
    }
  }
}

/**
 * Load MDE file(s)
 * @param {string|string[]} filePaths - single path or array of paths
 * @returns {{ definitions: Map, clauses: Map, forwardRules: Array, queries: Map, argNamesTable: Map, querySettings: Map, moduleDecls: Array, importTree: Array }}
 */
function load(filePaths) {
  const definitions = new Map();
  const clauses = new Map();
  const forwardRules = [];
  const queries = new Map();
  const argNamesTable = new Map();
  const querySettings = new Map();
  const splitQueries = new Map();
  const moduleDecls = [];

  const paths = Array.isArray(filePaths) ? filePaths : [filePaths];
  for (const p of paths) {
    loadFile(p, definitions, clauses, forwardRules, queries, {
      argNamesTable, querySettings, splitQueries, moduleDecls
    });
  }

  // T3: Source label discovery — use import tree to map declarations to source files.
  // Uses lightweight regex scan (not full parse) to avoid parse failures on
  // files that depend on imported types. Only needs to find declaration names.
  const tree = buildImportTree(paths[0]);
  const nameToLabel = new Map();
  for (const node of tree) {
    const label = path.basename(node.path, path.extname(node.path));
    _scanDeclNames(node.source, label, nameToLabel);
  }

  // Tag forward rules and clauses with source labels
  const rootLabel = path.basename(paths[0], path.extname(paths[0]));
  for (const r of forwardRules) r.sourceLabel = nameToLabel.get(r.name) || rootLabel;
  for (const [name, c] of clauses) c.sourceLabel = nameToLabel.get(name) || rootLabel;

  return { definitions, clauses, forwardRules, queries, argNamesTable,
    querySettings, splitQueries, moduleDecls, importTree: tree };
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
      const grade = Store.child(h, 0);
      const inner = Store.child(h, 1);
      if (grade === GRADE_0) {
        throw new Error(
          'Grade-0 resources (!_0) cannot appear in queries or initial states — ' +
          'they are compile-time only (THY_0015 §2.1).'
        );
      }
      persistent[inner] = true;
    } else {
      linear[h] = (linear[h] || 0) + 1;
    }
  }
  walk(body);

  // Phase 4: Validate — no unbound metavars
  const allMetavars = new Set();
  collectMetavars(body, allMetavars);
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
 * Parse a single expression string to a content-addressed hash.
 * Raw parser — may return hashes containing named_arg sentinels
 * (e.g. for `(name: expr)` syntax). Use resolveNamedArgSentinels()
 * to resolve sentinels to positional; loadFile does this automatically.
 * @param {string} source
 * @returns {number} hash
 */
function parseExpr(source) {
  return _exprParser(source);
}

module.exports = {
  load,
  loadFile,
  parseExpr,
  hasMonad,
  decomposeQuery,
  desugarPreserved,
  buildImportTree,
  computeTreeHashes,
  extractTopLevelImports,
  stripNamedArgsFromArrowChain,
  resolveNamedArgSentinels
};
