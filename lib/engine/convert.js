/**
 * MDE → Content-Addressed Hash Converter
 *
 * Uses calculus-generated Earley parser + declaration parser.
 *
 * Complexity: O(n) where n = source length
 */

import Store from '../kernel/store.js';
import fs from 'fs';
import path from 'path';
import { performance } from 'perf_hooks';
import { collectMetavars } from './pattern-utils.js';
import { parseDecls, subHashes } from '../parser/declarations.js';
import { SORT_PREDS } from './sorts.js';
import { DECIMATE_PREDS } from './decimate.js';
import { _parseSignature } from './type-check.js';
import { parserTables, parserFromTables } from '../calculus/builders.js';
import { hashString, hashCombine } from '../hash.js';
import { debruijnSubst } from '../kernel/substitute.js';
import { grade0, gradeW } from './grades.js';
import { ILL_COMPUTATION } from './formula-utils.js';
import calculus from '../calculus/index.js';
// ─── Expression parser ─────────────────────────────────────────────────────

/**
 * Loader configuration — which parser and which connective tags the .ill
 * loader reads (TODO_0265 Phase 2b). Default = the ILL instance; a second
 * calculus (till, Phase 4) passes its own via load()/loadFile()
 * opts.loaderConfig:
 *   buildParser: () => parse   — replaces the baked-in ILL expression parser
 *   connTags: { computation (role record), implication, product,
 *               exponential, preserved }
 *   grade0: () => hash         — the compile-time grade atom
 */
const DEFAULT_LOADER_CONFIG = {
  buildParser: null,
  connTags: {
    computation: ILL_COMPUTATION,
    implication: 'loli',
    product: 'tensor',
    exponential: 'bang',
    preserved: 'preserved',
  },
  grade0,
  // timed: true (till) runs desugarTimed over every rule — window-arith
  // lowering + timed-form validation. ILL rules cannot contain timed
  // wrappers, so the default skips the walk entirely.
  timed: false,
};

// ILL engine parser: formula operators derived from .calc constructors,
// plus engine-specific extras (concat) and .ill format opts.
// Lazy: built on first use, not at require() time (~20ms, loads entire ILL calculus).
let _exprParser = null;
function _getExprParser(loaderConfig = DEFAULT_LOADER_CONFIG) {
  if (loaderConfig.buildParser) {
    // Custom parser: memoized on the config object itself.
    if (!loaderConfig._parser) loaderConfig._parser = loaderConfig.buildParser();
    return loaderConfig._parser;
  }
  if (_exprParser) return _exprParser;
  const ill = calculus.loadILL();
  const tables = parserTables(ill.constructors);
  // Filter to formula-returning constructors only (exclude structural: comma, hyp, seq)
  // and remove loli (re-added by forwardRules with special -o { } handling)
  tables.operators = tables.operators
    .filter(o => ill.constructors[o.name]?.returnType === 'formula' && o.name !== 'loli');
  // concat (++) is a term-level operator used in EVM programs, not in the calculus
  tables.operators.push({ name: 'concat', op: '++', precedence: 55, assoc: 'left' });
  _exprParser = parserFromTables({
    ...tables,
    binders: { exists: 'exists', forall: 'forall' },
    multiCharFreevars: true,
    numbers: true,
    application: true,
    arrows: true,
    forwardRules: true,
    binaryNormalization: true,
  });
  return _exprParser;
}

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
function extractAntecedent(hash, implicationTag = 'loli') {
  const node = Store.get(hash);
  if (node?.tag === implicationTag) return node.children[0];
  return hash;
}

/**
 * Extract consequent from lollipop: A -o B → B
 * @param {number} hash
 * @returns {number}
 */
function extractConsequent(hash, implicationTag = 'loli') {
  const node = Store.get(hash);
  if (node?.tag === implicationTag) return node.children[1];
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
 * Timed loaders (stripStamps = true): a `$A@Q` antecedent keeps its stamped
 * pattern at(A, Q), but the CONSEQUENT copy is injected UNSTAMPED — E3:
 * timed-$ is ordinary consume + produce, and the scheduler stamps every
 * output at a(m)+d. Injecting the stamped copy verbatim would both violate
 * E3 (frozen stamp) and trip the no-explicit-consequent-stamps validation.
 *
 * @param {number} bodyHash - Parsed formula hash (may contain preserved() nodes)
 * @returns {number} Desugared formula hash (no preserved() nodes)
 */
function desugarPreserved(bodyHash, computation = ILL_COMPUTATION,
                          connTags = DEFAULT_LOADER_CONFIG.connTags,
                          stripStamps = false) {
  const _impl = connTags.implication, _prod = connTags.product;
  const _exp = connTags.exponential, _pres = connTags.preserved;
  if (Store.tag(bodyHash) !== _impl) return bodyHash;

  const ante = Store.child(bodyHash, 0);
  const conseq = Store.child(bodyHash, 1);

  // Collect preserved resources while stripping wrappers from antecedent tensor
  const preserved = [];

  function stripPreserved(h) {
    const t = Store.tag(h);
    if (t === _pres) {
      const inner = Store.child(h, 0);
      if (Store.tag(inner) === _exp) {
        throw new Error(
          '$!P is not allowed: persistent resources (!) are never consumed, ' +
          'so $ (preserved) is meaningless. Use !P instead.'
        );
      }
      preserved.push(stripStamps && Store.tag(inner) === 'at'
        ? Store.child(inner, 0) : inner);
      return inner;
    }
    if (t === _prod) {
      const left = stripPreserved(Store.child(h, 0));
      const right = stripPreserved(Store.child(h, 1));
      if (left === Store.child(h, 0) && right === Store.child(h, 1)) return h;
      return Store.put(_prod, [left, right]);
    }
    // !$P: preserved inside bang is meaningless (persistent resources are never consumed)
    if (t === _exp && Store.tag(Store.child(h, 1)) === _pres) {
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
  _assertNoPreserved(cleanAnte, 'antecedent', _pres);
  _assertNoPreserved(conseq, 'consequent', _pres);

  // Inject preserved resources into the consequent body.
  // Forward rules have shape loli(ante, {body}). Tensor preserved
  // resources at the front of the body, preserving left-to-right order.
  // The computation node is rebuilt through the role record so a graded
  // monad's grade child is threaded through unchanged (D7: timed-$).
  if (Store.tag(conseq) !== computation.tag) {
    throw new Error('$ (preserved) can only be used in forward rules (A -o { B })');
  }
  let conseqBody = Store.child(conseq, computation.bodyIdx);
  for (let i = preserved.length - 1; i >= 0; i--) {
    conseqBody = Store.put(_prod, [preserved[i], conseqBody]);
  }

  let newConseq;
  if (computation.gradeIdx === null) {
    newConseq = Store.put(computation.tag, [conseqBody]);
  } else {
    const kids = [];
    kids[computation.gradeIdx] = Store.child(conseq, computation.gradeIdx);
    kids[computation.bodyIdx] = conseqBody;
    newConseq = Store.put(computation.tag, kids);
  }
  return Store.put(_impl, [cleanAnte, newConseq]);
}

// ─── Timed forms: window desugaring + validation (TODO_0265 Phase 3) ────────
//
// `after (Q+2)` parses to after(qexpr_add(Q, ratlit 2)). Arithmetic in a
// grade position is SUGAR for backward propositions (E7.1) — each qexpr
// node lowers to a fresh variable resolved by a persistent q-op goal:
//
//   after (Q+2)   ⇒   after Q$0  with  !qplus Q 2 Q$0
//
// tensored into the antecedent. Downstream (compile.js, the timed matcher)
// only ever sees ATOMIC window expressions — a ground rational or a bound
// variable — so no expression evaluator exists anywhere in the engine;
// the existing persistent-goal machinery (FFI + clauses) computes the
// value, and E7.1's mode discipline (ground-after-substitution) falls out
// of the q-op modes.
//
// Validation (timed loaders only, loaderConfig.timed):
//   qexpr outside window args        — v1: @-position arithmetic rejected (E7.1)
//   after/before/read in consequent  — they are antecedent guards
//   at() in a rule consequent        — output stamps come from the scheduler (E2)
//   bang over at()                   — no stamped persistents (D15 backstop)
//   read !P / ! read P               — persistent facts need no read marker

// Window-arithmetic AST tags (generic — the parser emits them). The
// LOWERING TARGETS are calculus data: a timed calculus supplies
// loaderConfig.qexprPreds (till/gill point add/mul at the SHARED numeric
// names per the TODO_0011 §3 collapse, sub/div at the q-specific ones).
// There is deliberately no engine default — predicate names never live in
// engine code, and a missing map is a loud error at the first qexpr use.
const _QEXPR_TAGS = new Set(['qexpr_add', 'qexpr_sub', 'qexpr_mul', 'qexpr_div']);

/**
 * Desugar window arithmetic and validate timed forms in a rule formula.
 * Identity for formulas without timed wrappers.
 * @param {number} bodyHash - Rule formula (loli(ante, conseq)) or clause
 * @param {Object} connTags - loader connective tags
 * @returns {number} lowered formula hash
 */
function desugarTimed(bodyHash, connTags = DEFAULT_LOADER_CONFIG.connTags, qexprPreds = null) {
  const _impl = connTags.implication, _prod = connTags.product;
  const _exp = connTags.exponential;
  if (Store.tag(bodyHash) !== _impl) {
    _validateTimed(bodyHash, 'clause', connTags);
    return bodyHash;
  }

  const origAnte = Store.child(bodyHash, 0);
  const conseq = Store.child(bodyHash, 1);
  let fresh = 0;
  const goals = [];

  function lower(e) {
    const t = Store.tag(e);
    if (!_QEXPR_TAGS.has(t)) return e;
    const pred = qexprPreds && qexprPreds[t];
    if (!pred) {
      throw new Error(`desugarTimed: window arithmetic '${t}' has no lowering target — ` +
        'a timed calculus must supply loaderConfig.qexprPreds (q-op predicate names are calculus data, not an engine default)');
    }
    const a = lower(Store.child(e, 0));
    const b = lower(Store.child(e, 1));
    // '$' is unlexable in identifiers, so Q$n cannot collide with user vars
    const v = Store.put('metavar', ['Q$' + (fresh++)]);
    goals.push(Store.put(_exp, [gradeW(), Store.put(pred, [a, b, v])]));
    return v;
  }

  function walkAnte(h) {
    const t = Store.tag(h);
    if (t === _prod) {
      const l = walkAnte(Store.child(h, 0));
      const r = walkAnte(Store.child(h, 1));
      if (l === Store.child(h, 0) && r === Store.child(h, 1)) return h;
      return Store.put(_prod, [l, r]);
    }
    if (t === 'after' || t === 'before') {
      const e = Store.child(h, 0);
      const le = lower(e);
      return le === e ? h : Store.put(t, [le]);
    }
    return h;
  }

  let ante = walkAnte(origAnte);
  for (const g of goals) ante = Store.put(_prod, [ante, g]);

  _validateTimed(ante, 'antecedent', connTags);
  _validateTimed(conseq, 'consequent', connTags);
  return (ante === origAnte) ? bodyHash : Store.put(_impl, [ante, conseq]);
}

/** True iff `tag` occurs anywhere in the term tree of h. */
function _containsTag(h, tag) {
  const t = Store.tag(h);
  if (!t) return false;
  if (t === tag) return true;
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && Store.isTerm(c) && _containsTag(c, tag)) return true;
  }
  return false;
}

/** Recursive validation of timed forms (see desugarTimed). */
function _validateTimed(h, location, connTags) {
  const t = Store.tag(h);
  if (!t) return;
  if (_QEXPR_TAGS.has(t)) {
    throw new Error('arithmetic in grade position is only supported in ' +
      'after/before window arguments (E7.1): derive the value via !q-op goals instead');
  }
  // Kernel-reserved draw tokens (THY_0027 §1, TODO_0298): `drawn c s` is
  // the trace hypothesis of the ∃_ρ judgment — minted only by the @draw
  // checker at the verification boundary. No program rule may mention it
  // (producing one would forge trace mass; matching one would read the
  // trace) — the at/fire discipline, applied to the token family.
  if (t === DECIMATE_PREDS.DRAWN) {
    throw new Error("'drawn' tokens are kernel-reserved (THY_0027): they are minted by the @draw checker at the verification boundary — a program rule may neither produce nor match them");
  }
  if (location === 'consequent' || location === 'consequent-body') {
    if (t === 'after' || t === 'before') {
      throw new Error(`'${t}' windows are antecedent guards — not allowed in the consequent`);
    }
    if (t === 'readPreserved') {
      throw new Error("'read' marks antecedent patterns — not allowed in the consequent");
    }
    if (t === 'at') {
      throw new Error('explicit stamps in a rule consequent are not allowed: ' +
        'output stamps are a(m)+d, assigned by the scheduler (E2)');
    }
    // The top-level graded monad IS the consequent's delay wrapper; a NESTED
    // one would silently become a raw monad token in the state (round 13) —
    // the engine never applies the graded-μ fusion at runtime.
    if (connTags.computation && t === connTags.computation.tag) {
      if (location === 'consequent-body') {
        throw new Error("nested graded monad in a rule consequent: '{ {B}@d }@e' does not auto-fuse — write a single delay '{ B }@(d+e)' (graded-μ, THY-A)");
      }
      location = 'consequent-body';
    }
  }
  if (t === connTags.exponential) {
    const grade = Store.child(h, 0);
    const inner = Store.child(h, 1);
    const gt = Store.tag(grade);
    if (gt === 'binlit' || gt === 'metavar' || gt === 'freevar') {
      // Counted parcel `!_k A` / `!_W A` (D4): LINEAR — stamps are allowed
      // (`!_2 wood@4` is a cohort of 2 at stamp 4). D15 does not apply.
    } else {
      // D15 is transitive: a persistent fact is timeless KNOWLEDGE — no stamp
      // may appear ANYWHERE under !, not just as the direct child
      // (audit round 12: `!(A@t * B)` bypassed the direct check).
      if (_containsTag(inner, 'at')) {
        throw new Error('stamped persistents are not allowed: no A@t under ! (D15)');
      }
    }
    if (Store.tag(inner) === 'readPreserved') {
      throw new Error('! read P is meaningless: persistent facts are never consumed');
    }
  }
  if (t === 'readPreserved') {
    const inner = Store.tag(Store.child(h, 0));
    if (inner === connTags.exponential) {
      throw new Error('read !P is meaningless: persistent facts are never consumed');
    }
    if (inner === connTags.preserved) {
      throw new Error('read $P is contradictory: read never consumes, $ consumes and re-produces');
    }
  }
  if (t === 'atom' || t === 'freevar' || t === 'metavar' ||
      t === 'binlit' || t === 'ratlit' || t === 'bound' || t === 'strlit') return;
  // An implication in a consequent is a POSSESSED RULE (timed dynamic
  // rules, Phase 6c): its body is a fresh rule scope — the left side an
  // antecedent (windows/stamps legal), the right side its own consequent
  // (one delay monad of its own) — NOT part of this rule's computation.
  if (t === connTags.implication &&
      (location === 'consequent' || location === 'consequent-body')) {
    _validateTimed(Store.child(h, 0), 'antecedent', connTags);
    _validateTimed(Store.child(h, 1), 'consequent', connTags);
    return;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && Store.isTerm(c)) _validateTimed(c, location, connTags);
  }
}

/** Throw if any preserved() wrapper remains in a hash tree. */
function _assertNoPreserved(h, location, presTag = 'preserved') {
  const t = Store.tag(h);
  if (!t) return;
  if (t === presTag) {
    throw new Error(location === 'antecedent'
      ? '$ (preserved) can only appear on top-level antecedent resources, not inside ! or other connectives'
      : '$ (preserved) can only be used on antecedent resources, not in the consequent');
  }
  if (t === 'atom' || t === 'freevar' || t === 'metavar' ||
      t === 'binlit' || t === 'bound' || t === 'strlit') return;
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && Store.isTerm(c)) _assertNoPreserved(c, location, presTag);
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
 * Classify an instance signature against the principal bounded-variable
 * signature: variable positions must carry ONE uniform sort (the instance
 * sort), fixed positions must match exactly.
 * @param {string} name - predicate name (for errors)
 * @param {number} instHash - instance signature hash
 * @param {number} prinHash - principal (bounded-var) signature hash
 * @param {{name: string}} svar - the sort variable binder
 * @returns {string} the instance sort
 */
function _instanceSortOf(name, instHash, prinHash, svar) {
  const inst = _parseSignature(instHash);
  const prin = _parseSignature(prinHash);
  if (!inst || !prin || inst.argSorts.length !== prin.argSorts.length) {
    throw new Error(`Duplicate definition '${name}': an instance signature must have the shape of the bounded-variable signature`);
  }
  let s = null;
  const pairs = prin.argSorts.map((p, i) => [p, inst.argSorts[i]]);
  pairs.push([prin.returnSort, inst.returnSort]);
  for (const [p, x] of pairs) {
    if (p === svar.name) {
      if (s === null) s = x;
      else if (s !== x) {
        throw new Error(`'${name}': instance signature mixes sorts at the variable positions ('${s}' vs '${x}')`);
      }
    } else if (p !== x) {
      throw new Error(`'${name}': instance signature disagrees with the principal signature at a fixed position ('${x}' where '${p}' is declared)`);
    }
  }
  if (s === null) {
    throw new Error(`'${name}': instance signature never instantiates the sort variable '${svar.name}'`);
  }
  return s;
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
  const onPhase = opts.onPhase || null;
  const _pEmit = (name, ms, meta) => { if (onPhase) onPhase(name, ms, meta); };

  const _tRead = onPhase ? performance.now() : 0;
  let source = fs.readFileSync(filePath, 'utf8');
  const _rootBytes = source.length;
  if (onPhase) _pEmit('load/parse/readfile', performance.now() - _tRead, {
    bytes: _rootBytes,
    file: path.basename(filePath),
  });

  // Resolve #import(path) directives
  const _tImports = onPhase ? performance.now() : 0;
  const imported = opts.alreadyImported || new Set();
  const _beforeImport = imported.size;
  source = resolveImports(source, filePath, imported);
  const _afterImport = imported.size;
  if (onPhase) _pEmit('load/parse/imports', performance.now() - _tImports, {
    resolved: _afterImport - _beforeImport,
    finalBytes: source.length,
    expansionRatio: _rootBytes > 0 ? source.length / _rootBytes : 1,
  });

  const _lc = opts.loaderConfig || DEFAULT_LOADER_CONFIG;
  const _ct = _lc.connTags;

  const _tParserInit = onPhase ? performance.now() : 0;
  const _parserWasBuilt = _lc.buildParser ? !!_lc._parser : _exprParser !== null;
  const _parser = _getExprParser(_lc);
  if (onPhase) _pEmit('load/parse/parser-init', performance.now() - _tParserInit, {
    cacheHit: _parserWasBuilt,
  });

  const _tParseDecls = onPhase ? performance.now() : 0;
  // memberPriors: the ONE program-file annotation (`name: sort @w Q.`,
  // TODO_0292 D5/M6) — regex-narrow in declarations.js, so rule bodies
  // (where @ is the stamp position) can never match. Previously such a
  // body was a parse error, so enabling it globally only accepts more.
  const decls = parseDecls(source, _parser, { memberPriors: true });
  if (onPhase) _pEmit('load/parse/parse-decls', performance.now() - _tParseDecls, {
    decls: decls.length,
    sourceBytes: source.length,
  });
  const argNamesTable = opts.argNamesTable || new Map();

  const _tProcess = onPhase ? performance.now() : 0;
  let _cDefs = 0, _cQueries = 0, _cForward = 0, _cClauses = 0, _cGrade0 = 0, _cDirectives = 0;

  // ── Pass 1: definitions (no premises, no monad) ──
  for (const decl of decls) {
    if (decl.type === 'query') continue; // queries resolved in pass 2
    // Subsort declaration `A <: B.` (TODO_0011 rung 1): sugar for a
    // persistent sedge fact — the checker's DAG is an index over these.
    if (decl.type === 'subsort') {
      // `/` separator: collision-free for underscore-named sorts (see the
      // matching subsort-closure key in engine/index.js).
      const cname = `${SORT_PREDS.EDGE}/${decl.sub}/${decl.sup}`;
      if (!clauses.has(cname)) {
        clauses.set(cname, {
          hash: Store.put(SORT_PREDS.EDGE,
            [Store.put('atom', [decl.sub]), Store.put('atom', [decl.sup])]),
          premises: [],
        });
      }
      continue;
    }
    if (decl.type !== 'declaration') continue;
    const { name, bodyHash, premises } = decl;
    if (!bodyHash) continue;

    // Constructor prior `name: sort @w Q.` (TODO_0292 D5/M6): recorded
    // beside the tables — the member declaration itself proceeds
    // unchanged. Validation (member-of-classifier, Chi–Geman) runs at
    // build time (engine/priors.js).
    if (decl.annotations && decl.annotations.length && opts.priorsTable) {
      const w = decl.annotations.find((a) => a.key === 'w' && a.value.type === 'RatValue');
      if (w) opts.priorsTable.set(name, [w.value.n, w.value.d]);
    }

    // Only process definitions in pass 1 (skip forward rules, clauses, and grade-0 facts)
    if (hasMonad(bodyHash, _ct.computation.tag) || premises.length > 0) continue;
    if (Store.tag(bodyHash) === _ct.exponential && Store.child(bodyHash, 0) === _lc.grade0()) continue;

    // Bounded sort variables `f: (s <: q) sig.` — recorded beside the
    // signature (like argNamesTable); classifier binders are pass-2 rules.
    let sortVarEntry = null;
    if (decl.binders) {
      if (decl.binders.some(b => b.rel === ':')) continue; // rule schema, pass 2
      sortVarEntry = { vars: decl.binders, instSorts: [] };
    }

    // Strip named_arg sentinels from arrow chain
    const { cleanHash, argNames } = stripNamedArgsFromArrowChain(bodyHash);

    if (definitions.has(name)) {
      // Instance signatures (TODO_0011 §instances): a bounded-sort-variable
      // declaration and instance signatures of the SAME name coexist — the
      // bounded-var signature is PRINCIPAL, concrete ones are declared
      // instances (bin.ill's `plus: bin bin bin` under rat.ill's
      // `plus: (s <: q) s s s`). Any other duplicate stays an error.
      if (sortVarEntry) {
        sortVarEntry.instSorts.push(
          _instanceSortOf(name, definitions.get(name), cleanHash, sortVarEntry.vars[0]));
        definitions.set(name, cleanHash); // promote to principal
        if (argNames.length > 0) argNamesTable.set(name, argNames);
        if (opts.sortVarsTable) opts.sortVarsTable.set(name, sortVarEntry);
        _cDefs++;
        continue;
      }
      if (opts.sortVarsTable && opts.sortVarsTable.has(name)) {
        const entry = opts.sortVarsTable.get(name);
        entry.instSorts.push(
          _instanceSortOf(name, cleanHash, definitions.get(name), entry.vars[0]));
        continue;
      }
      throw new Error(`Duplicate definition '${name}' (already defined)`);
    }

    if (argNames.length > 0) {
      argNamesTable.set(name, argNames);
    }
    if (sortVarEntry && opts.sortVarsTable) opts.sortVarsTable.set(name, sortVarEntry);
    definitions.set(name, cleanHash);
    _cDefs++;
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
        _cQueries++;
      }
      continue;
    }
    // T12: Collect @module directives
    if (decl.type === 'directive' && decl.key === 'module' && opts.moduleDecls) {
      opts.moduleDecls.push(decl.args);
      _cDirectives++;
      continue;
    }
    if (decl.type !== 'declaration') continue;
    const { name, bodyHash, premises } = decl;
    if (!bodyHash) continue;

    // Shared conversion tail: named-arg resolution → $-desugar → timed
    // desugar → rule/clause registration. Used by the plain path and by
    // classifier schema expansion (one pipeline, no drift).
    const convertOne = (cName, cBodyHash, cPremises) => {
      let cleanBodyHash = resolveNamedArgSentinels(cBodyHash, argNamesTable);
      cleanBodyHash = desugarPreserved(cleanBodyHash, _ct.computation, _ct, _lc.timed);
      if (_lc.timed) cleanBodyHash = desugarTimed(cleanBodyHash, _ct, _lc.qexprPreds || null);
      const cleanPremises = cPremises.map(p => resolveNamedArgSentinels(p, argNamesTable));

      if (hasMonad(cleanBodyHash, _ct.computation.tag)) {
        // Forward rule
        if (forwardRules.some(r => r.name === cName)) {
          throw new Error(`Duplicate forward rule '${cName}' (already defined)`);
        }
        forwardRules.push({
          name: cName,
          hash: cleanBodyHash,
          antecedent: extractAntecedent(cleanBodyHash, _ct.implication),
          consequent: extractConsequent(cleanBodyHash, _ct.implication)
        });
        _cForward++;
      } else {
        // Backward chaining clause
        if (clauses.has(cName)) {
          throw new Error(`Duplicate clause '${cName}' (already defined)`);
        }
        // Grade-0 clause: !_0 body. → unwrap bang, flag for compile-time specialization.
        // Clause stays in map for backward chaining (FFI principle: clauses are semantics).
        const isGrade0 = Store.tag(cleanBodyHash) === _ct.exponential &&
                          Store.child(cleanBodyHash, 0) === _lc.grade0();
        const clauseHash = isGrade0 ? Store.child(cleanBodyHash, 1) : cleanBodyHash;
        const clause = { hash: clauseHash, premises: cleanPremises };
        if (isGrade0) { clause.grade0 = true; _cGrade0++; }
        clauses.set(cName, clause);
        _cClauses++;
      }
    };

    // Classifier-quantified rule schema (TODO_0011 rung 1): `(r: C) BODY.`
    // expands at load into one ground rule per declared member of C —
    // finite closed world, elaboration in the $-desugaring slot.
    if (decl.binders) {
      const classBinders = decl.binders.filter(b => b.rel === ':');
      if (classBinders.length > 0) {
        if (classBinders.length !== decl.binders.length) {
          throw new Error(`'${name}': mixing sort-variable and classifier binders is not supported (rung 1)`);
        }
        if (premises.length > 0 || !hasMonad(bodyHash, _ct.computation.tag)) {
          throw new Error(`'${name}': classifier binders are only supported on forward rules (rung 1)`);
        }
        const memberLists = decl.binders.map(b => {
          if (definitions.has(b.name)) {
            throw new Error(`'${name}': binder '${b.name}' shadows a declared symbol — rename the binder`);
          }
          if (definitions.get(b.sort) !== Store.put('atom', [SORT_PREDS.SORT])) {
            throw new Error(`'${name}': cannot quantify over '${b.sort}' — not a classifier. Only finite declared classes expand ('${b.sort}: ${SORT_PREDS.SORT}.' + member declarations)`);
          }
          const classAtom = Store.put('atom', [b.sort]);
          const members = [];
          for (const [n, h] of definitions) if (h === classAtom) members.push(n);
          // Rung 2: constructor members (`cons: (a: lst) -> lst.`) make
          // the member set an infinite term language — enumerating only
          // the atomic members would be silently partial, so the schema
          // is a load error (waves collapse such sorts lazily instead).
          for (const [n, h] of definitions) {
            if (h === classAtom) continue;
            const sig = _parseSignature(h);
            if (sig && sig.returnSort === b.sort && sig.argSorts.length > 0) {
              throw new Error(`'${name}': cannot schema-expand over '${b.sort}' — constructor member '${n}' makes it a structured (possibly infinite) sort; only atomic-member classifiers expand`);
            }
          }
          if (members.length === 0) {
            throw new Error(`'${name}': classifier '${b.sort}' has no members — the schema would expand to nothing`);
          }
          return members;
        });
        const combos = memberLists.reduce(
          (acc, list) => acc.flatMap(c => list.map(m => [...c, m])), [[]]);
        for (const combo of combos) {
          const subs = new Map();
          combo.forEach((m, i) => {
            const rep = Store.put('atom', [m]);
            for (const tag of ['atom', 'metavar', 'freevar']) {
              subs.set(Store.put(tag, [decl.binders[i].name]), rep);
            }
          });
          convertOne(`${name}/${combo.join('/')}`, subHashes(bodyHash, subs, Store), []);
        }
        continue;
      }
      // Pure sort-variable binders: signatures only (recorded in pass 1)
      if (hasMonad(bodyHash, _ct.computation.tag) || premises.length > 0) {
        throw new Error(`'${name}': bounded sort variables are only supported on signatures (rung 1)`);
      }
      continue; // signature — already in definitions
    }

    // Skip definitions (handled in pass 1) — but NOT grade-0 clauses (!_0 body.)
    if (!hasMonad(bodyHash, _ct.computation.tag) && premises.length === 0) {
      if (!(Store.tag(bodyHash) === _ct.exponential && Store.child(bodyHash, 0) === _lc.grade0())) continue;
    }

    convertOne(name, bodyHash, premises);
  }

  if (onPhase) _pEmit('load/parse/process-decls', performance.now() - _tProcess, {
    definitions: _cDefs,
    queries: _cQueries,
    forwardRules: _cForward,
    clauses: _cClauses,
    grade0Clauses: _cGrade0,
    directives: _cDirectives,
    totalDecls: decls.length,
  });
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
function load(filePaths, loadOpts = {}) {
  const onPhase = loadOpts.onPhase || null;
  const definitions = new Map();
  const clauses = new Map();
  const forwardRules = [];
  const queries = new Map();
  const argNamesTable = new Map();
  const sortVarsTable = new Map();
  const querySettings = new Map();
  const splitQueries = new Map();
  const moduleDecls = [];
  const priorsTable = new Map();

  const alreadyImported = new Set();
  const paths = Array.isArray(filePaths) ? filePaths : [filePaths];
  for (const p of paths) {
    loadFile(p, definitions, clauses, forwardRules, queries, {
      argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls, alreadyImported, onPhase,
      priorsTable,
      loaderConfig: loadOpts.loaderConfig,
    });
  }

  // T3: Source label discovery — use import tree to map declarations to source files.
  // Uses lightweight regex scan (not full parse) to avoid parse failures on
  // files that depend on imported types. Only needs to find declaration names.
  const _tTree = onPhase ? performance.now() : 0;
  const tree = buildImportTree(paths[0]);
  if (onPhase) {
    const treeBytes = tree.reduce((n, node) => n + (node.source ? node.source.length : 0), 0);
    onPhase('load/parse/import-tree', performance.now() - _tTree, {
      nodes: tree.length,
      totalBytes: treeBytes,
    });
  }

  const _tLabels = onPhase ? performance.now() : 0;
  const nameToLabel = new Map();
  for (const node of tree) {
    const label = path.basename(node.path, path.extname(node.path));
    _scanDeclNames(node.source, label, nameToLabel);
  }

  // Tag forward rules and clauses with source labels
  const rootLabel = path.basename(paths[0], path.extname(paths[0]));
  for (const r of forwardRules) r.sourceLabel = nameToLabel.get(r.name) || rootLabel;
  for (const [name, c] of clauses) c.sourceLabel = nameToLabel.get(name) || rootLabel;
  if (onPhase) {
    const uniqueLabels = new Set(nameToLabel.values());
    onPhase('load/parse/label-discovery', performance.now() - _tLabels, {
      names: nameToLabel.size,
      labels: uniqueLabels.size,
      taggedRules: forwardRules.length,
      taggedClauses: clauses.size,
    });
  }

  return { definitions, clauses, forwardRules, queries, argNamesTable,
    sortVarsTable, querySettings, splitQueries, moduleDecls, priorsTable, importTree: tree };
}

// ─── Quantifier elimination for queries ─────────────────────────────────────

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

  // Build replacement for each binder and substitute via debruijnSubst.
  // De Bruijn: outermost binder has index (depth-1), innermost has index 0.
  // debruijnSubst is depth-aware — correctly skips bound vars under nested
  // quantifiers that _substituteBound's flat map lookup would corrupt (B9).
  const existsVars = new Set();
  const totalDepth = binders.length;
  const replacements = new Array(totalDepth);

  for (let i = 0; i < totalDepth; i++) {
    if (binders[i].kind === 'forall') {
      replacements[i] = Store.put('freevar', [`_q${i}`]);
    } else {
      replacements[i] = Store.put('metavar', [`_q${i}`]);
      existsVars.add(replacements[i]);
    }
  }

  // Phase 2: Substitute each binder's de Bruijn index with its replacement.
  // Order is outermost-first (highest index first) — independent since each
  // targets a distinct index, and debruijnSubst preserves other indices.
  for (let i = 0; i < totalDepth; i++) {
    const dbIndex = BigInt(totalDepth - 1 - i);
    body = debruijnSubst(body, dbIndex, replacements[i]);
  }

  // Phase 3: Decompose tensor into linear/persistent
  const linear = {}, persistent = {};
  function walk(h) {
    const t = Store.tag(h);
    if (t === 'one') {
      // Multiplicative unit: the empty multiset (`=> I .` expects nothing).
    } else if (t === 'tensor') {
      walk(Store.child(h, 0));
      walk(Store.child(h, 1));
    } else if (t === 'bang') {
      const grade = Store.child(h, 0);
      const inner = Store.child(h, 1);
      if (grade === grade0()) {
        throw new Error(
          'Grade-0 resources (!_0) cannot appear in queries or initial states — ' +
          'they are compile-time only (THY_0015 §2.1).'
        );
      }
      const gt = Store.tag(grade);
      if (gt === 'binlit') {
        // Counted parcel `!_k A` (D4): k copies of A in the multiset.
        const k = Store.child(grade, 0);
        if (k > 0xffffffn) throw new Error(`count grade ${k} too large for a state`);
        linear[inner] = (linear[inner] || 0) + Number(k);
      } else if (gt === 'ratlit') {
        throw new Error('fractional count grades (ℚ parcels) are post-v1 (D4)');
      } else if (gt === 'metavar' || gt === 'freevar') {
        throw new Error('count-variable grades (!_W) are rule patterns — not allowed in queries or states');
      } else {
        persistent[inner] = true;
      }
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
  return _getExprParser()(source);
}

export { load, loadFile, parseExpr, hasMonad, decomposeQuery, desugarPreserved, desugarTimed, buildImportTree, computeTreeHashes, extractTopLevelImports, stripNamedArgsFromArrowChain, resolveNamedArgSentinels, DEFAULT_LOADER_CONFIG };
export default { load, loadFile, parseExpr, hasMonad, decomposeQuery, desugarPreserved, desugarTimed, buildImportTree, computeTreeHashes, extractTopLevelImports, stripNamedArgsFromArrowChain, resolveNamedArgSentinels, DEFAULT_LOADER_CONFIG };
