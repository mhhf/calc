/**
 * Shared directive loading for ILL-native tools.
 *
 * File discovery, directive scanning, program loading with overlay.
 * Used by both test-ill.js (judgments) and debug-ill.js (observations).
 */

const path = require('path');
const fs = require('fs');
const mde = require('./index');
const convert = require('./convert');
const Store = require('../kernel/store');
const { toObject } = require('../engine/fact-set');
const { getAllLeaves } = require('../engine/tree-utils');
const { showInteresting, classifyLeaf, show } = require('../engine/show');
const { getPredicateHead } = require('../kernel/ast');

const ROOT = path.join(__dirname, '..', '..');

// ─── File Discovery ─────────────────────────────────────────────────────────

function findIllFiles(dir) {
  if (!fs.existsSync(dir)) return [];
  const results = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) results.push(...findIllFiles(full));
    else if (entry.name.endsWith('.ill')) results.push(full);
  }
  return results.sort();
}

// ─── Directive Scanning ─────────────────────────────────────────────────────

/**
 * Pre-scan files for directive names matching a regex pattern.
 * @param {string[]} files - absolute paths to .ill files
 * @param {RegExp} re - pattern to match (must have one capture group)
 * @returns {Map<string, Set<string>>} file → Set<directiveName>
 */
function scanDirectives(files, re) {
  const fileDirectives = new Map();
  for (const file of files) {
    const src = fs.readFileSync(file, 'utf8');
    const names = new Set();
    for (const m of src.matchAll(re)) names.add(m[1]);
    if (names.size > 0) fileDirectives.set(file, names);
  }
  return fileDirectives;
}

/**
 * Detect duplicate directive names across files.
 * Throws on collision (splitQueries is a flat Map — last writer wins).
 */
function detectDuplicates(fileDirectives) {
  const nameToFile = new Map();
  for (const [file, names] of fileDirectives) {
    for (const name of names) {
      if (nameToFile.has(name)) {
        const prev = path.relative(ROOT, nameToFile.get(name));
        const curr = path.relative(ROOT, file);
        throw new Error(`Duplicate directive '${name}' in ${prev} and ${curr}`);
      }
      nameToFile.set(name, file);
    }
  }
}

// ─── Program Loading ────────────────────────────────────────────────────────

/**
 * Load shared program with cache, then overlay test/debug files.
 * @param {string} programPath - path to main program (e.g. evm.ill)
 * @param {Map<string, Set<string>>} fileDirectives - files to overlay
 * @returns {Object} calc context
 */
function loadProgram(programPath, fileDirectives) {
  const calc = mde.load(programPath, { cache: true });
  const alreadyImported = new Set(convert.buildImportTree(programPath).map(n => n.path));
  for (const file of fileDirectives.keys()) {
    convert.loadFile(file, new Map(), new Map(), [], calc.queries, {
      argNamesTable: new Map(), querySettings: calc.querySettings,
      splitQueries: calc.splitQueries, moduleDecls: [], alreadyImported
    });
  }
  return calc;
}

// ─── Modality ───────────────────────────────────────────────────────────────

/** Extract modality from directive kind prefix. */
function parseModality(kind) {
  if (kind === 'expect_not' || kind.startsWith('expect_not_')) return 'not';
  if (kind === 'expect_some' || kind.startsWith('expect_some_')) return 'some';
  if (kind.startsWith('expect')) return 'all';
  return null;
}

// ─── Freevar Detection ──────────────────────────────────────────────────────

/** Recursively check if a content-addressed hash contains freevar nodes. */
function hasFreevar(h) {
  const t = Store.tag(h);
  if (!t) return false;
  if (t === 'freevar') return true;
  if (t === 'charlit') return false;
  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (elems) for (let i = 0; i < elems.length; i++)
      if (hasFreevar(elems[i])) return true;
    return false;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && hasFreevar(c)) return true;
  }
  return false;
}

/** Check if a decomposed state contains any freevars (from eigenvariables). */
function stateHasFreevars(state) {
  for (const h of Object.keys(state.linear))
    if (hasFreevar(+h)) return true;
  for (const h of Object.keys(state.persistent))
    if (hasFreevar(+h)) return true;
  return false;
}

// ─── Subset Matching ────────────────────────────────────────────────────────

/** Pattern ⊆ state: every fact in pattern exists (with sufficient count) in state. */
function isSubset(pattern, state) {
  for (const [h, cnt] of Object.entries(pattern.linear))
    if ((state.linear[h] || 0) < cnt) return false;
  for (const h of Object.keys(pattern.persistent))
    if (!state.persistent[h]) return false;
  return true;
}

// ─── Diagnostics ────────────────────────────────────────────────────────────

function formatState(state, label) {
  if (!state) return `${label}: NO_STATE`;
  const cls = classifyLeaf(state);
  const facts = showInteresting(state, { exclude: [] });
  return `${label} [${cls}]: ${facts.join(', ')}`;
}

/**
 * Group state facts by predicate head for structured display.
 * @param {Object} state - plain { linear: {hash:count}, persistent: {hash:true} }
 * @returns {Map<string, string[]>} predicate → [show(fact), ...]
 */
function groupByPredicate(state) {
  const groups = new Map();
  for (const h of Object.keys(state.linear)) {
    const hn = Number(h);
    const pred = getPredicateHead(hn) || 'unknown';
    if (!groups.has(pred)) groups.set(pred, []);
    const count = state.linear[h];
    const s = show(hn);
    for (let i = 0; i < count; i++) groups.get(pred).push(s);
  }
  for (const h of Object.keys(state.persistent)) {
    const hn = Number(h);
    const pred = '!' + (getPredicateHead(hn) || 'unknown');
    if (!groups.has(pred)) groups.set(pred, []);
    groups.get(pred).push(show(hn));
  }
  return groups;
}

module.exports = {
  ROOT,
  findIllFiles,
  scanDirectives,
  detectDuplicates,
  loadProgram,
  parseModality,
  hasFreevar,
  stateHasFreevars,
  isSubset,
  formatState,
  groupByPredicate,
  // Re-exports for convenience
  show,
  classifyLeaf,
  showInteresting,
  toObject,
  getAllLeaves,
};
