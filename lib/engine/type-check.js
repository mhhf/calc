/**
 * Sort Checking for CALC — load-time verification of arity/sort consistency.
 *
 * Builds a sort table from LF-style type declarations (arrow signatures),
 * then checks forward rules and backward clauses against it.
 * Zero runtime cost — all work happens at _buildCalc() time.
 *
 * Design: SortEntry = { argSorts: string[], returnSort: string }
 * Extension path: Stage 3 (full dependent type checking) can refine
 * argSorts from strings to full type hashes.
 */

const Store = require('../kernel/store');

// ─── Sort Table Construction ─────────────────────────────────────────────────

/**
 * Extract sort name from a hash.
 * tag='type' → 'type', tag='atom' → atom name, else null.
 */
function _extractSortName(h) {
  const t = Store.tag(h);
  if (t === 'type') return 'type';
  if (t === 'atom') return Store.child(h, 0);
  return null;
}

/**
 * Parse an arrow-chain hash into a sort signature.
 * arrow(atom('bin'), arrow(atom('bin'), type())) → { argSorts: ['bin','bin'], returnSort: 'type' }
 * Returns null for non-signature hashes (axioms, predicate applications).
 */
function _parseSignature(h) {
  const argSorts = [];
  let current = h;
  while (Store.tag(current) === 'arrow') {
    const left = Store.child(current, 0);
    const sortName = _extractSortName(left);
    if (sortName === null) return null;
    argSorts.push(sortName);
    current = Store.child(current, 1);
  }
  const returnSort = _extractSortName(current);
  if (returnSort === null) return null;
  return { argSorts, returnSort };
}

/**
 * Build sort table from definitions Map.
 * Iterates definitions, parses arrow signatures, skips axioms.
 * @param {Map<string, number>} definitions - name → hash from convert.load()
 * @returns {Map<string, {argSorts: string[], returnSort: string}>}
 */
function buildSortTable(definitions) {
  const table = new Map();
  for (const [name, hash] of definitions) {
    const sig = _parseSignature(hash);
    if (sig) table.set(name, sig);
  }
  return table;
}

// ─── Term Checking ───────────────────────────────────────────────────────────

/**
 * Infer the sort of a term hash.
 * @param {number} h - term hash
 * @param {Map} sortTable
 * @param {Map} metavarSorts - freevar hash → sort
 * @returns {string} sort name or '_' (unknown)
 */
function inferSort(h, sortTable, metavarSorts) {
  const t = Store.tag(h);
  if (!t) return '_';

  if (t === 'freevar' || t === 'metavar') {
    const s = metavarSorts.get(h);
    return s || '_';
  }
  if (t === 'binlit') return 'bin';
  if (t === 'atom') {
    const name = Store.child(h, 0);
    const entry = sortTable.get(name);
    return entry ? entry.returnSort : '_';
  }

  const tid = Store.tagId(h);
  if (tid >= Store.PRED_BOUNDARY) {
    const predName = Store.TAG_NAMES[tid];
    const entry = sortTable.get(predName);
    return entry ? entry.returnSort : '_';
  }

  return '_'; // connective or unknown
}

/**
 * Check a term against an expected sort. Recurses into children.
 * Collects errors into `errors` array; does not throw.
 *
 * @param {number} h - term hash
 * @param {string} expectedSort - expected sort ('_' = unconstrained)
 * @param {Map} sortTable
 * @param {Map} metavarSorts - freevar hash → recorded sort (mutated)
 * @param {Array} errors - collected error strings (mutated)
 * @param {string} path - context for error messages (e.g. "rule 'evm/add'")
 */
function _checkTerm(h, expectedSort, sortTable, metavarSorts, errors, path) {
  const t = Store.tag(h);
  if (!t) return;

  const tid = Store.tagId(h);

  // Freevar/metavar: record or check sort consistency
  if (t === 'freevar' || t === 'metavar') {
    if (expectedSort === '_') return;
    const existing = metavarSorts.get(h);
    if (existing === undefined) {
      metavarSorts.set(h, expectedSort);
    } else if (existing !== '_' && existing !== expectedSort) {
      const name = Store.child(h, 0);
      errors.push(`${path}: metavar ${name} used as '${existing}' and '${expectedSort}'`);
    }
    return;
  }

  // Binary literal: sort is always 'bin'
  if (t === 'binlit') {
    if (expectedSort !== '_' && expectedSort !== 'bin') {
      errors.push(`${path}: expected sort '${expectedSort}', got 'bin' (binary literal)`);
    }
    return;
  }

  // Atom (nullary constructor)
  if (t === 'atom') {
    const name = Store.child(h, 0);
    const entry = sortTable.get(name);
    if (!entry) return; // not in sort table, skip
    if (entry.argSorts.length !== 0) {
      errors.push(`${path}: '${name}' expects ${entry.argSorts.length} args, got 0`);
      return;
    }
    if (expectedSort !== '_' && entry.returnSort !== expectedSort) {
      errors.push(`${path}: expected sort '${expectedSort}', got '${entry.returnSort}' for '${name}'`);
    }
    return;
  }

  // Connective / structural tag (< PRED_BOUNDARY, not atom/freevar/binlit)
  if (tid < Store.PRED_BOUNDARY) {
    const a = Store.arity(h);
    for (let i = 0; i < a; i++) {
      const ch = Store.child(h, i);
      if (typeof ch === 'number' && Store.isTerm(ch)) {
        _checkTerm(ch, '_', sortTable, metavarSorts, errors, path);
      }
    }
    return;
  }

  // Predicate tag (>= PRED_BOUNDARY)
  const predName = Store.TAG_NAMES[tid];
  const entry = sortTable.get(predName);
  if (!entry) return; // not in sort table, skip

  const a = Store.arity(h);
  if (a !== entry.argSorts.length) {
    errors.push(`${path}: '${predName}' expects ${entry.argSorts.length} args, got ${a}`);
    return;
  }

  if (expectedSort !== '_' && entry.returnSort !== expectedSort) {
    errors.push(`${path}: expected sort '${expectedSort}', got '${entry.returnSort}' for '${predName}'`);
  }

  for (let i = 0; i < a; i++) {
    const ch = Store.child(h, i);
    if (typeof ch === 'number' && Store.isTerm(ch)) {
      _checkTerm(ch, entry.argSorts[i], sortTable, metavarSorts, errors, path);
    }
  }
}

// ─── Rule & Clause Checking ─────────────────────────────────────────────────

/**
 * Check a compiled forward rule against the sort table.
 * @param {Object} rule - compiled rule from compile.js
 * @param {Map} sortTable
 * @returns {string[]} error messages (empty = OK)
 */
function checkForwardRule(rule, sortTable) {
  const errors = [];
  const metavarSorts = new Map();
  const path = `rule '${rule.name}'`;

  for (const h of (rule.antecedent.linear || []))
    _checkTerm(h, 'type', sortTable, metavarSorts, errors, path);
  for (const h of (rule.antecedent.persistent || []))
    _checkTerm(h, 'type', sortTable, metavarSorts, errors, path);
  for (const h of (rule.consequent.linear || []))
    _checkTerm(h, 'type', sortTable, metavarSorts, errors, path);
  for (const h of (rule.consequent.persistent || []))
    _checkTerm(h, 'type', sortTable, metavarSorts, errors, path);

  // Also check alternative consequents (oplus branches)
  if (rule.consequentAlts) {
    for (const alt of rule.consequentAlts.slice(1)) {
      for (const h of (alt.linear || []))
        _checkTerm(h, 'type', sortTable, metavarSorts, errors, path);
      for (const h of (alt.persistent || []))
        _checkTerm(h, 'type', sortTable, metavarSorts, errors, path);
    }
  }

  return errors;
}

/**
 * Check a backward clause against the sort table.
 * @param {string} name - clause name
 * @param {Object} clause - { hash, premises }
 * @param {Map} sortTable
 * @returns {string[]} error messages (empty = OK)
 */
function checkClause(name, clause, sortTable) {
  const errors = [];
  const metavarSorts = new Map();
  const path = `clause '${name}'`;

  _checkTerm(clause.hash, 'type', sortTable, metavarSorts, errors, path);
  for (const p of clause.premises)
    _checkTerm(p, 'type', sortTable, metavarSorts, errors, path);

  return errors;
}

// ─── Top-Level Orchestrator ──────────────────────────────────────────────────

/**
 * Check all declarations, forward rules, and clauses.
 * @param {Map} definitions - name → hash
 * @param {Object[]} compiledRules - compiled forward rules
 * @param {Map} clauses - name → { hash, premises }
 * @param {Object} [opts]
 * @param {boolean} [opts.strict] - throw on errors
 * @returns {{ errors: string[], warnings: string[] }}
 */
function checkAll(definitions, compiledRules, clauses, opts = {}) {
  const sortTable = buildSortTable(definitions);
  const errors = [];
  const warnings = [];

  for (const rule of compiledRules) {
    errors.push(...checkForwardRule(rule, sortTable));
  }

  for (const [name, clause] of clauses) {
    errors.push(...checkClause(name, clause, sortTable));
  }

  if (opts.strict && errors.length > 0) {
    throw new Error(`Sort checking failed (${errors.length} error(s)):\n  ${errors.join('\n  ')}`);
  }

  return { errors, warnings };
}

module.exports = {
  _extractSortName,
  _parseSignature,
  buildSortTable,
  inferSort,
  _checkTerm,
  checkForwardRule,
  checkClause,
  checkAll,
};
