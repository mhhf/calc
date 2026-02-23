/**
 * Forward Chaining Engine — execution and main loop.
 *
 * Applies matches and runs the committed-choice main loop.
 * Matching is in match.js, strategy in strategy.js.
 *
 * State: { linear: { hash: count }, persistent: { hash: true } }
 *
 * Architecture:
 *   compile.js   — rule preparation (compileRule)
 *   match.js     — pattern matching + indexing + persistent proving
 *   strategy.js  — rule selection (fingerprint, disc-tree, predicate)
 *   forward.js   — execution + main loop (applyMatch, run)
 *   symexec.js   — exhaustive DFS exploration + mutation/undo
 */

const { applyIndexed: subApplyIdx, subCompiled } = require('../kernel/substitute');
const { compileRule, flattenTensor, unwrapMonad, expandItem, expandConsequentChoices } = require('./compile');
const { getPredicateHead } = require('../kernel/ast');
const match = require('./match');
const strategy = require('./strategy');

// ─── Apply Match ────────────────────────────────────────────────────

/** Apply match result: consume resources, produce new ones */
function applyMatch(state, { rule, theta, slots, consumed, optimized }) {
  const newLinear = { ...state.linear };
  for (const hStr in consumed) {
    const hash = Number(hStr);
    newLinear[hash] -= consumed[hStr];
    if (newLinear[hash] <= 0) delete newLinear[hash];
  }

  let skipCount = null;
  if (optimized && rule.preserved) {
    skipCount = {};
    for (const h of rule.preserved) {
      skipCount[h] = (skipCount[h] || 0) + 1;
    }
  }
  const skipUsed = {};

  const cLinear = rule.compiledConseqLinear;
  const linPats = rule.consequent.linear || [];
  for (let i = 0; i < linPats.length; i++) {
    const pattern = linPats[i];
    if (skipCount && skipCount[pattern] > 0 &&
        (skipUsed[pattern] || 0) < skipCount[pattern]) {
      skipUsed[pattern] = (skipUsed[pattern] || 0) + 1;
      continue;
    }
    const recipe = cLinear && cLinear[i];
    const h = recipe && recipe.compiled
      ? subCompiled(recipe, theta)
      : subApplyIdx(pattern, theta, slots);
    newLinear[h] = (newLinear[h] || 0) + 1;
  }

  const newPersistent = { ...state.persistent };
  const cPersistent = rule.compiledConseqPersistent;
  const persPats = rule.consequent.persistent || [];
  for (let i = 0; i < persPats.length; i++) {
    const recipe = cPersistent && cPersistent[i];
    const h = recipe && recipe.compiled
      ? subCompiled(recipe, theta)
      : subApplyIdx(persPats[i], theta, slots);
    newPersistent[h] = true;
  }

  return { linear: newLinear, persistent: newPersistent };
}

// ─── Main Loop ──────────────────────────────────────────────────────

/** Run forward chaining until quiescence */
function run(state, rules, opts = {}) {
  const maxSteps = opts.maxSteps || 1000;
  const trace = opts.trace ? [] : null;
  const calc = opts.calc || null;
  const useFingerprint = opts.useFingerprint !== undefined
    ? opts.useFingerprint
    : opts.useEvmStrategy !== false;  // backward-compatible alias
  const optimizePreserved = opts.optimizePreserved !== false;
  let steps = 0;

  const discriminatorIndex = useFingerprint ? match.buildDiscriminatorIndex(rules) : null;
  const fpConfig = match.detectFingerprintConfig(rules);
  const indexedRules = { rules, discriminatorIndex, fpConfig };
  const matchOpts = optimizePreserved ? { optimizePreserved: true } : undefined;

  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('./prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  while (steps < maxSteps) {
    let m = strategy.findMatch(state, indexedRules, calc, matchOpts);
    if (!m) {
      // Try to fire a loli continuation from state
      m = match.matchFirstLoli(state, calc);
      if (!m) return { state, quiescent: true, steps, trace };
    }
    if (trace) trace.push(`[${steps}] ${m.rule.name}`);
    state = applyMatch(state, m);
    steps++;
  }

  return { state, quiescent: false, steps, trace };
}

function createState(linear = {}, persistent = {}) {
  return { linear, persistent };
}

module.exports = {
  // Compilation (re-exported from compile.js)
  compileRule,
  flattenTensor,
  unwrapMonad,
  expandItem,
  expandConsequentChoices,
  // Execution
  applyMatch,
  run,
  createState,
  // Re-exports from match.js (backward compatibility)
  buildStateIndex: match.buildStateIndex,
  buildDiscriminatorIndex: match.buildDiscriminatorIndex,
  buildOpcodeIndex: match.buildDiscriminatorIndex,  // backward-compatible alias
  detectFingerprintConfig: match.detectFingerprintConfig,
  findFingerprintValue: match.findFingerprintValue,
  tryMatch: match.tryMatch,
  matchLoli: match.matchLoli,
  matchFirstLoli: match.matchFirstLoli,
  provePersistentGoals: match.provePersistentGoals,
  resolveExistentials: match.resolveExistentials,
  getProfile: match.getProfile,
  resetProfile: match.resetProfile,
  getTryMatchLog: match.getTryMatchLog,
  resetTryMatchLog: match.resetTryMatchLog,
  // Re-exports from strategy.js (backward compatibility)
  findMatch: strategy.findMatch,
  // Re-export from ast.js (backward compatibility)
  getPredicateHead,
};
