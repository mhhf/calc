/**
 * Forward Chaining Engine — execution and main loop.
 *
 * Applies matches and runs the committed-choice main loop.
 * Matching is in match.js, strategy in strategy.js.
 *
 * State: FactSet-based State object (lib/engine/fact-set.js).
 * Public API accepts/returns plain { linear: {hash:count}, persistent: {hash:true} }
 * objects for backward compatibility.
 *
 * Architecture:
 *   compile.js   — rule preparation (compileRule)
 *   match.js     — pattern matching + persistent proving
 *   strategy.js  — rule selection (fingerprint, disc-tree, predicate)
 *   forward.js   — execution + main loop (applyMatch, run)
 *   symexec.js   — exhaustive DFS exploration + mutation/undo
 */

const Store = require('../kernel/store');
const { applyIndexed: subApplyIdx, subCompiled } = require('../kernel/substitute');
const { compileRule, flattenTensor, unwrapMonad, expandChoiceItem, expandConsequentChoices } = require('./compile');
const match = require('./match');
const strategy = require('./strategy');
const { fromObject, toObject } = require('./fact-set');

// ─── Apply Match ────────────────────────────────────────────────────

/**
 * Apply match result: consume resources, produce new ones.
 * Clones state, mutates clone, returns clone.
 * State is a FactSet-based State object.
 */
function applyMatch(state, { rule, theta, slots, consumed, optimized }) {
  const newState = state.clone();

  // Consume
  for (const hStr in consumed) {
    const hash = Number(hStr);
    const count = consumed[hStr];
    const tagIdx = Store.tagId(hash);
    for (let c = 0; c < count; c++) {
      newState.linear.remove(tagIdx, hash, null);
    }
  }

  // Produce linear (with preserved-skip + compiled sub)
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
    newState.linear.insert(Store.tagId(h), h, null);
  }

  // Produce persistent
  const cPersistent = rule.compiledConseqPersistent;
  const persPats = rule.consequent.persistent || [];
  for (let i = 0; i < persPats.length; i++) {
    const recipe = cPersistent && cPersistent[i];
    const h = recipe && recipe.compiled
      ? subCompiled(recipe, theta)
      : subApplyIdx(persPats[i], theta, slots);
    const tagIdx = Store.tagId(h);
    if (!newState.persistent.has(tagIdx, h)) {
      newState.persistent.insert(tagIdx, h, null);
    }
  }

  return newState;
}

// ─── Main Loop ──────────────────────────────────────────────────────

/** Run forward chaining until quiescence */
function run(inputState, rules, opts = {}) {
  const maxSteps = opts.maxSteps || 1000;
  const trace = opts.trace ? [] : null;
  const calc = opts.calc || null;
  const useFingerprint = opts.useFingerprint !== false;
  const optimizePreserved = opts.optimizePreserved !== false;
  let steps = 0;

  // Accept both plain objects and State objects
  let state = inputState.linear && inputState.linear.group
    ? inputState  // Already a State object
    : fromObject(inputState.linear || {}, inputState.persistent || {});

  const discriminatorIndex = useFingerprint ? match.buildDiscriminatorIndex(rules) : null;
  const fpConfig = match.detectFingerprintConfig(rules);
  const indexedRules = { rules, discriminatorIndex, fpConfig };
  const matchOpts = optimizePreserved ? { optimizePreserved: true } : undefined;

  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('./prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  // Build fingerprint secondary index on initial state
  if (fpConfig) {
    state._fpPred = fpConfig.pred;
    state._fpKeyPos = fpConfig.keyPos;
    _buildByKey(state, fpConfig);
  }

  while (steps < maxSteps) {
    // Rebuild _byKey for new state (in case code facts changed)
    if (fpConfig && !state._byKey) {
      state._fpPred = fpConfig.pred;
      state._fpKeyPos = fpConfig.keyPos;
      _buildByKey(state, fpConfig);
    }

    let m = strategy.findMatch(state, indexedRules, calc, matchOpts);
    if (!m) {
      // Try to fire a loli continuation from state
      m = match.matchFirstLoli(state, calc);
      if (!m) return { state: toObject(state), quiescent: true, steps, trace };
    }
    if (trace) trace.push(`[${steps}] ${m.rule.name}`);
    state = applyMatch(state, m);
    steps++;
  }

  return { state: toObject(state), quiescent: false, steps, trace };
}

/** Build secondary fingerprint index on state */
function _buildByKey(state, fpConfig) {
  const fpTagId = Store.TAG[fpConfig.pred];
  state._byKey = {};
  if (fpTagId !== undefined) {
    const grp = state.linear.group(fpTagId);
    for (let i = 0; i < grp.length; i++) {
      const h = grp[i];
      if (Store.arity(h) > fpConfig.keyPos) {
        state._byKey[Store.child(h, fpConfig.keyPos)] = h;
      }
    }
  }
}

function createState(linear = {}, persistent = {}) {
  return fromObject(linear, persistent);
}

module.exports = {
  // Compilation (re-exported from compile.js)
  compileRule,
  flattenTensor,
  unwrapMonad,
  expandChoiceItem,
  expandConsequentChoices,
  // Execution
  applyMatch,
  run,
  createState,
};
