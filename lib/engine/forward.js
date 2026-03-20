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
 *   explore.js   — exhaustive DFS exploration + mutation/undo
 */

const Store = require('../kernel/store');
const { compileRule, flattenTensor, unwrapMonad, expandChoiceItem, expandConsequentChoices } = require('./compile');
const match = require('./match');
const strategy = require('./strategy');
const { fromObject, toObject } = require('./fact-set');
const { consumeLinear, produceLinear, producePersistent } = require('./state-ops');
const { EqNeqSolver } = require('./constraint');
const { filterAltsBySAT } = require('./opt/constraint');

// ─── Apply Match ────────────────────────────────────────────────────

/**
 * Apply match result: consume resources, produce new ones.
 * Mutates state in-place (committed-choice: no backtracking needed).
 * Caller must invalidate secondary indices (_byKey) after mutation.
 */
function applyMatchInPlace(state, { rule, theta, slots, consumed, optimized }) {
  consumeLinear(state.linear, consumed, null);
  produceLinear(state.linear, rule.consequent.linear || [], theta, slots, rule, optimized, null);
  producePersistent(state.persistent, rule.consequent.persistent || [], theta, slots, rule, null);
  // Invalidate secondary index (will be rebuilt next iteration if needed)
  state._byKey = null;
}

/**
 * Apply match result: consume resources, produce new ones.
 * Clone-based (legacy API). Used by callers that need the old state.
 */
function applyMatch(state, m) {
  const newState = state.clone();
  applyMatchInPlace(newState, m);
  return newState;
}

// ─── Main Loop ──────────────────────────────────────────────────────

/** Run forward chaining until quiescence */
function run(inputState, rules, opts = {}) {
  const maxSteps = opts.maxSteps || 1000;
  const trace = opts.trace ? [] : null;
  const terms = opts.terms || false;
  const evidence = opts.evidence || false;
  const calc = opts.calc || null;
  const engine = opts.engine || null;
  const useFingerprint = opts.useFingerprint !== false;
  const optimizePreserved = opts.optimizePreserved !== false;
  // Default: noFFI (adversarially sound). Opt-in to FFI for benchmarking only.
  const useFFI = opts.dangerouslyUseFFI || false;
  // Tabling soundness: the backward cache maps (pred, inputs) → outputs.
  // This is sound because persistent context is monotonically growing during
  // forward execution — cached successes remain valid. We clear at run start
  // because a new run may have a different initial persistent context, making
  // prior cached failures stale (a previously-unprovable goal may now succeed).
  match.clearBackwardCache();
  let steps = 0;
  let solver = null; // Lazy EqNeqSolver for multi-alt rules

  // Accept both plain objects and State objects
  let state = inputState.linear && inputState.linear.group
    ? inputState  // Already a State object
    : fromObject(inputState.linear || {}, inputState.persistent || {});

  const discriminatorIndex = useFingerprint ? match.buildDiscriminatorIndex(rules) : null;
  const fpConfig = match.detectFingerprintConfig(rules);
  const indexedRules = { rules, discriminatorIndex, fpConfig };
  // Compose provePersistent callback based on FFI mode
  const provePersistent = useFFI ? match.provePersistentGoals : match.provePersistentNaive;
  const matchOpts = {
    optimizePreserved: optimizePreserved || undefined,
    evidence: evidence || undefined,
    provePersistent,
    useCompiledSteps: useFFI,
  };

  if (calc && calc.clauses && calc.definitions && !calc.backchainIndex) {
    const backward = require('./prove');
    calc.backchainIndex = backward.buildIndex(calc.clauses, calc.definitions);
  }

  // Build fingerprint secondary index on initial state (skip for virtual — uses ARRAY_TABLE)
  if (fpConfig && fpConfig.type !== 'virtual') {
    state._fpPred = fpConfig.pred;
    state._fpKeyPos = fpConfig.keyPos;
    buildFingerprintIndex(state, fpConfig);
  }

  while (steps < maxSteps) {
    // Rebuild _byKey for new state (in case code facts changed)
    if (fpConfig && fpConfig.type !== 'virtual' && !state._byKey) {
      state._fpPred = fpConfig.pred;
      state._fpKeyPos = fpConfig.keyPos;
      buildFingerprintIndex(state, fpConfig);
    }

    let m = strategy.findMatch(state, indexedRules, calc, matchOpts);
    if (!m) {
      // Try to fire a loli continuation from state
      const loliTagId = Store.TAG[calc?.roles?.implication || 'loli'];
      const loliGroup = state.linear.group(loliTagId);
      for (let i = 0; i < loliGroup.length; i++) {
        m = match.matchLoli(loliGroup[i], state, calc, matchOpts);
        if (m) break;
      }
      if (!m) {
        return { state: toObject(state), quiescent: true, steps, trace };
      }
    }
    // Three trace levels, gated by flags to avoid allocation in the hot path:
    //   evidence=true (guided profile): full rule object, theta snapshot, slots,
    //     per-persistent-goal evidence, loliHash — everything buildGuidedTerm needs.
    //     theta.slice() is the ONLY allocation overhead in the hot loop — theta is
    //     a mutable array reused across matches, so we must snapshot it.
    //   terms=true (full profile with terms): rule name + consumed facts for
    //     buildMonadicTerm's opaque CLF let-chain.
    //   default: string trace for debugging ("[0] rule_name").
    // Multi-alt consequent: SAT-filter alternatives, pick the survivor.
    // Must happen BEFORE trace recording so trace.rule.consequent matches the
    // actual alt used for state transition.
    if (m.rule.consequentAlts && m.rule.consequentAlts.length > 1) {
      if (!solver) solver = new EqNeqSolver();
      const satAlts = filterAltsBySAT(solver, m.rule.consequentAlts, m.theta, m.slots);
      if (satAlts.length >= 1 && satAlts[0] !== 0) {
        const alt = m.rule.consequentAlts[satAlts[0]];
        // Null compiled-sub caches (indexed for alt[0]). Keep preserved/optimized intact.
        m = { ...m, rule: { ...m.rule, consequent: alt,
          compiledConseqLinear: null, compiledConseqPersistent: null } };
      }
    }
    if (trace) {
      if (evidence) {
        trace.push({
          rule: m.rule,
          consumed: { ...m.consumed },
          theta: m.theta.slice(),
          slots: m.slots,
          persistentEvidence: m.persistentEvidence || [],
          loliHash: m.loliHash || null
        });
      } else if (terms) {
        trace.push({ rule: m.rule.name, consumed: { ...m.consumed } });
      } else {
        trace.push(`[${steps}] ${m.rule.name}`);
      }
    }
    applyMatchInPlace(state, m);
    steps++;
  }

  return { state: toObject(state), quiescent: false, steps, trace };
}

/** Build secondary fingerprint index on state */
function buildFingerprintIndex(state, fpConfig) {
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
  buildFingerprintIndex,
};
