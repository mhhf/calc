/**
 * Execution Tree Exploration
 *
 * Explores all forward chaining executions up to a depth bound.
 * Returns a tree of all reachable states.
 *
 * Tree structure:
 *   { type: 'leaf', state }           - quiescent (no rules fire)
 *   { type: 'branch', state: null, children } - nondeterministic choice
 *   { type: 'bound', state }          - depth limit reached
 *   { type: 'cycle', state }          - back-edge detected
 *   { type: 'memo', state }           - already explored (global visited hit)
 *
 * Handles both rule-level nondeterminism (which rule fires) and
 * additive choice in consequents (A ⊕ B forks the tree).
 *
 * Uses FactSet-based State (lib/engine/fact-set.js) with Arena undo.
 * State IS the index — no separate stateIndex needed.
 */

const Store = require('../kernel/store');
const { resolveConn } = require('./formula-utils');
const { buildFingerprintIndex } = require('./forward');
const { tryMatch, EMPTY_MATCH_OPTS } = require('./match');
const { clearBWCache: lnlClearCache } = require('./backward-cache');
const { findAllMatches, detectStrategy } = require('./strategy');
const { EqNeqSolver } = require('./constraint');
const { fromObject, Arena } = require('./fact-set');
const { filterPres, mutateState } = require('./state-ops');
const { feedPers, satFilter } = require('./constraint-feed');


// --- Cycle detection ---

/**
 * Hash a state deterministically for cycle detection (string version).
 * Sorts linear {hash:count} entries + persistent keys.
 * Works on plain objects (for debug/test use).
 */
function stateHashStr(plainState) {
  const linParts = Object.entries(plainState.linear || {})
    .filter(([, c]) => c > 0)
    .sort(([a], [b]) => a - b)
    .map(([h, c]) => `${h}:${c}`);
  const persParts = Object.keys(plainState.persistent || {})
    .sort((a, b) => a - b);
  return `L[${linParts.join(',')}]P[${persParts.join(',')}]`;
}


// ─── Explore ────────────────────────────────────────────────────────

/**
 * Explore all execution paths up to depth bound.
 * Handles rule-level nondeterminism AND additive choice in consequents.
 * Uses path-based cycle detection (back-edges only, not joins).
 *
 * Uses FactSet-based State with Arena undo for incremental state management.
 * State IS the index — no separate stateIndex or ExploreContext needed.
 *
 * Options:
 *   structuralMemo: boolean — enable control-hash structural memoization.
 */
function explore(initialState, rules, opts = {}) {
  const maxDepth = opts.maxDepth ?? 100;
  const calc = opts.calc ?? null;
  const useStructuralMemo = opts.structuralMemo ?? false;
  const _smFns = opts.structuralMemoFns || null;  // { createMemoCtx, controlHash, recordMemo }
  const _predictNextFn = opts.predictNext || null;
  const controlOpts = opts.controlOpts || null;
  const evidence = opts.evidence || false;
  const onStep = opts.onStep || null;

  // Default: noFFI (adversarially sound). Opt-in to FFI for benchmarking only.
  const useFFI = opts.dangerouslyUseFFI || false;
  // Clear backward cache at exploration start. See backward-cache.js for the
  // full soundness argument (why clearing once per run is sufficient).
  lnlClearCache();

  // Evidence trace stack — accumulates during DFS, snapshotted at each leaf.
  // Same format as forward.run's evidence trace: { rule, theta, slots,
  // persistentEvidence, loliHash }. guidedTerm consumes these directly.
  const traceStack = evidence ? [] : null;

  const ct = calc?.connectives || null;
  const rc = ct ? resolveConn(ct) : {};
  const implTag = rc.implication;
  const _TAG_LOLI = Store.TAG[implTag];

  // noFFI: convert bytecode arrlit → trie for clause resolution.
  // FFI mode keeps arrlit for O(1) arr_get access.
  // bytecodeToTrie comes from calculus config (domainConfig) via orchestrator.
  // Lazy ILL fallback for direct callers that bypass orchestrator.
  let effectiveInitial = initialState;
  if (!useFFI && initialState.linear && !initialState.linear.group) {
    const _bytecodeToTrie = calc?.domainConfig?.bytecodeToTrie;
    if (_bytecodeToTrie) effectiveInitial = _bytecodeToTrie(initialState);
  }

  // Accept both plain objects and State objects
  const state = effectiveInitial.linear && effectiveInitial.linear.group
    ? effectiveInitial.clone()  // Clone so we don't modify caller's state
    : fromObject(effectiveInitial.linear, effectiveInitial.persistent);

  // Carry forward bytecode element cache for O(1) prediction
  if (effectiveInitial._bytecodeElems) state._bytecodeElems = effectiveInitial._bytecodeElems;

  // Pre-build rule index (consequentAlts precomputed in compileRule)
  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  const indexedRules = rules.rules ? rules : { rules };

  // Auto-detect strategy (or use caller-provided one)
  const strategy = opts.strategy || detectStrategy(ruleList);

  // Extract config early — needed by fpConfig injection and constraint solver
  const _domCfg = calc?.domainConfig || null;

  // Set up fingerprint on state
  const fpConfig = strategy.fpConfig || null;
  if (fpConfig) {
    // Inject domain-specific lookupArrayValue for virtual fingerprint dispatch
    if (!fpConfig.lookupArrayValue && _domCfg?.lookupArrayValue) {
      fpConfig.lookupArrayValue = _domCfg.lookupArrayValue;
    }
    state._fpPred = fpConfig.pred;
    state._fpKeyPos = fpConfig.keyPos;
    if (fpConfig.type !== 'virtual') {
      buildFingerprintIndex(state, fpConfig);
    }
  }

  // Constraint solver for branch pruning (eq/neq)
  const _evalNumeric = _domCfg?.evalNumeric || undefined;
  const solver = new EqNeqSolver(_evalNumeric ? { evalNumeric: _evalNumeric } : {});
  // Seed solver with initial persistent facts
  state.persistent.forEach(h => solver.addConstraint(h));

  // Arenas for mutation undo
  const linArena = new Arena(16384);
  const perArena = new Arena(4096);

  // Prediction closure (Opt_H) — threaded code dispatch
  const _predOpts = {};
  if (_evalNumeric) _predOpts.binToInt = _evalNumeric;
  if (_domCfg?.trieNav) _predOpts.trieNav = _domCfg.trieNav;
  const predictor = _predictNextFn ? _predictNextFn(ruleList, fpConfig, state, _predOpts) : null;
  const matchOpts = opts.matchOpts || EMPTY_MATCH_OPTS;
  const drainLolis = matchOpts.drainLolis || null;

  // DFS with mutation+undo via FactSet + Arena.
  // State is mutated in-place during DFS and restored via arena undo.
  const pathVisited = new Set();
  const globalVisited = new Set();

  // Structural memoization context (null when disabled)
  const memoCtx = (useStructuralMemo && _smFns) ? _smFns.createMemoCtx() : null;

  /**
   * Algorithm: Exhaustive Forward Exploration (DFS + Mutation/Undo)
   *
   * Implements CLF's monadic forward chaining judgment: Σ; Δ ⊢_fwd T : A
   * where Σ = compiled rules, Δ = linear multiset state, T = execution tree.
   *
   * The search enumerates all interleavings of committed-choice forward
   * steps (CLF atomic actions) under additive nondeterminism (⊕). Each
   * step consumes linear resources, proves persistent guards, and produces
   * new facts — a single CLF monadic let-binding.
   *
   * State is mutated in-place during DFS and restored via Arena undo logs,
   * giving O(1) checkpoint/restore without copying the multiset.
   *
   *   go(depth):
   *     1. CYCLE CHECK — if stateHash ∈ pathVisited → cycle node
   *        (back-edge in DFS; avoids infinite loops on circular resource configs)
   *     2. MEMO CHECK  — if stateHash ∈ globalVisited → memo node
   *        (state already fully explored; sound because forward steps are deterministic per-state)
   *     3. STRUCTURAL MEMO — if controlHash(PC,SH) ∈ globalControl → memo node
   *        (coarser hash on control state only; sound when branching is symbolic)
   *     4. BOUND CHECK — if depth ≥ maxDepth → bound node
   *     5. MATCH       — findAllMatches(Δ, Σ) via strategy stack
   *        (fingerprint → disc-tree → predicate-index → general)
   *     6. QUIESCENT   — if no matches → leaf node (normal form / terminal state)
   *     7. BRANCH      — for each match m in nondeterministic choice:
   *        a. Single-alt (no ⊕): mutate(Δ, m) → drainLolis → go(depth+1) → undo
   *        b. Multi-alt (⊕): SAT-filter alternatives via EqNeqSolver →
   *           - 0 survivors → dead node (all branches UNSAT)
   *           - 1 survivor → collapse to single-alt (deterministic pruning)
   *           - N survivors → fork: for each alt: mutate → drain → go → undo
   *     8. Record stateHash in globalVisited; if subtree has no bound nodes,
   *        record controlHash in structuralMemo
   *     → return branch(children)
   */
  function go(depth, predicted) {
    const sh = state.stateHash;

    if (pathVisited.has(sh)) {
      return { type: 'cycle', state: state.snapshotBulk() };
    }

    if (globalVisited.has(sh)) {
      return { type: 'memo', state: state.snapshotBulk() };
    }

    // Structural memo: check control hash (only when subtree was fully explored)
    let ctrlHash;
    let boundBefore;
    if (memoCtx) {
      ctrlHash = _smFns.controlHash(state, controlOpts);
      if (memoCtx.globalControl.get(ctrlHash) === true) {
        return { type: 'memo', state: state.snapshotBulk() };
      }
      boundBefore = memoCtx.boundCount;
    }

    if (depth >= maxDepth) {
      if (memoCtx) memoCtx.boundCount++;
      return { type: 'bound', state: state.snapshotBulk() };
    }

    // Prediction fast path (Opt_H): if we predicted the next rule,
    // try it directly. Skip findAllMatches if it succeeds and no lolis.
    let matches;
    if (predicted) {
      const pm = tryMatch(predicted, state, calc, matchOpts);
      if (pm && state.linear.group(_TAG_LOLI).length === 0) {
        matches = [pm];
      } else {
        matches = findAllMatches(state, indexedRules, calc, strategy, matchOpts);
      }
    } else {
      matches = findAllMatches(state, indexedRules, calc, strategy, matchOpts);
    }

    if (matches.length === 0) {
      return { type: 'leaf', state: state.snapshotBulk(),
        trace: traceStack ? traceStack.slice() : undefined };
    }

    pathVisited.add(sh);

    const children = [];
    for (let mi = 0; mi < matches.length; mi++) {
      const m = matches[mi];
      const alts = m.rule.consequentAlts;

      if (alts.length <= 1) {
        // Single-alt: pass full consequent + rule so mutateState handles
        // preserved-skip + compiled substitution together (recipe indices align)
        const linCp = linArena.checkpoint();
        const perCp = perArena.checkpoint();
        const scp = solver.checkpoint();

        if (traceStack) traceStack.push({
          rule: m.rule, consumed: { ...m.consumed },
          theta: m.theta.slice(), slots: m.slots,
          persistentEvidence: m.persistentEvidence || [],
          loliHash: m.loliHash || null
        });

        mutateState(state, m.consumed, m.theta,
          m.rule.consequent.linear || [], m.rule.consequent.persistent || [],
          m.slots, m.optimized ? m.rule : null, linArena, perArena);

        // Drain persistent-trigger lolis eagerly (CLF monad fusion)
        if (drainLolis) drainLolis(state, linArena, perArena, calc, null, matchOpts);

        // Feed all new persistent facts into constraint solver
        feedPers(solver, perArena, perCp);

        if (onStep) onStep({
          depth, rule: m.rule,
          consumed: { ...m.consumed }, theta: m.theta.slice(),
          slots: m.slots, state
        });

        const pred = predictor ? predictor(m) : null;
        const child = go(depth + 1, pred);

        if (traceStack) traceStack.pop();
        state.persistent.undo(perArena, perCp);
        state.linear.undo(linArena, linCp);
        solver.restore(scp);

        children.push({ rule: m.rule.name, child });
      } else {
        // Multi-alt: pre-filter alternatives via constraint solver.
        // If only 1 survives, collapse to single-alt (no branch node).
        const satAlts = satFilter(solver, alts, m.theta, m.slots);

        if (satAlts.length === 0) {
          // All alternatives UNSAT — produce a single dead child
          children.push({ rule: m.rule.name, child: { type: 'dead', state: null } });
        } else if (satAlts.length === 1) {
          // Single survivor — collapse to single-alt (no branch node)
          const i = satAlts[0];
          let linPats = alts[i].linear;
          if (m.optimized && m.rule.preserved) {
            linPats = filterPres(alts[i].linear, m.rule.preserved);
          }
          const linCp = linArena.checkpoint();
          const perCp = perArena.checkpoint();
          const scp = solver.checkpoint();

          // Rebase rule.consequent to the chosen alt for guided term building
          if (traceStack) traceStack.push({
            rule: { ...m.rule, consequent: alts[i],
              compiledConseqLinear: null, compiledConseqPersistent: null },
            consumed: { ...m.consumed },
            theta: m.theta.slice(), slots: m.slots,
            persistentEvidence: m.persistentEvidence || [],
            loliHash: m.loliHash || null
          });

          mutateState(state, m.consumed, m.theta,
            linPats, alts[i].persistent, m.slots, null, linArena, perArena);
          if (drainLolis) drainLolis(state, linArena, perArena, calc, null, matchOpts);
          feedPers(solver, perArena, perCp);

          if (onStep) onStep({
            depth, rule: { ...m.rule, consequent: alts[i] },
            consumed: { ...m.consumed }, theta: m.theta.slice(),
            slots: m.slots, state
          });

          const pred = predictor ? predictor(m) : null;
          const child = go(depth + 1, pred);

          if (traceStack) traceStack.pop();
          state.persistent.undo(perArena, perCp);
          state.linear.undo(linArena, linCp);
          solver.restore(scp);

          children.push({ rule: m.rule.name, child });
        } else {
          // Multiple survivors — branch with dead nodes for pruned alts
          for (let i = 0; i < alts.length; i++) {
            let linPats = alts[i].linear;
            if (m.optimized && m.rule.preserved) {
              linPats = filterPres(alts[i].linear, m.rule.preserved);
            }
            const linCp = linArena.checkpoint();
            const perCp = perArena.checkpoint();
            const scp = solver.checkpoint();

            mutateState(state, m.consumed, m.theta,
              linPats, alts[i].persistent, m.slots, null, linArena, perArena);

            // Feed initial mutation's persistent facts for SAT check
            feedPers(solver, perArena, perCp);

            if (!solver.checkSAT()) {
              state.persistent.undo(perArena, perCp);
              state.linear.undo(linArena, linCp);
              solver.restore(scp);
              children.push({ rule: m.rule.name, choice: i, child: { type: 'dead', state: null } });
              continue;
            }

            // Rebase rule.consequent to the chosen alt for guided term building
            if (traceStack) traceStack.push({
              rule: { ...m.rule, consequent: alts[i],
                compiledConseqLinear: null, compiledConseqPersistent: null },
              consumed: { ...m.consumed },
              theta: m.theta.slice(), slots: m.slots,
              persistentEvidence: m.persistentEvidence || [],
              loliHash: m.loliHash || null
            });

            const preDrainCp = perArena.checkpoint();
            if (drainLolis) drainLolis(state, linArena, perArena, calc, null, matchOpts);
            // Feed drain's new persistent facts
            feedPers(solver, perArena, preDrainCp);

            if (onStep) onStep({
              depth, rule: { ...m.rule, consequent: alts[i] },
              consumed: { ...m.consumed }, theta: m.theta.slice(),
              slots: m.slots, state
            });

            // No prediction for multi-alt branching (rare path)
            const child = go(depth + 1);

            if (traceStack) traceStack.pop();
            state.persistent.undo(perArena, perCp);
            state.linear.undo(linArena, linCp);
            solver.restore(scp);

            children.push({ rule: m.rule.name, choice: i, child });
          }
        }
      }
    }

    pathVisited.delete(sh);
    globalVisited.add(sh);

    // Record structural memo if subtree was fully explored (no bound nodes)
    if (memoCtx && ctrlHash !== undefined) {
      _smFns.recordMemo(ctrlHash, boundBefore, memoCtx);
    }

    return { type: 'branch', state: null, children };
  }

  return go(0);
}

module.exports = {
  explore,
  findAllMatches,
  stateHashStr,
  // State mutation (for benchmarking)
  mutateState,
};
