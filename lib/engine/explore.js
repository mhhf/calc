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
const { expandChoiceItem, expandConsequentChoices } = require('./compile');
const { buildFingerprintIndex } = require('./forward');
const match = require('./match');
const { tryMatch } = match;
const { findAllMatches, detectStrategy } = require('./strategy');
const { EqNeqSolver } = require('./constraint');
const { fromObject, Arena } = require('./fact-set');
const { filterPreserved, mutateState } = require('./state-ops');
const { drainPersistentLolis } = require('./opt/loli-drain');
const { computeControlHash, createMemoCtx, recordMemo } = require('./opt/structural-memo');
const { createPredictNext } = require('./opt/prediction');
const { feedPersistent, filterAltsBySAT } = require('./opt/constraint');

// --- Cycle detection ---

/**
 * Hash a state deterministically for cycle detection (string version).
 * Sorts linear {hash:count} entries + persistent keys.
 * Works on plain objects (for debug/test use).
 */
function hashStateString(plainState) {
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
  const engine = opts.engine ?? null;
  const useStructuralMemo = opts.structuralMemo ?? false;
  const evidence = opts.evidence || false;

  // Default: noFFI (adversarially sound). Opt-in to FFI for benchmarking only.
  const useFFI = opts.dangerouslyUseFFI || false;
  match.setNoFFI(!useFFI);
  // Tabling soundness: clear at exploration start. Persistent context grows
  // monotonically within a single DFS path, so cached successes remain valid.
  // But different DFS paths restore persistent state via Arena undo, so
  // a success cached on path A may be invalid on path B. This is safe:
  // persistent facts only grow (never retracted), so any cached success
  // remains provable on all paths. Cached failures are conservative —
  // a goal that failed with fewer persistent facts won't succeed with more.
  // Actually: Arena undo DOES retract persistent facts on backtrack, but
  // the cache is keyed on input args (not persistent state), so we clear
  // once at start and accept that cached failures may be stale on paths
  // with more persistent facts. This is sound: false negatives cause
  // re-proving (slower but correct), never false positives.
  match.clearBackwardCache();

  try {
  // Evidence trace stack — accumulates during DFS, snapshotted at each leaf.
  // Same format as forward.run's evidence trace: { rule, theta, slots,
  // persistentEvidence, loliHash }. buildGuidedTerm consumes these directly.
  const traceStack = evidence ? [] : null;

  const implTag = calc?.roles?.implication || 'loli';
  const _TAG_LOLI = Store.TAG[implTag];

  // Accept both plain objects and State objects
  const state = initialState.linear && initialState.linear.group
    ? initialState.clone()  // Clone so we don't modify caller's state
    : fromObject(initialState.linear, initialState.persistent);

  // Pre-build rule index (consequentAlts precomputed in compileRule)
  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  const indexedRules = rules.rules ? rules : { rules };

  // Auto-detect strategy (or use caller-provided one)
  const strategy = opts.strategy || detectStrategy(ruleList);

  // Set up fingerprint on state
  const fpConfig = strategy.fpConfig || null;
  if (fpConfig) {
    state._fpPred = fpConfig.pred;
    state._fpKeyPos = fpConfig.keyPos;
    if (fpConfig.type !== 'virtual') {
      buildFingerprintIndex(state, fpConfig);
    }
  }

  // Build backward prover index if needed
  if (calc && calc.clauses && calc.definitions && !calc.backwardIndex) {
    const backward = require('./prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.definitions);
  }

  // Constraint solver for branch pruning (eq/neq)
  const solver = new EqNeqSolver();
  // Seed solver with initial persistent facts
  state.persistent.forEach(h => solver.addConstraint(h));

  // Arenas for mutation undo
  const linArena = new Arena(16384);
  const perArena = new Arena(4096);

  // Prediction closure (Opt_H) — threaded code dispatch
  const predictNext = createPredictNext(ruleList, fpConfig, state);
  const _predMatchOpts = evidence
    ? { optimizePreserved: true, evidence: true }
    : { optimizePreserved: true };

  // DFS with mutation+undo via FactSet + Arena.
  // State is mutated in-place during DFS and restored via arena undo.
  const pathVisited = new Set();
  const globalVisited = new Set();

  // Structural memoization context (null when disabled)
  const memoCtx = useStructuralMemo ? createMemoCtx() : null;

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
   *        a. Single-alt (no ⊕): mutate(Δ, m) → drainPersistentLolis → go(depth+1) → undo
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
    let controlHash;
    let boundBefore;
    if (memoCtx) {
      controlHash = computeControlHash(state);
      if (memoCtx.globalControl.get(controlHash) === true) {
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
      const pm = tryMatch(predicted, state, calc, _predMatchOpts);
      if (pm && state.linear.group(_TAG_LOLI).length === 0) {
        matches = [pm];
      } else {
        matches = findAllMatches(state, indexedRules, calc, strategy, _predMatchOpts);
      }
    } else {
      matches = findAllMatches(state, indexedRules, calc, strategy, _predMatchOpts);
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
        drainPersistentLolis(state, linArena, perArena, calc);

        // Feed all new persistent facts into constraint solver
        feedPersistent(solver, perArena, perCp);

        const pred = predictNext ? predictNext(m) : null;
        const child = go(depth + 1, pred);

        if (traceStack) traceStack.pop();
        state.persistent.undo(perArena, perCp);
        state.linear.undo(linArena, linCp);
        solver.restore(scp);

        children.push({ rule: m.rule.name, child });
      } else {
        // Multi-alt: pre-filter alternatives via constraint solver.
        // If only 1 survives, collapse to single-alt (no branch node).
        const satAlts = filterAltsBySAT(solver, alts, m.theta, m.slots);

        if (satAlts.length === 0) {
          // All alternatives UNSAT — produce a single dead child
          children.push({ rule: m.rule.name, child: { type: 'dead', state: null } });
        } else if (satAlts.length === 1) {
          // Single survivor — collapse to single-alt (no branch node)
          const i = satAlts[0];
          let linPats = alts[i].linear;
          if (m.optimized && m.rule.preserved) {
            linPats = filterPreserved(alts[i].linear, m.rule.preserved);
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
          drainPersistentLolis(state, linArena, perArena, calc);
          feedPersistent(solver, perArena, perCp);

          const pred = predictNext ? predictNext(m) : null;
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
              linPats = filterPreserved(alts[i].linear, m.rule.preserved);
            }
            const linCp = linArena.checkpoint();
            const perCp = perArena.checkpoint();
            const scp = solver.checkpoint();

            mutateState(state, m.consumed, m.theta,
              linPats, alts[i].persistent, m.slots, null, linArena, perArena);

            // Feed initial mutation's persistent facts for SAT check
            feedPersistent(solver, perArena, perCp);

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
            drainPersistentLolis(state, linArena, perArena, calc);
            // Feed drain's new persistent facts
            feedPersistent(solver, perArena, preDrainCp);

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
    if (memoCtx && controlHash !== undefined) {
      recordMemo(controlHash, boundBefore, memoCtx);
    }

    return { type: 'branch', state: null, children };
  }

  return go(0);
  } finally {
    match.setNoFFI(true); // Reset to default (noFFI)
  }
}

module.exports = {
  explore,
  findAllMatches,
  expandChoiceItem,
  expandConsequentChoices,
  hashStateString,
  // State mutation (for benchmarking)
  mutateState,
  computeControlHash,
};
