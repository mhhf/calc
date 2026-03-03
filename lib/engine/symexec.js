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
const { applyIndexed: subApplyIdx } = require('../kernel/substitute');
const { expandChoiceItem, expandConsequentChoices } = require('./compile');
const { buildFingerprintIndex } = require('./forward');
const { tryMatch, buildDiscriminatorIndex } = require('./match');
const { findAllMatches, detectStrategy } = require('./strategy');
const { EqNeqSolver } = require('./constraint');
const { fromObject, Arena, INSERT_OP } = require('./fact-set');
const { filterPreserved, consumeLinear, produceLinear, producePersistent } = require('./state-ops');
const { drainPersistentLolis } = require('./opt/loli-drain');
const ffi = require('./ffi');

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

// --- State mutation ---

/**
 * Mutate state in-place: consume linear facts, produce new facts.
 * Records undo entries in linArena/perArena for backtracking.
 *
 * @param {State} state - Mutable FactSet-based State
 * @param {{ [hash: string]: number }} consumed - Consumed linear facts
 * @param {Array} theta - Substitution
 * @param {number[]} linearPatterns - Consequent linear patterns
 * @param {number[]} persistentPatterns - Consequent persistent patterns
 * @param {Object} slots - Metavar slot mapping
 * @param {Object|null} rule - Compiled rule (for preserved-skip + compiled sub)
 * @param {Arena} linArena - Undo arena for linear FactSet
 * @param {Arena} perArena - Undo arena for persistent FactSet
 */
function mutateState(state, consumed, theta, linearPatterns, persistentPatterns, slots, rule, linArena, perArena) {
  consumeLinear(state.linear, consumed, linArena);
  produceLinear(state.linear, linearPatterns, theta, slots, rule, !!rule, linArena);
  producePersistent(state.persistent, persistentPatterns, theta, slots, rule, perArena);
}

const _TAG_LOLI = Store.TAG.loli;

/**
 * Feed newly-added persistent facts from perArena into the solver.
 * Reads arena records from checkpoint to current cursor, looking for INSERT ops.
 */
function _feedPersistent(solver, perArena, checkpoint) {
  const buf = perArena.buf;
  for (let i = checkpoint; i < perArena.cursor; i += 4) {
    if (buf[i] === INSERT_OP) {
      solver.addConstraint(buf[i + 2]); // hash is at offset +2
    }
  }
}

// ─── Control Hash (structural memoization) ──────────────────────────

/**
 * Compute a "control hash" for structural memoization.
 * Uses State's FactSet groups for O(1) access to pc and stack facts.
 *
 * Hashes only: PC value + stack arrlit length (stack depth).
 * These two values identify the execution point — states with the same
 * PC and stack depth execute the same instruction sequence.
 *
 * Sound when: (a) all oplus branching is on symbolic values (evars/freevars),
 * and (b) the constraint solver's pruning doesn't depend on state differences
 * excluded from this hash.
 */
function computeControlHash(state) {
  const pcTagId = Store.TAG['pc'];
  const stackTagId = Store.TAG['stack'];
  const pcGroup = pcTagId !== undefined ? state.linear.group(pcTagId) : _emptyI32;
  const stackGroup = stackTagId !== undefined ? state.linear.group(stackTagId) : _emptyI32;
  const pcVal = pcGroup.length > 0 ? Store.child(pcGroup[0], 0) : 0;
  let stackLen = 0;
  if (stackGroup.length > 0) {
    const arrHash = Store.child(stackGroup[0], 0);
    const elems = Store.getArrayElements(arrHash);
    stackLen = elems ? elems.length : 0;
  }
  return (Math.imul(pcVal | 0, 2654435761) ^ Math.imul(stackLen | 0, 2246822519)) >>> 0;
}

const _emptyI32 = new Int32Array(0);

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
  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('./prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  // Constraint solver for branch pruning (eq/neq)
  const solver = new EqNeqSolver();
  // Seed solver with initial persistent facts
  state.persistent.forEach(h => solver.addConstraint(h));

  // Arenas for mutation undo
  const linArena = new Arena(16384);
  const perArena = new Arena(4096);

  // ─── Prediction infrastructure (Opt_H) ─────────────────────────────
  // For virtual fingerprint configs, we can predict the next rule from the
  // substitution: theta[nextPointerSlot] → new PC → bytecode lookup → rule.
  const _binToInt = ffi.convert.binToInt;
  const discIndex = buildDiscriminatorIndex(ruleList);
  let bytecodeElems = null;
  if (fpConfig && fpConfig.type === 'virtual') {
    const arrayTagId = Store.TAG[fpConfig.arrayPred];
    if (arrayTagId !== undefined) {
      const arrayGroup = state.linear.group(arrayTagId);
      if (arrayGroup.length === 1) {
        bytecodeElems = Store.getArrayElements(Store.child(arrayGroup[0], 0));
      }
    }
  }
  const _predMatchOpts = { optimizePreserved: true };

  function predictNext(m) {
    if (!bytecodeElems) return null;
    const rule = m.rule;
    if (rule.nextPointerSlot === undefined) return null;

    let newPC;
    if (rule.nextPointerSlot === -1) {
      newPC = rule.nextPointerValue;
    } else {
      newPC = m.theta[rule.nextPointerSlot];
      if (newPC === undefined) return null;
    }

    const idx = _binToInt(newPC);
    if (idx === null || idx < 0n || idx >= BigInt(bytecodeElems.length)) return null;
    const opcode = bytecodeElems[Number(idx)];

    const candidates = discIndex[opcode];
    if (!candidates || candidates.length !== 1) return null;
    return candidates[0];
  }

  // DFS with mutation+undo via FactSet + Arena.
  // State is mutated in-place during DFS and restored via arena undo.
  const pathVisited = new Set();
  const globalVisited = new Set();

  // Structural memoization: control hash → true (complete, no bound nodes)
  const globalControl = useStructuralMemo ? new Map() : null;
  let boundCount = 0;

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
    if (globalControl) {
      controlHash = computeControlHash(state);
      if (globalControl.get(controlHash) === true) {
        return { type: 'memo', state: state.snapshotBulk() };
      }
      boundBefore = boundCount;
    }

    if (depth >= maxDepth) {
      boundCount++;
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
        matches = findAllMatches(state, indexedRules, calc, strategy);
      }
    } else {
      matches = findAllMatches(state, indexedRules, calc, strategy);
    }

    if (matches.length === 0) {
      return { type: 'leaf', state: state.snapshotBulk() };
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

        mutateState(state, m.consumed, m.theta,
          m.rule.consequent.linear || [], m.rule.consequent.persistent || [],
          m.slots, m.optimized ? m.rule : null, linArena, perArena);

        // Drain persistent-trigger lolis eagerly (CLF monad fusion)
        drainPersistentLolis(state, linArena, perArena, calc, mutateState);

        // Feed all new persistent facts into constraint solver
        _feedPersistent(solver, perArena, perCp);

        const pred = predictNext(m);
        const child = go(depth + 1, pred);

        state.persistent.undo(perArena, perCp);
        state.linear.undo(linArena, linCp);
        solver.restore(scp);

        children.push({ rule: m.rule.name, child });
      } else {
        // Multi-alt: pre-filter alternatives via constraint solver.
        // If only 1 survives, collapse to single-alt (no branch node).
        const satAlts = [];
        for (let i = 0; i < alts.length; i++) {
          const scp = solver.checkpoint();
          for (const pattern of alts[i].persistent) {
            const h = subApplyIdx(pattern, m.theta, m.slots);
            solver.addConstraint(h);
          }
          if (solver.checkSAT()) satAlts.push(i);
          solver.restore(scp);
        }

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

          mutateState(state, m.consumed, m.theta,
            linPats, alts[i].persistent, m.slots, null, linArena, perArena);
          drainPersistentLolis(state, linArena, perArena, calc, mutateState);
          _feedPersistent(solver, perArena, perCp);

          const pred = predictNext(m);
          const child = go(depth + 1, pred);

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
            _feedPersistent(solver, perArena, perCp);

            if (!solver.checkSAT()) {
              state.persistent.undo(perArena, perCp);
              state.linear.undo(linArena, linCp);
              solver.restore(scp);
              children.push({ rule: m.rule.name, choice: i, child: { type: 'dead', state: null } });
              continue;
            }

            const preDrainCp = perArena.checkpoint();
            drainPersistentLolis(state, linArena, perArena, calc, mutateState);
            // Feed drain's new persistent facts
            _feedPersistent(solver, perArena, preDrainCp);

            // No prediction for multi-alt branching (rare path)
            const child = go(depth + 1);

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
    if (globalControl && controlHash !== undefined) {
      if (boundBefore !== undefined && boundCount === boundBefore) {
        globalControl.set(controlHash, true);
      }
    }

    return { type: 'branch', state: null, children };
  }

  return go(0);
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
