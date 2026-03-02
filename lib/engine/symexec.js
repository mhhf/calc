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
 * additive choice in consequents (A & B forks the tree).
 *
 * Uses FactSet-based State (lib/engine/fact-set.js) with Arena undo.
 * State IS the index — no separate stateIndex needed.
 */

const Store = require('../kernel/store');
const { applyIndexed: subApplyIdx, subCompiled } = require('../kernel/substitute');
const { expandItem, expandConsequentChoices } = require('./compile');
const { matchLoli } = require('./match');
const { findAllMatches, detectStrategy } = require('./strategy');
const { EqNeqSolver } = require('./constraint');
const { fromObject, Arena, INSERT_OP } = require('./fact-set');

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

// Keep hashState as alias for backward compat (used by benchmark, tests)
const hashState = hashStateString;

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
  // Consume linear facts
  for (const hStr in consumed) {
    const hash = Number(hStr);
    const count = consumed[hStr];
    const tagIdx = Store.tagId(hash);
    for (let c = 0; c < count; c++) {
      state.linear.remove(tagIdx, hash, linArena);
    }
  }

  // Produce linear facts (with preserved-skip + compiled sub)
  const cLinear = rule && rule.compiledConseqLinear;
  let skipCount = null;
  if (rule && rule.preserved && rule.preserved.length > 0) {
    skipCount = {};
    for (const h of rule.preserved) skipCount[h] = (skipCount[h] || 0) + 1;
  }
  const skipUsed = {};

  for (let i = 0; i < linearPatterns.length; i++) {
    const pattern = linearPatterns[i];
    if (skipCount && skipCount[pattern] > 0 &&
        (skipUsed[pattern] || 0) < skipCount[pattern]) {
      skipUsed[pattern] = (skipUsed[pattern] || 0) + 1;
      continue;
    }
    let h;
    const recipe = cLinear && cLinear[i];
    if (recipe && recipe.compiled) {
      h = recipe.isSlot ? theta[recipe.slot] : subCompiled(recipe, theta);
    } else {
      h = subApplyIdx(pattern, theta, slots);
    }
    state.linear.insert(Store.tagId(h), h, linArena);
  }

  // Produce persistent facts
  const cPersistent = rule && rule.compiledConseqPersistent;
  for (let i = 0; i < persistentPatterns.length; i++) {
    const pattern = persistentPatterns[i];
    let h;
    const recipe = cPersistent && cPersistent[i];
    if (recipe && recipe.compiled) {
      h = recipe.isSlot ? theta[recipe.slot] : subCompiled(recipe, theta);
    } else {
      h = subApplyIdx(pattern, theta, slots);
    }
    const tagIdx = Store.tagId(h);
    if (!state.persistent.has(tagIdx, h)) {
      state.persistent.insert(tagIdx, h, perArena);
    }
  }
}

// ─── Persistent-trigger Loli Fusion ─────────────────────────────────

const _TAG_LOLI = Store.TAG.loli;

/**
 * Check if a loli hash has an all-bang (persistent-only) trigger.
 * These lolis consume only themselves and can be fired eagerly.
 * O(trigger_size), no allocation.
 */
function isPersistentTriggerLoli(h) {
  if (Store.tagId(h) !== _TAG_LOLI) return false;
  return _allBang(Store.child(h, 0));
}

function _allBang(h) {
  const t = Store.tag(h);
  if (t === 'tensor') return _allBang(Store.child(h, 0)) && _allBang(Store.child(h, 1));
  if (t === 'bang') return true;
  return false;
}

/**
 * Eagerly fire all persistent-trigger lolis in state.
 * Restores CLF monad boundary semantics: guard resolution is part of the atomic step.
 *
 * Safe because:
 * - Persistent-trigger lolis consume ONLY themselves (no other linear facts)
 * - Guards depend only on persistent state (never affected by concurrent transitions)
 * - Firing them eagerly produces identical results regardless of ordering
 *
 * Records all mutations in linArena/perArena for automatic undo.
 */
function drainPersistentLolis(state, linArena, perArena, calc) {
  let drained = true;
  while (drained) {
    drained = false;
    const loliGroup = state.linear.group(_TAG_LOLI);
    // Copy to temp array because mutation changes the group
    const lolis = new Array(loliGroup.length);
    for (let i = 0; i < loliGroup.length; i++) lolis[i] = loliGroup[i];

    for (let i = 0; i < lolis.length; i++) {
      const h = lolis[i];
      if (!state.linear.has(_TAG_LOLI, h)) continue;
      if (!isPersistentTriggerLoli(h)) continue;
      const m = matchLoli(h, state, calc);
      if (!m) continue;
      if (m.rule.consequentAlts.length > 1) continue; // skip oplus-bodied lolis
      const alts = m.rule.consequentAlts;
      mutateState(state, m.consumed, m.theta,
        alts[0].linear, alts[0].persistent, m.slots, null, linArena, perArena);
      drained = true;
      break; // restart scan (state changed)
    }
  }
}

/**
 * Filter linear patterns by skipping preserved (re-produced) facts.
 */
function _skipPreserved(linearPats, preserved) {
  const skipCount = {};
  for (const h of preserved) skipCount[h] = (skipCount[h] || 0) + 1;
  const skipUsed = {};
  const out = [];
  for (const p of linearPats) {
    if (skipCount[p] > 0 && (skipUsed[p] || 0) < skipCount[p]) {
      skipUsed[p] = (skipUsed[p] || 0) + 1;
      continue;
    }
    out.push(p);
  }
  return out;
}

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
 * Uses State's FactSet groups for O(1) access to pc and sh facts.
 *
 * Hashes only: PC value + SH fact hash (stack height encoding).
 * These two values identify the execution point — states with the same
 * PC and SH execute the same instruction sequence.
 *
 * Sound when: (a) all oplus branching is on symbolic values (evars/freevars),
 * and (b) the constraint solver's pruning doesn't depend on state differences
 * excluded from this hash.
 */
function computeControlHash(state) {
  const pcTagId = Store.TAG['pc'];
  const shTagId = Store.TAG['sh'];
  const pcGroup = pcTagId !== undefined ? state.linear.group(pcTagId) : _emptyI32;
  const shGroup = shTagId !== undefined ? state.linear.group(shTagId) : _emptyI32;
  const pcVal = pcGroup.length > 0 ? Store.child(pcGroup[0], 0) : 0;
  const shHash = shGroup.length > 0 ? shGroup[0] : 0;
  return (Math.imul(pcVal | 0, 2654435761) ^ Math.imul(shHash | 0, 2246822519)) >>> 0;
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
    // Build secondary index
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

  // DFS with mutation+undo via FactSet + Arena.
  // State is mutated in-place during DFS and restored via arena undo.
  const pathVisited = new Set();
  const globalVisited = new Set();

  // Structural memoization: control hash → true (complete, no bound nodes)
  const globalControl = useStructuralMemo ? new Map() : null;
  let boundCount = 0;

  function go(depth) {
    const sh = state.stateHash;

    if (pathVisited.has(sh)) {
      return { type: 'cycle', state: state.snapshot() };
    }

    if (globalVisited.has(sh)) {
      return { type: 'memo', state: state.snapshot() };
    }

    // Structural memo: check control hash (only when subtree was fully explored)
    let controlHash;
    let boundBefore;
    if (globalControl) {
      controlHash = computeControlHash(state);
      if (globalControl.get(controlHash) === true) {
        return { type: 'memo', state: state.snapshot() };
      }
      boundBefore = boundCount;
    }

    if (depth >= maxDepth) {
      boundCount++;
      return { type: 'bound', state: state.snapshot() };
    }

    const matches = findAllMatches(state, indexedRules, calc, strategy);

    if (matches.length === 0) {
      return { type: 'leaf', state: state.snapshot() };
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
        drainPersistentLolis(state, linArena, perArena, calc);

        // Feed all new persistent facts into constraint solver
        _feedPersistent(solver, perArena, perCp);

        const child = go(depth + 1);

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
            linPats = _skipPreserved(alts[i].linear, m.rule.preserved);
          }
          const linCp = linArena.checkpoint();
          const perCp = perArena.checkpoint();
          const scp = solver.checkpoint();

          mutateState(state, m.consumed, m.theta,
            linPats, alts[i].persistent, m.slots, null, linArena, perArena);
          drainPersistentLolis(state, linArena, perArena, calc);
          _feedPersistent(solver, perArena, perCp);

          const child = go(depth + 1);

          state.persistent.undo(perArena, perCp);
          state.linear.undo(linArena, linCp);
          solver.restore(scp);

          children.push({ rule: m.rule.name, child });
        } else {
          // Multiple survivors — branch with dead nodes for pruned alts
          for (let i = 0; i < alts.length; i++) {
            let linPats = alts[i].linear;
            if (m.optimized && m.rule.preserved) {
              linPats = _skipPreserved(alts[i].linear, m.rule.preserved);
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
            drainPersistentLolis(state, linArena, perArena, calc);
            // Feed drain's new persistent facts
            _feedPersistent(solver, perArena, preDrainCp);

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
  expandItem,
  expandConsequentChoices,
  hashState,
  hashStateString,
  // State mutation (for benchmarking)
  mutateState,
  computeControlHash,
};
