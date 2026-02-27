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
 */

const Store = require('../kernel/store');
const { applyIndexed: subApplyIdx, subCompiled } = require('../kernel/substitute');
const { getPredicateHead } = require('../kernel/ast');
const { expandItem, expandConsequentChoices } = require('./compile');
const { buildStateIndex, matchLoli } = require('./match');
const { findAllMatches, detectStrategy } = require('./strategy');
const { EqNeqSolver } = require('./constraint');

// --- Apply match with specific choice alternative ---

/**
 * Apply a match using a specific consequent alternative (for choice expansion).
 * Like forward.applyMatch but substitutes into the given alternative hashes
 * instead of using rule.consequent directly.
 *
 * @param {Object} state - { linear, persistent }
 * @param {{ rule, theta, consumed }} m - Match result
 * @param {{ linear: number[], persistent: number[] }} alt - Consequent alternative
 * @returns {Object} New state
 */
function applyMatchChoice(state, { theta, consumed, optimized, rule, slots }, alt) {
  const newLinear = { ...state.linear };
  for (const [h, count] of Object.entries(consumed)) {
    const hash = Number(h);
    newLinear[hash] -= count;
    if (newLinear[hash] <= 0) delete newLinear[hash];
  }

  // Build skip count for preserved consequent patterns
  let skipCount = null;
  if (optimized && rule && rule.preserved) {
    skipCount = {};
    for (const h of rule.preserved) {
      skipCount[h] = (skipCount[h] || 0) + 1;
    }
  }
  const skipUsed = {};

  for (const pattern of alt.linear) {
    if (skipCount && skipCount[pattern] > 0 &&
        (skipUsed[pattern] || 0) < skipCount[pattern]) {
      skipUsed[pattern] = (skipUsed[pattern] || 0) + 1;
      continue;
    }
    const h = subApplyIdx(pattern, theta, slots);
    newLinear[h] = (newLinear[h] || 0) + 1;
  }

  const newPersistent = { ...state.persistent };
  for (const pattern of alt.persistent) {
    const h = subApplyIdx(pattern, theta, slots);
    newPersistent[h] = true;
  }

  return { linear: newLinear, persistent: newPersistent };
}

// --- Cycle detection ---

/**
 * Hash a state deterministically for cycle detection (string version).
 * Sorts linear {hash:count} entries + persistent keys.
 */
function hashStateString(state) {
  const linParts = Object.entries(state.linear || {})
    .filter(([, c]) => c > 0)
    .sort(([a], [b]) => a - b)
    .map(([h, c]) => `${h}:${c}`);
  const persParts = Object.keys(state.persistent || {})
    .sort((a, b) => a - b);
  return `L[${linParts.join(',')}]P[${persParts.join(',')}]`;
}

// Keep hashState as alias for backward compat (used by benchmark, tests)
const hashState = hashStateString;

// --- Incremental ExploreContext ---

/**
 * Mix a fact hash and count into a 32-bit value for commutative hashing.
 * Order-independent: XOR of hashPair values gives state fingerprint.
 */
function hashPair(h, count) {
  let x = Math.imul(h | 0, 2654435761) ^ Math.imul(count | 0, 2246822519);
  x = Math.imul(x ^ (x >>> 16), 0x45d9f3b);
  x = Math.imul(x ^ (x >>> 13), 0x45d9f3b);
  return (x ^ (x >>> 16)) >>> 0;
}

/**
 * Compute full numeric hash from state (linear + persistent).
 */
function computeNumericHash(state) {
  let h = 0;
  for (const [hStr, count] of Object.entries(state.linear || {})) {
    if (count > 0) h ^= hashPair(Number(hStr), count);
  }
  for (const hStr of Object.keys(state.persistent || {})) {
    // persistent facts use a distinct marker (count = -1) to avoid collisions
    h ^= hashPair(Number(hStr), -1);
  }
  return h;
}

/**
 * Extract key value from a fact hash for secondary index. O(1).
 * @param {number} h - Fact hash
 * @param {string} fpPred - Fingerprint predicate name (e.g., 'code')
 * @param {number} fpKeyPos - Key position in the predicate (e.g., 0)
 */
function getSecondaryKey(h, fpPred, fpKeyPos) {
  if (Store.tag(h) !== fpPred || Store.arity(h) <= fpKeyPos) return null;
  return Store.child(h, fpKeyPos);
}

/**
 * Add a fact hash to a stateIndex (mutates idx).
 * Updates secondary index if fingerprint predicate matches.
 */
const _TAG_LOLI_SYM = Store.TAG.loli;

function indexAdd(idx, h) {
  const pred = getPredicateHead(h);
  if (pred) {
    if (!idx[pred]) idx[pred] = [];
    idx[pred].push(h);
    // Update secondary index for fingerprint predicate
    if (pred === idx._fpPred && idx._byKey) {
      const keyValue = getSecondaryKey(h, pred, idx._fpKeyPos);
      if (keyValue !== null) idx._byKey[keyValue] = h;
    }
  } else if (Store.tagId(h) === _TAG_LOLI_SYM) {
    if (!idx._loli) idx._loli = [];
    idx._loli.push(h);
  } else {
    if (!idx['*']) idx['*'] = [];
    idx['*'].push(h);
  }
}

/**
 * Remove a fact hash from a stateIndex (mutates idx).
 * Uses swap-with-last + pop for O(1) removal (order doesn't matter for candidate lists).
 */
function indexRemove(idx, h) {
  const pred = getPredicateHead(h);
  if (pred) {
    const arr = idx[pred];
    if (arr) {
      const i = arr.indexOf(h);
      if (i >= 0) {
        arr[i] = arr[arr.length - 1];
        arr.pop();
      }
    }
    // Update secondary index for fingerprint predicate
    if (pred === idx._fpPred && idx._byKey) {
      const keyValue = getSecondaryKey(h, pred, idx._fpKeyPos);
      if (keyValue !== null && idx._byKey[keyValue] === h) {
        delete idx._byKey[keyValue];
      }
    }
  } else if (Store.tagId(h) === _TAG_LOLI_SYM) {
    const arr = idx._loli;
    if (arr) {
      const i = arr.indexOf(h);
      if (i >= 0) {
        arr[i] = arr[arr.length - 1];
        arr.pop();
      }
    }
  } else {
    const arr = idx['*'];
    if (arr) {
      const i = arr.indexOf(h);
      if (i >= 0) {
        arr[i] = arr[arr.length - 1];
        arr.pop();
      }
    }
  }
}

/**
 * ExploreContext: carries stateIndex + numeric hash through the tree.
 * Created once at root (full build), then incrementally updated per child.
 * Plain object — no class needed since only fields are accessed.
 */
function createExploreContext(stateIndex, stateHash) {
  return { stateIndex, stateHash };
}

/** Build root context from full state. fpConfig from detectFingerprintConfig. */
createExploreContext.fromState = function(state, fpConfig) {
  const stateIndex = buildStateIndex(state.linear, fpConfig || null, state.persistent);
  if (fpConfig) {
    stateIndex._fpPred = fpConfig.pred;
    stateIndex._fpKeyPos = fpConfig.keyPos;
  }
  const stateHash = computeNumericHash(state);
  return createExploreContext(stateIndex, stateHash);
};

/**
 * Create child ExploreContext from parent context + mutation undo log.
 *
 * MUTATION+UNDO PATTERN: The stateIndex is mutated in-place (never cloned).
 * After the child subtree returns, the caller must call undoIndexChanges()
 * to restore the parent's index.
 *
 * @param {ExploreContext} parentCtx
 * @param {Object} state - Already-mutated state (current counts)
 * @param {number[]} log - Flat undo log from mutateState
 * @returns {{ ctx: ExploreContext, indexUndo: Array }}
 */
function makeChildCtx(parentCtx, state, log) {
  const idx = parentCtx.stateIndex;
  let h = parentCtx.stateHash;
  const indexUndo = [];

  for (let i = 0; i < log.length; i += 3) {
    const type = log[i];
    const hash = log[i + 1];
    const oldValue = log[i + 2];

    if (type === 0) {
      // Linear: oldValue is the original count
      const newCount = state.linear[hash] || 0;
      if (oldValue === newCount) continue;
      if (oldValue > 0) h ^= hashPair(hash, oldValue);
      if (newCount > 0) h ^= hashPair(hash, newCount);
      if (oldValue > 0 && newCount <= 0) {
        indexRemove(idx, hash);
        indexUndo.push(hash, 1);  // 1 = was removed, undo by adding back
      } else if (oldValue <= 0 && newCount > 0) {
        indexAdd(idx, hash);
        indexUndo.push(hash, 0);  // 0 = was added, undo by removing
      }
    } else {
      // Persistent: oldValue 0 means it was newly added
      if (!oldValue) {
        h ^= hashPair(hash, -1);
        // Lazy-growing: add predicate to guard set (never undo — false positives OK)
        if (idx._persistentPreds) {
          const pred = getPredicateHead(hash);
          if (pred) idx._persistentPreds.add(pred);
        }
      }
    }
  }

  return { ctx: createExploreContext(idx, h), indexUndo };
}

/**
 * Undo index mutations from makeChildCtx.
 * Restores the stateIndex to its state before the child was applied.
 * Must be called after the child subtree returns and state is undone.
 */
function undoIndexChanges(idx, indexUndo) {
  for (let i = indexUndo.length - 2; i >= 0; i -= 2) {
    const hash = indexUndo[i];
    const wasRemoved = indexUndo[i + 1];
    if (wasRemoved) indexAdd(idx, hash);
    else indexRemove(idx, hash);
  }
}

/**
 * Mutate state in-place: consume linear facts, produce new facts.
 * Returns flat undo log: [TYPE, hash, oldValue, ...] where TYPE: 0=linear, 1=persistent.
 * Records each hash ONCE (first touch wins) so undo restores the pre-mutation value.
 *
 * @param {Object} state - Mutable { linear, persistent }
 * @param {{ [hash: string]: number }} consumed - Consumed linear facts
 * @param {Array} theta - Substitution
 * @param {number[]} linearPatterns - Consequent linear patterns
 * @param {number[]} persistentPatterns - Consequent persistent patterns
 * @param {Object} slots - Metavar slot mapping
 * @param {Object|null} rule - Compiled rule (for preserved-skip + compiled sub)
 * @returns {number[]} Flat undo log [type, hash, oldValue, ...]
 */
function mutateState(state, consumed, theta, linearPatterns, persistentPatterns, slots, rule) {
  const log = [];

  // Consume linear facts. Track seen hashes to record each ONCE (first-touch-wins).
  const seenLinear = {};
  for (const hStr in consumed) {
    const hash = Number(hStr);
    if (!(hash in seenLinear)) {
      seenLinear[hash] = 1;
      log.push(0, hash, state.linear[hash] || 0);
    }
    const newCount = (state.linear[hash] || 0) - consumed[hStr];
    if (newCount <= 0) delete state.linear[hash];
    else state.linear[hash] = newCount;
  }

  // Handle preserved-skip + compiled sub together when rule is provided.
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
    if (!(h in seenLinear)) {
      seenLinear[h] = 1;
      log.push(0, h, state.linear[h] || 0);
    }
    state.linear[h] = (state.linear[h] || 0) + 1;
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
    if (!state.persistent[h]) {
      log.push(1, h, 0);
    }
    state.persistent[h] = true;
  }

  return log;
}

/**
 * Undo a state mutation by restoring original values from flat undo log.
 * Iterates backward for correct restoration order (last-modified-first-restored).
 */
function undoMutate(state, log) {
  for (let i = log.length - 3; i >= 0; i -= 3) {
    const type = log[i];
    const hash = log[i + 1];
    const oldValue = log[i + 2];
    if (type === 0) {
      // Linear
      if (oldValue > 0) state.linear[hash] = oldValue;
      else delete state.linear[hash];
    } else {
      // Persistent
      if (!oldValue) delete state.persistent[hash];
    }
  }
}

/** Snapshot state (deep copy). Only used at terminal nodes. */
function snapshotState(state) {
  return {
    linear: { ...state.linear },
    persistent: { ...state.persistent }
  };
}

// ─── Persistent-trigger Loli Fusion (Option C) ──────────────────────

/**
 * Check if a loli hash has an all-bang (persistent-only) trigger.
 * These lolis consume only themselves and can be fired eagerly.
 * O(trigger_size), no allocation.
 */
function isPersistentTriggerLoli(h) {
  if (Store.tagId(h) !== _TAG_LOLI_SYM) return false;
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
 * @returns {{ ctx, undoLogs, indexUndoLogs }}
 */
function drainPersistentLolis(state, parentCtx, calc) {
  const undoLogs = [];
  const indexUndoLogs = [];
  let currentCtx = parentCtx;
  let drained = true;
  while (drained) {
    drained = false;
    const lolis = currentCtx.stateIndex._loli
      ? [...currentCtx.stateIndex._loli] : [];
    for (const h of lolis) {
      if (!state.linear[h] || state.linear[h] <= 0) continue;
      if (!isPersistentTriggerLoli(h)) continue;
      const m = matchLoli(h, state, calc);
      if (!m) continue;
      if (m.rule.consequentAlts.length > 1) continue; // skip oplus-bodied lolis
      const alts = m.rule.consequentAlts;
      const undo = mutateState(state, m.consumed, m.theta,
        alts[0].linear, alts[0].persistent, m.slots, null);
      const { ctx: newCtx, indexUndo } = makeChildCtx(currentCtx, state, undo);
      undoLogs.push(undo);
      indexUndoLogs.push(indexUndo);
      currentCtx = newCtx;
      drained = true;
      break; // restart scan (state changed)
    }
  }
  return { ctx: currentCtx, undoLogs, indexUndoLogs };
}

/**
 * Undo drain mutations in reverse order.
 */
function undoDrain(stateIndex, state, undoLogs, indexUndoLogs) {
  for (let i = undoLogs.length - 1; i >= 0; i--) {
    undoIndexChanges(stateIndex, indexUndoLogs[i]);
    undoMutate(state, undoLogs[i]);
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
 * Feed newly-added persistent facts from a mutateState undo log into the solver.
 * In the undo log, entries are [type, hash, oldValue, ...] in triples.
 * type=1 means persistent; oldValue=0 means newly added.
 */
function _feedPersistent(solver, log) {
  for (let i = 0; i < log.length; i += 3) {
    if (log[i] === 1 && log[i + 2] === 0) {
      solver.addConstraint(log[i + 1]);
    }
  }
}

// ─── Explore ────────────────────────────────────────────────────────

/**
 * Explore all execution paths up to depth bound.
 * Handles rule-level nondeterminism AND additive choice in consequents.
 * Uses path-based cycle detection (back-edges only, not joins).
 *
 * Uses ExploreContext for incremental stateIndex and hashState updates.
 */
function explore(initialState, rules, opts = {}) {
  const maxDepth = opts.maxDepth ?? 100;
  const calc = opts.calc ?? null;

  // Work with a mutable copy so we don't modify the caller's state
  const state = {
    linear: { ...initialState.linear },
    persistent: { ...initialState.persistent }
  };

  // Pre-build rule index (consequentAlts precomputed in compileRule)
  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  const indexedRules = rules.rules ? rules : { rules };

  // Auto-detect strategy (or use caller-provided one)
  const strategy = opts.strategy || detectStrategy(ruleList);

  // Build backward prover index if needed
  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('./prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  // Constraint solver for branch pruning (eq/neq)
  const solver = new EqNeqSolver();
  // Seed solver with initial persistent facts
  for (const h of Object.keys(initialState.persistent)) {
    solver.addConstraint(Number(h));
  }

  // DFS with mutation+undo for both state AND index.
  // State, stateIndex, and pathVisited are all mutated in-place during DFS
  // and restored when backtracking.
  const pathVisited = new Set();
  const globalVisited = new Set();

  function go(depth, ctx) {
    if (pathVisited.has(ctx.stateHash)) {
      return { type: 'cycle', state: snapshotState(state) };
    }

    if (globalVisited.has(ctx.stateHash)) {
      return { type: 'memo', state: snapshotState(state) };
    }

    if (depth >= maxDepth) {
      return { type: 'bound', state: snapshotState(state) };
    }

    const matches = findAllMatches(state, indexedRules, calc, strategy, ctx.stateIndex);

    if (matches.length === 0) {
      return { type: 'leaf', state: snapshotState(state) };
    }

    pathVisited.add(ctx.stateHash);

    const children = [];
    for (let mi = 0; mi < matches.length; mi++) {
      const m = matches[mi];
      const alts = m.rule.consequentAlts;

      if (alts.length <= 1) {
        // Single-alt: pass full consequent + rule so mutateState handles
        // preserved-skip + compiled substitution together (recipe indices align)
        const undo = mutateState(state, m.consumed, m.theta,
          m.rule.consequent.linear || [], m.rule.consequent.persistent || [],
          m.slots, m.optimized ? m.rule : null);
        const { ctx: childCtx, indexUndo } = makeChildCtx(ctx, state, undo);
        // Feed new persistent facts into constraint solver
        const scp = solver.checkpoint();
        _feedPersistent(solver, undo);
        // Drain persistent-trigger lolis eagerly (CLF monad fusion)
        const drain = drainPersistentLolis(state, childCtx, calc);
        for (const dl of drain.undoLogs) _feedPersistent(solver, dl);
        const child = go(depth + 1, drain.ctx);
        undoDrain(ctx.stateIndex, state, drain.undoLogs, drain.indexUndoLogs);
        undoIndexChanges(ctx.stateIndex, indexUndo);
        undoMutate(state, undo);
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
          const undo = mutateState(state, m.consumed, m.theta,
            linPats, alts[i].persistent, m.slots, null);
          const { ctx: childCtx, indexUndo } = makeChildCtx(ctx, state, undo);
          const scp = solver.checkpoint();
          _feedPersistent(solver, undo);
          const drain = drainPersistentLolis(state, childCtx, calc);
          for (const dl of drain.undoLogs) _feedPersistent(solver, dl);
          const child = go(depth + 1, drain.ctx);
          undoDrain(ctx.stateIndex, state, drain.undoLogs, drain.indexUndoLogs);
          undoIndexChanges(ctx.stateIndex, indexUndo);
          undoMutate(state, undo);
          solver.restore(scp);
          children.push({ rule: m.rule.name, child });
        } else {
          // Multiple survivors — branch with dead nodes for pruned alts
          for (let i = 0; i < alts.length; i++) {
            let linPats = alts[i].linear;
            if (m.optimized && m.rule.preserved) {
              linPats = _skipPreserved(alts[i].linear, m.rule.preserved);
            }
            const undo = mutateState(state, m.consumed, m.theta,
              linPats, alts[i].persistent, m.slots, null);
            const { ctx: childCtx, indexUndo } = makeChildCtx(ctx, state, undo);
            const scp = solver.checkpoint();
            _feedPersistent(solver, undo);
            if (!solver.checkSAT()) {
              undoIndexChanges(ctx.stateIndex, indexUndo);
              undoMutate(state, undo);
              solver.restore(scp);
              children.push({ rule: m.rule.name, choice: i, child: { type: 'dead', state: null } });
              continue;
            }
            const drain = drainPersistentLolis(state, childCtx, calc);
            for (const dl of drain.undoLogs) _feedPersistent(solver, dl);
            const child = go(depth + 1, drain.ctx);
            undoDrain(ctx.stateIndex, state, drain.undoLogs, drain.indexUndoLogs);
            undoIndexChanges(ctx.stateIndex, indexUndo);
            undoMutate(state, undo);
            solver.restore(scp);
            children.push({ rule: m.rule.name, choice: i, child });
          }
        }
      }
    }

    pathVisited.delete(ctx.stateHash);
    globalVisited.add(ctx.stateHash);

    return { type: 'branch', state: null, children };
  }

  // Pass fingerprint config from strategy to root context for secondary index
  const fpConfig = strategy.fpConfig || null;
  const rootCtx = createExploreContext.fromState(state, fpConfig);
  return go(0, rootCtx);
}

module.exports = {
  explore,
  findAllMatches,
  expandItem,
  expandConsequentChoices,
  applyMatchChoice,
  hashState,
  hashStateString,
  // Incremental context + mutation (for benchmarking)
  ExploreContext: createExploreContext,
  makeChildCtx,
  undoIndexChanges,
  mutateState,
  undoMutate,
  snapshotState,
  computeNumericHash,
  hashPair
};
