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
 *
 * Handles both rule-level nondeterminism (which rule fires) and
 * additive choice in consequents (A & B forks the tree).
 */

const Store = require('../../kernel/store');
const { apply: subApply } = require('../../kernel/substitute');
const {
  tryMatch,
  buildStateIndex,
  getPredicateHead
} = require('./forward.js');

// --- Step 1: Choice expansion ---

/**
 * Expand a single hash into alternatives, recursing through with/tensor/bang.
 * Each alternative is { linear: number[], persistent: number[] }.
 *
 * - with(A,B) → concat alternatives from both children
 * - tensor(A,B) → cross-product of alternatives from both children
 * - bang(A) → [{ linear: [], persistent: [A] }]
 * - loli(bang(P), monad(Q)) → assume P persistent, expand Q
 *     (guarded conditional: "if !P then {Q}" — in tree context we commit)
 * - leaf → [{ linear: [h], persistent: [] }]
 */
function expandItem(h) {
  const t = Store.tag(h);
  if (!t) return [{ linear: [h], persistent: [] }];

  if (t === 'with') {
    return [
      ...expandItem(Store.child(h, 0)),
      ...expandItem(Store.child(h, 1))
    ];
  }
  if (t === 'tensor') {
    const lefts = expandItem(Store.child(h, 0));
    const rights = expandItem(Store.child(h, 1));
    const out = [];
    for (const l of lefts) {
      for (const r of rights) {
        out.push({
          linear: [...l.linear, ...r.linear],
          persistent: [...l.persistent, ...r.persistent]
        });
      }
    }
    return out;
  }
  if (t === 'bang') {
    return [{ linear: [], persistent: [Store.child(h, 0)] }];
  }
  // loli(bang(P), monad(Q)) → assume !P, produce Q's resources
  if (t === 'loli') {
    const c0 = Store.child(h, 0);
    const c1 = Store.child(h, 1);
    if (Store.tag(c0) === 'bang' && Store.tag(c1) === 'monad') {
      const bodyAlts = expandItem(Store.child(c1, 0));
      return bodyAlts.map(a => ({
        linear: a.linear,
        persistent: [c0, ...a.persistent]
      }));
    }
  }
  return [{ linear: [h], persistent: [] }];
}

/**
 * Expand compiled consequent into choice alternatives.
 * Cross-products expandItem results across all linear items,
 * then appends the original persistent set.
 *
 * @param {{ linear: number[], persistent: number[] }} consequent
 * @returns {{ linear: number[], persistent: number[] }[]}
 */
function expandConsequentChoices(consequent) {
  let alts = [{ linear: [], persistent: [] }];

  for (const h of (consequent.linear || [])) {
    const itemAlts = expandItem(h);
    const next = [];
    for (const acc of alts) {
      for (const ia of itemAlts) {
        next.push({
          linear: [...acc.linear, ...ia.linear],
          persistent: [...acc.persistent, ...ia.persistent]
        });
      }
    }
    alts = next;
  }

  // Append original persistent from compilation
  const origPersistent = consequent.persistent || [];
  if (origPersistent.length > 0) {
    alts = alts.map(a => ({
      linear: a.linear,
      persistent: [...a.persistent, ...origPersistent]
    }));
  }

  return alts;
}

/**
 * Filter preserved patterns from consequent linear list.
 * Returns only the patterns that should actually be produced.
 */
function filterPreserved(patterns, preserved) {
  const skipCount = {};
  for (const h of preserved) skipCount[h] = (skipCount[h] || 0) + 1;
  const skipUsed = {};
  const result = [];
  for (const p of patterns) {
    if (skipCount[p] > 0 && (skipUsed[p] || 0) < skipCount[p]) {
      skipUsed[p] = (skipUsed[p] || 0) + 1;
      continue;
    }
    result.push(p);
  }
  return result;
}

// --- Step 2: Apply match with specific choice alternative ---

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
function applyMatchChoice(state, { theta, consumed, optimized, rule }, alt) {
  const newLinear = { ...state.linear };
  for (const [h, count] of Object.entries(consumed)) {
    const hash = Number(h);
    newLinear[hash] -= count;
    if (newLinear[hash] <= 0) delete newLinear[hash];
  }

  // Build skip count for preserved consequent patterns
  let skipCount = null;
  if (optimized && rule && rule.analysis) {
    skipCount = {};
    for (const h of rule.analysis.preserved) {
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
    const h = subApply(pattern, theta);
    newLinear[h] = (newLinear[h] || 0) + 1;
  }

  const newPersistent = { ...state.persistent };
  for (const pattern of alt.persistent) {
    const h = subApply(pattern, theta);
    newPersistent[h] = true;
  }

  return { linear: newLinear, persistent: newPersistent };
}

// --- Step 3: Cycle detection ---

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
 * Shallow-clone a stateIndex for branching.
 * Only needed when a node has multiple children (nondeterminism).
 */
function cloneIndex(idx) {
  const clone = {};
  for (const k of Object.keys(idx)) {
    clone[k] = k === 'codeByPC' ? { ...idx[k] } : [...idx[k]];
  }
  return clone;
}

/**
 * Extract PC value from a code fact hash. O(1).
 * {tag: 'code', children: [PC, OPCODE]} → PC
 */
function getCodePC(h) {
  if (Store.tag(h) !== 'code' || Store.arity(h) < 2) return null;
  return Store.child(h, 0);
}

/**
 * Add a fact hash to a stateIndex (mutates idx).
 */
function indexAdd(idx, h) {
  const pred = getPredicateHead(h);
  if (pred) {
    if (!idx[pred]) idx[pred] = [];
    idx[pred].push(h);
    if (pred === 'code') {
      const pcValue = getCodePC(h);
      if (pcValue !== null) {
        if (!idx.codeByPC) idx.codeByPC = {};
        idx.codeByPC[pcValue] = h;
      }
    }
  } else {
    if (!idx['*']) idx['*'] = [];
    idx['*'].push(h);
  }
}

/**
 * Remove a fact hash from a stateIndex (mutates idx).
 */
function indexRemove(idx, h) {
  const pred = getPredicateHead(h);
  if (pred) {
    const arr = idx[pred];
    if (arr) {
      const i = arr.indexOf(h);
      if (i >= 0) arr.splice(i, 1);
    }
    if (pred === 'code' && idx.codeByPC) {
      const pcValue = getCodePC(h);
      if (pcValue !== null && idx.codeByPC[pcValue] === h) {
        delete idx.codeByPC[pcValue];
      }
    }
  } else {
    const arr = idx['*'];
    if (arr) {
      const i = arr.indexOf(h);
      if (i >= 0) arr.splice(i, 1);
    }
  }
}

/**
 * ExploreContext: carries stateIndex + numeric hash through the tree.
 * Created once at root (full build), then incrementally updated per child.
 */
class ExploreContext {
  constructor(stateIndex, stateHash) {
    this.stateIndex = stateIndex;
    this.stateHash = stateHash;
  }

  /** Build from full state (called once at root). */
  static fromState(state) {
    const stateIndex = buildStateIndex(state.linear);
    const stateHash = computeNumericHash(state);
    return new ExploreContext(stateIndex, stateHash);
  }
}

/**
 * Create child ExploreContext from parent context + mutation undo log.
 *
 * MUTATION+UNDO PATTERN: The stateIndex is mutated in-place (never cloned).
 * After the child subtree returns, the caller must call undoIndexChanges()
 * to restore the parent's index. This mirrors the state mutation+undo pattern
 * and eliminates the expensive cloneIndex() call (46µs per clone for the
 * 173-entry codeByPC object spread). See doc/documentation/symexec-optimizations.md.
 *
 * @param {ExploreContext} parentCtx
 * @param {Object} state - Already-mutated state (current counts)
 * @param {{ linearOrig: Object, persistentOrig: Object }} undo - Undo log from mutateState
 * @returns {{ ctx: ExploreContext, indexUndo: Array }}
 */
function makeChildCtx(parentCtx, state, undo) {
  const idx = parentCtx.stateIndex;
  let h = parentCtx.stateHash;
  const indexUndo = [];

  for (const hStr in undo.linearOrig) {
    const hash = Number(hStr);
    const oldCount = undo.linearOrig[hStr];
    const newCount = state.linear[hash] || 0;
    if (oldCount === newCount) continue;
    if (oldCount > 0) h ^= hashPair(hash, oldCount);
    if (newCount > 0) h ^= hashPair(hash, newCount);
    if (oldCount > 0 && newCount <= 0) {
      indexRemove(idx, hash);
      indexUndo.push(hash, 1);  // 1 = was removed, undo by adding back
    } else if (oldCount <= 0 && newCount > 0) {
      indexAdd(idx, hash);
      indexUndo.push(hash, 0);  // 0 = was added, undo by removing
    }
  }

  for (const hStr in undo.persistentOrig) {
    if (!undo.persistentOrig[hStr]) {
      h ^= hashPair(Number(hStr), -1);
    }
  }

  return { ctx: new ExploreContext(idx, h), indexUndo };
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
 * Returns undo log mapping each modified hash to its original value.
 *
 * @param {Object} state - Mutable { linear, persistent }
 * @param {{ [hash: string]: number }} consumed - Consumed linear facts
 * @param {Array} theta - Substitution
 * @param {number[]} linearPatterns - Consequent linear patterns
 * @param {number[]} persistentPatterns - Consequent persistent patterns
 * @returns {{ linearOrig: Object, persistentOrig: Object }}
 */
function mutateState(state, consumed, theta, linearPatterns, persistentPatterns) {
  const linearOrig = {};
  const persistentOrig = {};

  // Consume linear facts
  for (const hStr in consumed) {
    const hash = Number(hStr);
    if (!(hash in linearOrig)) linearOrig[hash] = state.linear[hash] || 0;
    const newCount = (state.linear[hash] || 0) - consumed[hStr];
    if (newCount <= 0) delete state.linear[hash];
    else state.linear[hash] = newCount;
  }

  // Produce linear facts
  for (const pattern of linearPatterns) {
    const h = subApply(pattern, theta);
    if (!(h in linearOrig)) linearOrig[h] = state.linear[h] || 0;
    state.linear[h] = (state.linear[h] || 0) + 1;
  }

  // Produce persistent facts
  for (const pattern of persistentPatterns) {
    const h = subApply(pattern, theta);
    if (!(h in persistentOrig)) {
      persistentOrig[h] = !!state.persistent[h];
    }
    state.persistent[h] = true;
  }

  return { linearOrig, persistentOrig };
}

/**
 * Undo a state mutation by restoring original values.
 */
function undoMutate(state, undo) {
  for (const hStr in undo.linearOrig) {
    const hash = Number(hStr);
    const orig = undo.linearOrig[hStr];
    if (orig > 0) state.linear[hash] = orig;
    else delete state.linear[hash];
  }
  for (const hStr in undo.persistentOrig) {
    if (!undo.persistentOrig[hStr]) {
      delete state.persistent[Number(hStr)];
    }
  }
}

/**
 * Snapshot state (deep copy). Only used at terminal nodes.
 */
function snapshotState(state) {
  return {
    linear: { ...state.linear },
    persistent: { ...state.persistent }
  };
}


// --- Strategy stack ---
//
// A strategy stack partitions rules across layers. Each layer claims rules
// it can index efficiently. Unclaimed rules fall through to the next layer.
// The last layer is always a predicate filter (catch-all).
//
// Layer interface:
//   claims(rule) → bool          — "can I index this rule?"
//   build(rules) → { getCandidateRules(state, stateIndex) → rule[] }

/**
 * Find the current opcode hash from state (PC → code → opcode). O(1).
 * pc(VALUE) → codeByPC[VALUE] → code(PC, OPCODE) → OPCODE
 * @returns {number|null} Opcode hash or null
 */
function findCurrentOpcode(stateIndex) {
  const pcFacts = stateIndex['pc'];
  if (!pcFacts || pcFacts.length !== 1) return null;
  if (Store.arity(pcFacts[0]) < 1) return null;
  const pcValue = Store.child(pcFacts[0], 0);

  // O(1) via codeByPC secondary index
  if (stateIndex.codeByPC) {
    const codeFact = stateIndex.codeByPC[pcValue];
    if (codeFact && Store.arity(codeFact) >= 2) return Store.child(codeFact, 1);
  }

  // Fallback: scan code facts
  const codeFacts = stateIndex['code'];
  if (!codeFacts) return null;
  for (const codeHash of codeFacts) {
    if (Store.arity(codeHash) < 2) continue;
    if (Store.child(codeHash, 0) !== pcValue) continue;
    return Store.child(codeHash, 1);
  }
  return null;
}

/** Opcode layer: O(1) rule lookup by opcode hash. Handles collisions (multiple rules per opcode). */
const opcodeLayer = {
  claims: (rule) => !!rule.opcodeHash,
  build: (rules) => {
    // Multi-value index: opcodeHash → [rule, ...]
    const index = {};
    for (const rule of rules) {
      if (!index[rule.opcodeHash]) index[rule.opcodeHash] = [];
      index[rule.opcodeHash].push(rule);
    }
    return {
      getCandidateRules(state, stateIndex) {
        const opcode = findCurrentOpcode(stateIndex);
        return (opcode && index[opcode]) || [];
      }
    };
  }
};

/** Predicate layer: filters rules by trigger predicates present in state. */
const predicateLayer = {
  claims: () => true,
  build: (rules) => ({
    getCandidateRules(state, stateIndex) {
      const result = [];
      for (const r of rules) {
        const t = r.triggerPreds;
        if (!t || t.length === 0) { result.push(r); continue; }
        let allPresent = true;
        for (let i = 0; i < t.length; i++) {
          const arr = stateIndex[t[i]];
          if (!arr || arr.length === 0) { allPresent = false; break; }
        }
        if (allPresent) result.push(r);
      }
      return result;
    }
  })
};

/**
 * Build a strategy stack from ordered layers.
 * Rules flow through layers; each claims what it can index.
 * Unclaimed rules go to a predicate filter catch-all.
 *
 * @param {Object[]} rules - Compiled rules
 * @param {Object[]} layers - Ordered layer definitions (before catch-all)
 * @returns {{ getCandidateRules: function }}
 */
function buildStrategyStack(rules, layers) {
  const built = [];
  let remaining = rules;

  for (const layer of layers) {
    const claimed = remaining.filter(r => layer.claims(r));
    remaining = remaining.filter(r => !layer.claims(r));
    if (claimed.length > 0) {
      built.push(layer.build(claimed));
    }
  }

  // Catch-all: predicate filter for unclaimed rules
  if (remaining.length > 0) {
    built.push(predicateLayer.build(remaining));
  }

  return {
    getCandidateRules(state, stateIndex) {
      const candidates = [];
      for (const s of built) {
        const c = s.getCandidateRules(state, stateIndex);
        for (let i = 0; i < c.length; i++) candidates.push(c[i]);
      }
      return candidates;
    }
  };
}

/**
 * Auto-detect strategy stack based on rules.
 * @param {Object[]} rules - Compiled rules
 * @returns {{ getCandidateRules: function }}
 */
function detectStrategy(rules) {
  const layers = [];
  if (rules.some(r => r.opcodeHash)) layers.push(opcodeLayer);
  return buildStrategyStack(rules, layers);
}

/**
 * Find all rules that can fire in current state.
 * When stateIndex is provided (from ExploreContext), skips buildStateIndex.
 *
 * @param {Object} state - { linear, persistent }
 * @param {Object} rules - Rule list or { rules } wrapper
 * @param {Object} calc - Calculus context for backward proving
 * @param {Object} [strategy] - Strategy object with getCandidateRules method
 * @param {Object} [stateIndex] - Pre-built state index (from ExploreContext)
 */
// Reusable object to avoid { ...state, index } allocation per findAllMatches call.
// tryMatch only reads .linear, .persistent, .index from this object.
const _indexedState = { linear: null, persistent: null, index: null };

const _matchOpts = { optimizePreserved: true };

function findAllMatches(state, rules, calc, strategy, stateIndex) {
  const idx = stateIndex || buildStateIndex(state.linear);

  _indexedState.linear = state.linear;
  _indexedState.persistent = state.persistent;
  _indexedState.index = idx;

  const candidates = strategy
    ? strategy.getCandidateRules(state, idx)
    : (rules.rules || rules);

  const matches = [];
  for (const rule of candidates) {
    const m = tryMatch(rule, _indexedState, calc, _matchOpts);
    if (m) matches.push(m);
  }
  return matches;
}

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

  // Pre-build rule index and precompute consequent alternatives
  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  const indexedRules = rules.rules ? rules : { rules };
  for (const r of ruleList) {
    if (!r.consequentAlts) r.consequentAlts = expandConsequentChoices(r.consequent);
  }

  // Auto-detect strategy (or use caller-provided one)
  const strategy = opts.strategy || detectStrategy(ruleList);

  // Build backward prover index if needed
  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('../../engine/prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  // DFS with mutation+undo for both state AND index.
  // State, stateIndex, and pathVisited are all mutated in-place during DFS
  // and restored when backtracking. This avoids expensive cloning:
  // - state: mutateState/undoMutate (existing)
  // - stateIndex: makeChildCtx/undoIndexChanges (eliminates 46µs cloneIndex)
  // - pathVisited: add/delete (eliminates new Set() copies)
  // Only terminal nodes (leaf/bound/cycle) snapshot the state.
  // See doc/documentation/symexec-optimizations.md for rationale.
  const pathVisited = new Set();

  function go(depth, ctx) {
    if (pathVisited.has(ctx.stateHash)) {
      return { type: 'cycle', state: snapshotState(state) };
    }

    if (depth >= maxDepth) {
      return { type: 'bound', state: snapshotState(state) };
    }

    const matches = findAllMatches(state, indexedRules, calc, strategy, ctx.stateIndex);

    if (matches.length === 0) {
      return { type: 'leaf', state: snapshotState(state) };
    }

    pathVisited.add(ctx.stateHash);

    const matchAlts = matches.map(m => m.rule.consequentAlts);

    const children = [];
    for (let mi = 0; mi < matches.length; mi++) {
      const m = matches[mi];
      const alts = matchAlts[mi];

      // Filter out preserved consequent patterns (already in state, not consumed)
      const skipPreserved = m.optimized && m.rule.analysis
        ? filterPreserved : null;

      if (alts.length <= 1) {
        const linPats = skipPreserved
          ? skipPreserved(m.rule.consequent.linear || [], m.rule.analysis.preserved)
          : (m.rule.consequent.linear || []);
        const undo = mutateState(state, m.consumed, m.theta,
          linPats, m.rule.consequent.persistent || []);
        const { ctx: childCtx, indexUndo } = makeChildCtx(ctx, state, undo);
        const child = go(depth + 1, childCtx);
        undoIndexChanges(ctx.stateIndex, indexUndo);
        undoMutate(state, undo);
        children.push({ rule: m.rule.name, child });
      } else {
        for (let i = 0; i < alts.length; i++) {
          const linPats = skipPreserved
            ? skipPreserved(alts[i].linear, m.rule.analysis.preserved)
            : alts[i].linear;
          const undo = mutateState(state, m.consumed, m.theta,
            linPats, alts[i].persistent);
          const { ctx: childCtx, indexUndo } = makeChildCtx(ctx, state, undo);
          const child = go(depth + 1, childCtx);
          undoIndexChanges(ctx.stateIndex, indexUndo);
          undoMutate(state, undo);
          children.push({ rule: m.rule.name, choice: i, child });
        }
      }
    }

    pathVisited.delete(ctx.stateHash);

    return { type: 'branch', state: null, children };
  }

  const rootCtx = ExploreContext.fromState(state);
  return go(0, rootCtx);
}

// Tree utilities

function isTerminal(tree) {
  return tree.type === 'leaf' || tree.type === 'bound' || tree.type === 'cycle';
}

function countLeaves(tree) {
  if (isTerminal(tree)) return 1;
  return tree.children.reduce((sum, c) => sum + countLeaves(c.child), 0);
}

function getAllLeaves(tree) {
  if (isTerminal(tree)) return [tree];
  return tree.children.flatMap(c => getAllLeaves(c.child));
}

function maxDepth(tree, d = 0) {
  if (isTerminal(tree)) return d;
  return Math.max(...tree.children.map(c => maxDepth(c.child, d + 1)));
}

function countNodes(tree) {
  if (isTerminal(tree)) return 1;
  return 1 + tree.children.reduce((sum, c) => sum + countNodes(c.child), 0);
}

// --- Step 5: DOT export ---

/**
 * Convert execution tree to DOT (Graphviz) format.
 *
 * @param {Object} tree - Execution tree from explore()
 * @param {Object} [opts]
 * @param {function} [opts.render] - (state) => string label for nodes
 * @returns {string} DOT source
 */
function toDot(tree, opts = {}) {
  const render = opts.render || (() => '');
  const lines = ['digraph exec {'];
  let nextId = 0;

  const colors = { leaf: 'green', bound: 'yellow', cycle: 'red', branch: 'white' };

  function visit(node) {
    const id = nextId++;
    const color = colors[node.type] || 'white';
    const label = node.state ? render(node.state).replace(/"/g, '\\"') : '';
    lines.push(`  n${id} [label="${node.type}${label ? '\\n' + label : ''}" style=filled fillcolor=${color}];`);

    if (node.type === 'branch') {
      for (const c of node.children) {
        const childId = visit(c.child);
        const edgeLabel = c.choice !== undefined
          ? `${c.rule}[${c.choice}]`
          : c.rule;
        lines.push(`  n${id} -> n${childId} [label="${edgeLabel}"];`);
      }
    }
    return id;
  }

  visit(tree);
  lines.push('}');
  return lines.join('\n');
}

module.exports = {
  explore,
  findAllMatches,
  expandItem,
  expandConsequentChoices,
  applyMatchChoice,
  hashState,
  hashStateString,
  toDot,
  countLeaves,
  getAllLeaves,
  maxDepth,
  countNodes,
  buildStrategyStack,
  detectStrategy,
  opcodeLayer,
  predicateLayer,
  // Incremental context + mutation (for benchmarking)
  ExploreContext,
  makeChildCtx,
  undoIndexChanges,
  mutateState,
  undoMutate,
  snapshotState,
  computeNumericHash,
  hashPair,
  cloneIndex
};
