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
  const node = Store.get(h);
  if (!node) return [{ linear: [h], persistent: [] }];

  if (node.tag === 'with') {
    return [
      ...expandItem(node.children[0]),
      ...expandItem(node.children[1])
    ];
  }
  if (node.tag === 'tensor') {
    const lefts = expandItem(node.children[0]);
    const rights = expandItem(node.children[1]);
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
  if (node.tag === 'bang') {
    return [{ linear: [], persistent: [node.children[0]] }];
  }
  // loli(bang(P), monad(Q)) → assume !P, produce Q's resources
  // This handles guarded conditionals like: !neq X Y -o {stack SH 0}
  // In tree exploration we commit to the branch, so assume P and expand Q.
  if (node.tag === 'loli') {
    const guard = Store.get(node.children[0]);
    const body = Store.get(node.children[1]);
    if (guard?.tag === 'bang' && body?.tag === 'monad') {
      const assumption = node.children[0]; // keep the !P as persistent
      const bodyAlts = expandItem(body.children[0]);
      return bodyAlts.map(a => ({
        linear: a.linear,
        persistent: [assumption, ...a.persistent]
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
function applyMatchChoice(state, { theta, consumed }, alt) {
  const newLinear = { ...state.linear };
  for (const [h, count] of Object.entries(consumed)) {
    const hash = Number(h);
    newLinear[hash] -= count;
    if (newLinear[hash] <= 0) delete newLinear[hash];
  }

  for (const pattern of alt.linear) {
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
 * Add a fact hash to a stateIndex (mutates idx).
 */
function indexAdd(idx, h) {
  const pred = getPredicateHead(h);
  if (pred) {
    if (!idx[pred]) idx[pred] = [];
    idx[pred].push(h);
    if (pred === 'code') {
      const node = Store.get(h);
      if (node && node.tag === 'app') {
        const left = Store.get(node.children[0]);
        if (left && left.tag === 'app') {
          if (!idx.codeByPC) idx.codeByPC = {};
          idx.codeByPC[left.children[1]] = h;
        }
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
      const node = Store.get(h);
      if (node && node.tag === 'app') {
        const left = Store.get(node.children[0]);
        if (left && left.tag === 'app') {
          const pcValue = left.children[1];
          if (idx.codeByPC[pcValue] === h) delete idx.codeByPC[pcValue];
        }
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
 * Reads undo.linearOrig for old counts and current (mutated) state for new counts.
 *
 * @param {ExploreContext} parentCtx
 * @param {Object} state - Already-mutated state (current counts)
 * @param {{ linearOrig: Object, persistentOrig: Object }} undo - Undo log from mutateState
 * @param {boolean} needsClone - Whether to clone the index (branching)
 * @returns {ExploreContext}
 */
function makeChildCtx(parentCtx, state, undo, needsClone) {
  const idx = needsClone ? cloneIndex(parentCtx.stateIndex) : parentCtx.stateIndex;
  let h = parentCtx.stateHash;

  for (const hStr in undo.linearOrig) {
    const hash = Number(hStr);
    const oldCount = undo.linearOrig[hStr];
    const newCount = state.linear[hash] || 0;
    if (oldCount === newCount) continue;
    if (oldCount > 0) h ^= hashPair(hash, oldCount);
    if (newCount > 0) h ^= hashPair(hash, newCount);
    if (oldCount > 0 && newCount <= 0) indexRemove(idx, hash);
    else if (oldCount <= 0 && newCount > 0) indexAdd(idx, hash);
  }

  for (const hStr in undo.persistentOrig) {
    if (!undo.persistentOrig[hStr]) {
      h ^= hashPair(Number(hStr), -1);
    }
  }

  return new ExploreContext(idx, h);
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
 * Find the current opcode hash from state (PC → code → opcode).
 * @returns {number|null} Opcode hash or null
 */
function findCurrentOpcode(stateIndex) {
  const pcFacts = stateIndex['pc'];
  if (!pcFacts || pcFacts.length !== 1) return null;
  const pcNode = Store.get(pcFacts[0]);
  if (!pcNode || pcNode.tag !== 'app') return null;
  const pcValue = pcNode.children[1];

  // O(1) via codeByPC secondary index
  if (stateIndex.codeByPC) {
    const codeFact = stateIndex.codeByPC[pcValue];
    if (codeFact) {
      const codeNode = Store.get(codeFact);
      if (codeNode && codeNode.tag === 'app') return codeNode.children[1];
    }
  }

  // Fallback: scan code facts
  const codeFacts = stateIndex['code'];
  if (!codeFacts) return null;
  for (const codeHash of codeFacts) {
    const codeNode = Store.get(codeHash);
    if (!codeNode || codeNode.tag !== 'app') continue;
    const left = Store.get(codeNode.children[0]);
    if (!left || left.tag !== 'app') continue;
    if (left.children[1] !== pcValue) continue;
    return codeNode.children[1];
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
      const preds = new Set(
        Object.entries(stateIndex)
          .filter(([k, v]) => k !== 'codeByPC' && Array.isArray(v) && v.length > 0)
          .map(([k]) => k)
      );
      return rules.filter(r => {
        const t = r.triggerPreds || [];
        return t.length === 0 || t.every(p => preds.has(p));
      });
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
function findAllMatches(state, rules, calc, strategy, stateIndex) {
  const idx = stateIndex || buildStateIndex(state.linear);
  const indexedState = { ...state, index: idx };

  const candidates = strategy
    ? strategy.getCandidateRules(state, idx)
    : (rules.rules || rules);

  const matches = [];
  for (const rule of candidates) {
    const m = tryMatch(rule, indexedState, calc);
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

  // Pre-build rule index
  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  const indexedRules = rules.rules ? rules : { rules };

  // Auto-detect strategy (or use caller-provided one)
  const strategy = opts.strategy || detectStrategy(ruleList);

  // Build backward prover index if needed
  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('../../engine/prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  // DFS with mutation+undo: state is mutated in-place, then restored after each child.
  // Only terminal nodes (leaf/bound/cycle) snapshot the state.
  function go(depth, pathVisited, ctx) {
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

    const nextVisited = new Set(pathVisited);
    nextVisited.add(ctx.stateHash);

    // Pre-expand choices and count total children for clone decision
    const matchAlts = matches.map(m => expandConsequentChoices(m.rule.consequent));
    let totalChildren = 0;
    for (const alts of matchAlts) {
      totalChildren += alts.length <= 1 ? 1 : alts.length;
    }
    const needsClone = totalChildren > 1;

    const children = [];
    for (let mi = 0; mi < matches.length; mi++) {
      const m = matches[mi];
      const alts = matchAlts[mi];

      if (alts.length <= 1) {
        const undo = mutateState(state, m.consumed, m.theta,
          m.rule.consequent.linear || [], m.rule.consequent.persistent || []);
        const childCtx = makeChildCtx(ctx, state, undo, needsClone);
        const child = go(depth + 1, nextVisited, childCtx);
        undoMutate(state, undo);
        children.push({ rule: m.rule.name, child });
      } else {
        for (let i = 0; i < alts.length; i++) {
          const undo = mutateState(state, m.consumed, m.theta,
            alts[i].linear, alts[i].persistent);
          const childCtx = makeChildCtx(ctx, state, undo, needsClone);
          const child = go(depth + 1, nextVisited, childCtx);
          undoMutate(state, undo);
          children.push({ rule: m.rule.name, choice: i, child });
        }
      }
    }

    return { type: 'branch', state: null, children };
  }

  const rootCtx = ExploreContext.fromState(state);
  return go(0, new Set(), rootCtx);
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
  mutateState,
  undoMutate,
  snapshotState,
  computeNumericHash,
  hashPair,
  cloneIndex
};
