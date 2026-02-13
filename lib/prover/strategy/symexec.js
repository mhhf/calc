/**
 * Execution Tree Exploration
 *
 * Explores all forward chaining executions up to a depth bound.
 * Returns a tree of all reachable states.
 *
 * Tree structure:
 *   { type: 'leaf', state }           - quiescent (no rules fire)
 *   { type: 'branch', state, children } - nondeterministic choice
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
  applyMatch,
  buildStateIndex,
  buildRuleIndex
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
 * Hash a state deterministically for cycle detection.
 * Sorts linear {hash:count} entries + persistent keys.
 */
function hashState(state) {
  const linParts = Object.entries(state.linear || {})
    .filter(([, c]) => c > 0)
    .sort(([a], [b]) => a - b)
    .map(([h, c]) => `${h}:${c}`);
  const persParts = Object.keys(state.persistent || {})
    .sort((a, b) => a - b);
  return `L[${linParts.join(',')}]P[${persParts.join(',')}]`;
}

/**
 * Find all rules that can fire in current state
 * Returns array of matches (one per rule that can fire)
 */
function findAllMatches(state, rules, calc) {
  const stateIndex = buildStateIndex(state.linear);
  const indexedState = { ...state, index: stateIndex };
  const ruleList = rules.rules || rules;

  const matches = [];
  for (const rule of ruleList) {
    const m = tryMatch(rule, indexedState, calc);
    if (m) matches.push(m);
  }
  return matches;
}

/**
 * Explore all execution paths up to depth bound.
 * Handles rule-level nondeterminism AND additive choice in consequents.
 * Uses path-based cycle detection (back-edges only, not joins).
 */
function explore(state, rules, opts = {}) {
  const maxDepth = opts.maxDepth ?? 100;
  const calc = opts.calc ?? null;

  // Pre-build rule index
  const indexedRules = rules.rules ? rules : { rules };

  // Build backward prover index if needed
  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('../../engine/prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  function go(state, depth, pathVisited) {
    // Cycle detection: check if we've seen this state on the current path
    const sh = hashState(state);
    if (pathVisited.has(sh)) {
      return { type: 'cycle', state };
    }

    if (depth >= maxDepth) {
      return { type: 'bound', state };
    }

    const matches = findAllMatches(state, indexedRules, calc);

    if (matches.length === 0) {
      return { type: 'leaf', state };
    }

    const nextVisited = new Set(pathVisited);
    nextVisited.add(sh);

    const children = [];
    for (const m of matches) {
      const alts = expandConsequentChoices(m.rule.consequent);
      if (alts.length <= 1) {
        // No additive choice — use original applyMatch
        children.push({
          rule: m.rule.name,
          child: go(applyMatch(state, m), depth + 1, nextVisited)
        });
      } else {
        // Fork: one child per choice alternative
        for (let i = 0; i < alts.length; i++) {
          children.push({
            rule: m.rule.name,
            choice: i,
            child: go(applyMatchChoice(state, m, alts[i]), depth + 1, nextVisited)
          });
        }
      }
    }

    return { type: 'branch', state, children };
  }

  return go(state, 0, new Set());
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
    const label = render(node.state).replace(/"/g, '\\"');
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
  toDot,
  countLeaves,
  getAllLeaves,
  maxDepth,
  countNodes
};
