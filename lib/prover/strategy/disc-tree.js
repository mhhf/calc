/**
 * Discrimination Tree for Forward Rule Indexing
 *
 * A trie over preorder traversals of rule trigger patterns.
 * Provides O(pattern_depth) candidate lookup per state fact,
 * replacing the O(R) predicate layer scan at 400+ rules.
 *
 * Insert: flatten pattern to preorder tag sequence (metavars → WILDCARD),
 *         walk trie creating nodes.
 * Query:  flatten ground fact to preorder tag sequence with arity metadata,
 *         walk trie following both concrete and wildcard branches.
 *
 * Multi-antecedent: indexes first linear trigger pattern per rule.
 * Post-filter: verifies all trigger predicates present in state.
 */

const Store = require('../../kernel/store');
const { isMetavar } = require('../../kernel/unify');

const WILDCARD = Symbol('*');

// Shared buffers (non-reentrant, same guarantee as forward.js match)
const _flat = new Array(64);
const _factFlat = new Array(64);
const _factArity = new Array(64);

function createNode() {
  return { children: null, wildcard: null, rules: null };
}

/**
 * Flatten pattern to preorder tag sequence. Metavars → WILDCARD.
 * Only recurses into term children (skips string/bigint children).
 * @param {number} h - Pattern hash
 * @returns {number} Length of flattened sequence in _flat
 */
function flattenPattern(h) {
  let len = 0;
  function walk(hash) {
    if (isMetavar(hash)) { _flat[len++] = WILDCARD; return; }
    const tag = Store.tag(hash);
    if (!tag) { _flat[len++] = hash; return; }
    _flat[len++] = tag;
    const a = Store.arity(hash);
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (Store.isTermChild(c)) walk(c);
    }
  }
  walk(h);
  return len;
}

/**
 * Flatten ground fact to preorder sequence with arity metadata.
 * Only recurses into term children (skips string/bigint children).
 * _factArity[pos] = number of term children (for subtreeSize computation).
 * @param {number} h - Fact hash
 * @returns {number} Length of flattened sequence in _factFlat/_factArity
 */
function flattenFact(h) {
  let len = 0;
  function walk(hash) {
    const tag = Store.tag(hash);
    if (!tag) { _factFlat[len] = hash; _factArity[len] = 0; len++; return; }
    const a = Store.arity(hash);
    // Count term children only (for subtreeSize)
    let termArity = 0;
    for (let i = 0; i < a; i++) {
      if (Store.isTermChild(Store.child(hash, i))) termArity++;
    }
    _factFlat[len] = tag;
    _factArity[len] = termArity;
    len++;
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (Store.isTermChild(c)) walk(c);
    }
  }
  walk(h);
  return len;
}

/**
 * Insert rule into trie indexed on patternHash.
 * @param {Object} root - Trie root node
 * @param {number} patternHash - First linear trigger pattern
 * @param {Object} rule - Compiled rule
 */
function insert(root, patternHash, rule) {
  const len = flattenPattern(patternHash);
  let node = root;
  for (let i = 0; i < len; i++) {
    const sym = _flat[i];
    if (sym === WILDCARD) {
      if (!node.wildcard) node.wildcard = createNode();
      node = node.wildcard;
    } else {
      if (!node.children) node.children = Object.create(null);
      if (!node.children[sym]) node.children[sym] = createNode();
      node = node.children[sym];
    }
  }
  if (!node.rules) node.rules = [];
  node.rules.push(rule);
}

/**
 * Collect all rules reachable from node (for wildcard subtree matches).
 */
function collectAll(node, results) {
  if (node.rules) {
    for (let i = 0; i < node.rules.length; i++) results.push(node.rules[i]);
  }
  if (node.wildcard) collectAll(node.wildcard, results);
  if (node.children) {
    for (const k in node.children) collectAll(node.children[k], results);
  }
}

/**
 * Compute number of flatterm positions spanned by subtree at pos.
 * Uses arity metadata to skip over entire subtrees.
 */
function subtreeSize(pos, len) {
  let remaining = 1, p = pos;
  while (remaining > 0 && p < len) {
    remaining += _factArity[p] - 1;
    p++;
  }
  return p - pos;
}

/**
 * Query: find all rules whose pattern generalizes the ground fact.
 * Follows both concrete and wildcard branches at each position.
 */
function queryFlat(root, factLen, results) {
  _queryFlat(root, 0, factLen, results);
}

function _queryFlat(node, pos, len, results) {
  if (pos >= len) {
    if (node.rules) {
      for (let i = 0; i < node.rules.length; i++) results.push(node.rules[i]);
    }
    return;
  }
  // Wildcard branch: skip entire subtree at this position
  if (node.wildcard) {
    const skip = subtreeSize(pos, len);
    _queryFlat(node.wildcard, pos + skip, len, results);
  }
  // Concrete branch: follow matching tag
  const sym = _factFlat[pos];
  if (node.children && node.children[sym]) {
    _queryFlat(node.children[sym], pos + 1, len, results);
  }
}

/**
 * Strategy layer: discrimination tree catch-all.
 * Claims all rules — replaces predicateLayer as the general-purpose fallback.
 */
function makeDiscTreeLayer() {
  return {
    claims: () => true,
    build: (rules) => {
      const root = createNode();
      // Collect the set of relevant predicates (first trigger pred of each rule).
      // At query time, only iterate facts from these predicates.
      const relevantPreds = new Set();
      for (const rule of rules) {
        const triggers = rule.antecedent.linear;
        if (triggers && triggers.length > 0) {
          insert(root, triggers[0], rule);
          const t = rule.triggerPreds;
          if (t && t.length > 0) relevantPreds.add(t[0]);
        }
      }
      // Also include wildcard roots (rules with all-variable first pattern):
      // these need to scan all facts, tracked by having root.wildcard non-null
      const hasWildcardRoot = root.wildcard !== null;
      const relevantArray = [...relevantPreds];
      return {
        getCandidateRules(state, stateIndex) {
          const results = [];
          const seen = new Set();
          if (hasWildcardRoot) {
            // Must scan all predicates for wildcard-rooted patterns
            for (const pred in stateIndex) {
              if (pred[0] === '_' || pred === '*') continue;
              const facts = stateIndex[pred];
              if (!facts) continue;
              for (let fi = 0; fi < facts.length; fi++) {
                const factLen = flattenFact(facts[fi]);
                queryFlat(root, factLen, results);
              }
            }
          } else {
            // Only scan facts from predicates that appear in indexed patterns
            for (let pi = 0; pi < relevantArray.length; pi++) {
              const facts = stateIndex[relevantArray[pi]];
              if (!facts) continue;
              for (let fi = 0; fi < facts.length; fi++) {
                const factLen = flattenFact(facts[fi]);
                queryFlat(root, factLen, results);
              }
            }
          }
          // Dedup + verify all trigger preds present in state
          const filtered = [];
          for (let i = 0; i < results.length; i++) {
            const r = results[i];
            if (seen.has(r)) continue;
            seen.add(r);
            const t = r.triggerPreds;
            if (!t || t.length === 0) { filtered.push(r); continue; }
            let ok = true;
            for (let j = 0; j < t.length; j++) {
              if (!stateIndex[t[j]] || stateIndex[t[j]].length === 0) { ok = false; break; }
            }
            if (ok) filtered.push(r);
          }
          return filtered;
        }
      };
    }
  };
}

module.exports = {
  createNode,
  insert,
  flattenPattern,
  flattenFact,
  subtreeSize,
  queryFlat,
  collectAll,
  makeDiscTreeLayer,
  WILDCARD
};
