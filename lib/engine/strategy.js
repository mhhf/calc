/**
 * Rule selection strategies for forward chaining.
 *
 * Strategy stack: fingerprint → disc-tree → predicate (catch-all).
 * Contains:
 *   - Strategy layers (fingerprint, disc-tree, predicate)
 *   - Strategy stack builder and auto-detection
 *   - findMatch (committed choice for forward.run)
 *   - findAllMatches (exhaustive for symexec.explore)
 */

const Store = require('../kernel/store');
const _TAG_LOLI = Store.TAG.loli;
const {
  tryMatch,
  buildStateIndex,
  detectFingerprintConfig,
  findFingerprintValue,
  matchLoli,
} = require('./match');
const { makeDiscTreeLayer } = require('./disc-tree');

// ─── Strategy Stack ─────────────────────────────────────────────────
//
// A strategy stack partitions rules across layers. Each layer claims rules
// it can index efficiently. Unclaimed rules fall through to the next layer.
// The last layer is always a predicate filter (catch-all).
//
// Layer interface:
//   claims(rule) → bool          — "can I index this rule?"
//   build(rules) → { getCandidateRules(state, stateIndex) → rule[] }

/**
 * Fingerprint layer: O(1) rule lookup by ground discriminator value.
 * Works for any program with a discriminating ground child in a binary+ predicate pattern.
 *
 * @param {Object} fpConfig - Fingerprint config (pred, keyPos, groundPos, pointerPred)
 * @returns {Object} Layer with claims/build methods
 */
function makeFingerprintLayer(fpConfig) {
  return {
    claims: (rule) => !!(rule.discriminator && rule.discriminator.pred === fpConfig.pred),
    build: (rules) => {
      // Multi-value index: groundValue → [rule, ...]
      const index = {};
      for (const rule of rules) {
        const gv = rule.discriminator.groundValue;
        if (!index[gv]) index[gv] = [];
        index[gv].push(rule);
      }
      return {
        getCandidateRules(state, stateIndex) {
          const fpValue = findFingerprintValue(stateIndex, fpConfig);
          return (fpValue && index[fpValue]) || [];
        }
      };
    }
  };
}

/** Predicate layer: filters rules by trigger predicates present in state.
 *  Exported for testing. Disc-tree is now the default catch-all (see detectStrategy). */
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
 *
 * Uses detectFingerprintConfig to find the dominant discriminator predicate,
 * then builds a fingerprint layer for O(1) rule lookup. Falls back to
 * predicate-only filtering if no discriminator is found.
 *
 * @param {Object[]} rules - Compiled rules
 * @returns {{ getCandidateRules: function, fpConfig: Object|null }}
 */
function detectStrategy(rules) {
  const layers = [];
  const fpConfig = detectFingerprintConfig(rules);
  if (fpConfig) {
    layers.push(makeFingerprintLayer(fpConfig));
  }
  layers.push(makeDiscTreeLayer());  // replaces predicateLayer as catch-all
  const stack = buildStrategyStack(rules, layers);
  stack.fpConfig = fpConfig;
  return stack;
}

// ─── Match Selection ────────────────────────────────────────────────

// Reusable objects to avoid allocation per call.
// tryMatch only reads .linear, .persistent, .index from these.
const _findMatchState = { linear: null, persistent: null, index: null };
const _indexedState = { linear: null, persistent: null, index: null };
const _matchOpts = { optimizePreserved: true };

/** Find first matching rule (committed choice for forward.run) */
function findMatch(state, rules, calc, matchOpts) {
  const stateIndex = buildStateIndex(state.linear, rules.fpConfig || null, state.persistent);
  _findMatchState.linear = state.linear;
  _findMatchState.persistent = state.persistent;
  _findMatchState.index = stateIndex;

  const ruleList = rules.rules || rules;
  const discriminatorIndex = rules.discriminatorIndex || null;

  // Strategy 1: Fingerprint O(1) lookup
  if (discriminatorIndex && rules.fpConfig) {
    const fpValue = findFingerprintValue(stateIndex, rules.fpConfig);
    const candidates = fpValue != null && discriminatorIndex[fpValue];
    if (candidates) {
      for (const rule of candidates) {
        const m = tryMatch(rule, _findMatchState, calc, matchOpts);
        if (m) return m;
      }
    }
  }

  // Strategy 2: Predicate filtering + try all
  for (const rule of ruleList) {
    const triggers = rule.triggerPreds;
    if (triggers && triggers.length > 0) {
      let allPresent = true;
      for (let i = 0; i < triggers.length; i++) {
        const arr = stateIndex[triggers[i]];
        if (!arr || arr.length === 0) { allPresent = false; break; }
      }
      if (!allPresent) continue;
    }
    const m = tryMatch(rule, _findMatchState, calc, matchOpts);
    if (m) return m;
  }
  return null;
}

/**
 * Find all rules that can fire in current state (exhaustive for symexec.explore).
 * Includes loli continuation scanning.
 *
 * @param {Object} state - { linear, persistent }
 * @param {Object} rules - Rule list or { rules } wrapper
 * @param {Object} calc - Calculus context for backward proving
 * @param {Object} [strategy] - Strategy object with getCandidateRules method
 * @param {Object} [stateIndex] - Pre-built state index (from ExploreContext)
 */
function findAllMatches(state, rules, calc, strategy, stateIndex) {
  const idx = stateIndex || buildStateIndex(state.linear, null, state.persistent);

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

  // Scan for fireable loli continuations (equal priority with compiled rules)
  for (const hStr of Object.keys(state.linear)) {
    const h = Number(hStr);
    if (Store.tagId(h) !== _TAG_LOLI) continue;
    const lm = matchLoli(h, state, calc);
    if (lm) matches.push(lm);
  }

  return matches;
}

module.exports = {
  // Strategy stack
  makeFingerprintLayer,
  predicateLayer,
  buildStrategyStack,
  detectStrategy,
  makeDiscTreeLayer,
  // Match selection
  findMatch,
  findAllMatches,
};
