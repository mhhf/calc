/**
 * Rule selection strategies for forward chaining.
 *
 * Strategy stack: fingerprint → disc-tree → predicate (catch-all).
 * Contains:
 *   - Strategy layers (fingerprint, disc-tree, predicate)
 *   - Strategy stack builder and auto-detection
 *   - findMatch (committed choice for forward.run)
 *   - findAllMatches (exhaustive for explore.explore)
 *
 * State is a FactSet-based State object (lib/engine/fact-set.js).
 * No separate stateIndex — State IS the index.
 */

const Store = require('../kernel/store');
const { getPredicateHead } = require('../kernel/ast');
const { isGround } = require('./pattern-utils');
const {
  tryMatch,
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
//   build(rules) → { getCandidateRules(state) → rule[] }

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
        getCandidateRules(state) {
          const fpValue = findFingerprintValue(state, fpConfig);
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
    getCandidateRules(state) {
      const result = [];
      for (const r of rules) {
        const t = r.triggerPreds;
        if (!t || t.length === 0) { result.push(r); continue; }
        let allPresent = true;
        for (let i = 0; i < t.length; i++) {
          if (!state.hasPredicate(t[i])) { allPresent = false; break; }
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
    getCandidateRules(state) {
      const candidates = [];
      for (const s of built) {
        const c = s.getCandidateRules(state);
        for (let i = 0; i < c.length; i++) candidates.push(c[i]);
      }
      return candidates;
    }
  };
}

/**
 * Attach prediction metadata to rules for Opt_H threaded code.
 *
 * For each rule with a fingerprint discriminator and single consequent alt,
 * finds the pointer predicate pattern (e.g., pc(X)) in the consequent.
 * Records the metavar slot that will hold the new pointer value after firing.
 *
 * @param {Object[]} rules - Compiled rules
 * @param {Object} fpConfig - Fingerprint config from detectFingerprintConfig
 */
function attachPredictions(rules, fpConfig) {
  if (!fpConfig || !fpConfig.pointerPred) return;

  const pointerPred = fpConfig.pointerPred;

  for (const rule of rules) {
    if (!rule.discriminator || rule.discriminator.pred !== fpConfig.pred) continue;
    if (rule.consequentAlts.length !== 1) continue;

    const alt = rule.consequentAlts[0];
    for (const p of alt.linear) {
      const pred = getPredicateHead(p);
      if (pred !== pointerPred) continue;
      if (Store.arity(p) !== 1) continue;

      const child = Store.child(p, 0);
      const slot = rule.metavarSlots[child];
      if (slot !== undefined) {
        rule.nextPointerSlot = slot;
      } else if (isGround(child)) {
        rule.nextPointerSlot = -1;
        rule.nextPointerValue = child;
      }
      break;
    }
  }
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
    attachPredictions(rules, fpConfig);
  }
  layers.push(makeDiscTreeLayer());  // replaces predicateLayer as catch-all
  const stack = buildStrategyStack(rules, layers);
  stack.fpConfig = fpConfig;
  return stack;
}

// ─── Match Selection ────────────────────────────────────────────────

const _matchOpts = { optimizePreserved: true };

/**
 * Find first matching rule (committed choice for forward.run).
 * State is a FactSet-based State object.
 */
function findMatch(state, rules, calc, matchOpts) {
  // Build secondary index for fingerprint if needed (skip for virtual — uses ARRAY_TABLE)
  if (rules.fpConfig && rules.fpConfig.type !== 'virtual' && !state._byKey) {
    state._fpPred = rules.fpConfig.pred;
    state._fpKeyPos = rules.fpConfig.keyPos;
    const fpTagId = Store.TAG[rules.fpConfig.pred];
    state._byKey = {};
    if (fpTagId !== undefined) {
      const grp = state.linear.group(fpTagId);
      for (let i = 0; i < grp.length; i++) {
        const h = grp[i];
        if (Store.arity(h) > rules.fpConfig.keyPos) {
          state._byKey[Store.child(h, rules.fpConfig.keyPos)] = h;
        }
      }
    }
  }

  const ruleList = rules.rules || rules;
  const discriminatorIndex = rules.discriminatorIndex || null;

  // Strategy 1: Fingerprint O(1) lookup
  if (discriminatorIndex && rules.fpConfig) {
    const fpValue = findFingerprintValue(state, rules.fpConfig);
    const candidates = fpValue != null && discriminatorIndex[fpValue];
    if (candidates) {
      for (const rule of candidates) {
        const m = tryMatch(rule, state, calc, matchOpts);
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
        if (!state.hasPredicate(triggers[i])) { allPresent = false; break; }
      }
      if (!allPresent) continue;
    }
    const m = tryMatch(rule, state, calc, matchOpts);
    if (m) return m;
  }
  return null;
}

/**
 * Find all rules that can fire in current state (exhaustive for explore.explore).
 * Includes loli continuation scanning.
 * State is a FactSet-based State object.
 *
 * @param {State} state - FactSet-based State object
 * @param {Object} rules - Rule list or { rules } wrapper
 * @param {Object} calc - Calculus context for backward proving
 * @param {Object} [strategy] - Strategy object with getCandidateRules method
 */
function findAllMatches(state, rules, calc, strategy) {
  const candidates = strategy
    ? strategy.getCandidateRules(state)
    : (rules.rules || rules);

  const matches = [];
  for (const rule of candidates) {
    const m = tryMatch(rule, state, calc, _matchOpts);
    if (m) matches.push(m);
  }

  // Scan for fireable loli continuations
  const loliTagId = Store.TAG[calc?.roles?.implication || 'loli'];
  const loliGroup = state.linear.group(loliTagId);
  for (let li = 0; li < loliGroup.length; li++) {
    const lm = matchLoli(loliGroup[li], state, calc);
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
  attachPredictions,
  makeDiscTreeLayer,
  // Match selection
  findMatch,
  findAllMatches,
};
