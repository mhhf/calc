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
const { predHead } = require('../kernel/ast');
const { isGround } = require('./pattern-utils');
const {
  tryMatch,
  fpDetect,
  fpValue,
  EMPTY_MATCH_OPTS,
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
function fpLayer(fpConfig) {
  return {
    claims: (rule) => !!(rule.discriminator && rule.discriminator.pred === fpConfig.pred),
    build: (rules) => {
      const index = {};
      for (const rule of rules) {
        const gv = rule.discriminator.groundValue;
        if (gv != null) {
          if (!index[gv]) index[gv] = [];
          index[gv].push(rule);
        }
      }
      return {
        getCandidateRules(state) {
          const fpVal = fpValue(state, fpConfig);
          if (fpVal == null) return rules;  // Can't compute fingerprint — try all claimed rules
          return index[fpVal] || [];
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
function buildStack(rules, layers) {
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
 * @param {Object} fpConfig - Fingerprint config from fpDetect
 */
function attachPred(rules, fpConfig) {
  if (!fpConfig || !fpConfig.pointerPred) return;

  const pointerPred = fpConfig.pointerPred;

  for (const rule of rules) {
    if (!rule.discriminator || rule.discriminator.pred !== fpConfig.pred) continue;
    if (rule.consequentAlts.length !== 1) continue;

    const alt = rule.consequentAlts[0];
    for (const p of alt.linear) {
      const pred = predHead(p);
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
 * Uses fpDetect to find the dominant discriminator predicate,
 * then builds a fingerprint layer for O(1) rule lookup. Falls back to
 * predicate-only filtering if no discriminator is found.
 *
 * @param {Object[]} rules - Compiled rules
 * @returns {{ getCandidateRules: function, fpConfig: Object|null }}
 */
function detectStrategy(rules) {
  const layers = [];
  const fpConfig = fpDetect(rules);
  if (fpConfig) {
    layers.push(fpLayer(fpConfig));
    attachPred(rules, fpConfig);
  }
  layers.push(makeDiscTreeLayer());  // replaces predicateLayer as catch-all
  const stack = buildStack(rules, layers);
  stack.fpConfig = fpConfig;
  return stack;
}

// ─── Match Selection ────────────────────────────────────────────────

/**
 * Find first matching rule (committed choice for forward.run).
 * Uses strategy stack (same as findAllMatches) for unified rule selection.
 * State is a FactSet-based State object.
 *
 * Contract: matchOpts is always the frozen 20-field record produced by
 * buildMatchOpts. EMPTY_MATCH_OPTS is the canonical empty default,
 * so direct callers (tests, benchmarks) can omit the argument.
 */
function findMatch(state, rules, calc, matchOpts = EMPTY_MATCH_OPTS) {
  const strat = rules.strategy;
  const candidates = strat
    ? strat.getCandidateRules(state)
    : (rules.rules || rules);

  for (const rule of candidates) {
    const m = tryMatch(rule, state, calc, matchOpts);
    if (m) return m;
  }

  // Dynamic rules (e.g., loli continuations) — generic iteration
  if (matchOpts.dynamicRuleTag && matchOpts.matchDynamicRule) {
    const tagId = Store.TAG[matchOpts.dynamicRuleTag];
    if (tagId !== undefined) {
      const group = state.linear.group(tagId);
      for (let i = 0; i < group.length; i++) {
        const m = matchOpts.matchDynamicRule(group[i], state, calc, matchOpts);
        if (m) return m;
      }
    }
  }

  return null;
}

/**
 * Find all rules that can fire in current state (exhaustive for explore.explore).
 * Includes loli continuation scanning.
 * State is a FactSet-based State object.
 *
 * Contract: matchOpts is always the frozen 20-field record produced by
 * buildMatchOpts. EMPTY_MATCH_OPTS is the canonical empty default.
 *
 * @param {State} state - FactSet-based State object
 * @param {Object} rules - Rule list or { rules } wrapper
 * @param {Object} calc - Calculus context for backward proving
 * @param {Object} [strategy] - Strategy object with getCandidateRules method
 * @param {Object} [matchOpts] - Frozen match options (defaults to EMPTY_MATCH_OPTS)
 */
function findAllMatches(state, rules, calc, strategy, matchOpts = EMPTY_MATCH_OPTS) {
  const candidates = strategy
    ? strategy.getCandidateRules(state)
    : (rules.rules || rules);

  const matches = [];
  for (const rule of candidates) {
    const m = tryMatch(rule, state, calc, matchOpts);
    if (m) matches.push(m);
  }

  // Dynamic rules (e.g., loli continuations) — generic iteration
  if (matchOpts.dynamicRuleTag && matchOpts.matchDynamicRule) {
    const tagId = Store.TAG[matchOpts.dynamicRuleTag];
    if (tagId !== undefined) {
      const group = state.linear.group(tagId);
      for (let li = 0; li < group.length; li++) {
        const lm = matchOpts.matchDynamicRule(group[li], state, calc, matchOpts);
        if (lm) matches.push(lm);
      }
    }
  }

  return matches;
}

module.exports = {
  // Strategy stack
  fpLayer,
  predicateLayer,
  buildStack,
  detectStrategy,
  attachPred,
  makeDiscTreeLayer,
  // Match selection
  findMatch,
  findAllMatches,
};
