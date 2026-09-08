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

import Store from '../kernel/store.js';
import { predHead } from '../kernel/ast.js';
import { isGround } from './pattern-utils.js';
import { tryMatch, EMPTY_MATCH_OPTS } from './match.js';
// ─── Strategy Stack ─────────────────────────────────────────────────
//
// A strategy stack partitions rules across layers. Each layer claims rules
// it can index efficiently. Unclaimed rules fall through to the next layer.
// The last layer is always a predicate filter (catch-all).
//
// Layer interface:
//   claims(rule) → bool          — "can I index this rule?"
//   build(rules) → { getCandidateRules(state) → rule[] }

/** Predicate layer: filters rules by trigger predicates present in state.
 *  Exported for testing; also the bareStrategy catch-all. */
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
 * The layer-free strategy: every rule flows through the predicate-filter
 * catch-all — same semantics as any index stack, O(R) selection. This is
 * the fallback for direct run/explore callers that pass no engine
 * context (RES_0143 F2: strategy reaches the loops ONLY through
 * engine.buildStrategy or an explicit opts.strategy — the ambient
 * auto-detection hook is gone; profile-driven detection lives in
 * optimizer.js, opt-layer composition in opt/fingerprint.js).
 *
 * @param {Object[]} rules - Compiled rules
 * @returns {{ getCandidateRules: function, fpConfig: null }}
 */
function bareStrategy(rules) {
  const stack = buildStack(rules, []);
  stack.fpConfig = null;
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

export { buildStack, predicateLayer, bareStrategy, findMatch, findAllMatches };
export default { buildStack, predicateLayer, bareStrategy, findMatch, findAllMatches };
