/**
 * Fingerprint indexing — O(1) rule selection by ground discriminator
 * value (Opt: first-argument fingerprinting).
 *
 * The whole fingerprint stack lives here (RES_0143 M5 — it was
 * historically co-located with the matcher and the forward loop):
 *
 *   fpDetect   — auto-detect the dominant discriminator + pointer preds
 *   fpValue    — read the current fingerprint value from a state
 *   fpLayer    — the strategy-stack layer (claims discriminator rules)
 *   attachPred — Opt_H threaded-code prediction metadata on rules
 *   buildFingerprintIndex — the per-state secondary index (_byKey)
 *   detectStrategy — the all-layers stack for direct callers; engine-
 *                mediated runs get their stack from engine.buildStrategy
 *                (optimizer.js) — the one channel (RES_0143 F2).
 *
 * Soundness notes ride the functions (functional-key sentinel, ambiguity
 * degradation — TODO_0309 P0 findings 1–3).
 */

import Store from '../../kernel/store.js';
import { predHead } from '../../kernel/ast.js';
import { isGround } from '../pattern-utils.js';
import { makeDiscTreeLayer } from './disc-tree.js';
import { buildStack } from '../strategy.js';

/** Map discriminator ground value → [rule, ...] for O(1) lookup */
function discIndex(rules) {
  const index = {};
  for (const rule of rules) {
    if (!rule.discriminator) continue;
    const gv = rule.discriminator.groundValue;
    if (gv != null) {
      if (!index[gv]) index[gv] = [];
      index[gv].push(rule);
    }
  }
  return index;
}

/**
 * Auto-detect fingerprint configuration from compiled rules.
 * Finds dominant discriminator predicate and pointer predicate.
 * Two-pass (count discriminators, then find pointers) — runs once at startup.
 */
function fpDetect(rules) {
  const discCounts = {};
  for (const r of rules) {
    if (r.discriminator) {
      const key = r.discriminator.pred;
      discCounts[key] = (discCounts[key] || 0) + 1;
    }
  }

  let bestPred = null, bestCount = 0;
  for (const pred in discCounts) {
    if (discCounts[pred] > bestCount) {
      bestPred = pred;
      bestCount = discCounts[pred];
    }
  }
  if (!bestPred || bestCount < 2) return null;

  const sample = rules.find(r => r.discriminator && r.discriminator.pred === bestPred);
  const { groundPos, keyPos } = sample.discriminator;

  // Virtual discriminator: pointerPred and arrayPred stored directly
  if (sample.discriminator.type === 'virtual') {
    return {
      type: 'virtual',
      pred: bestPred,
      keyPos,
      groundPos,
      pointerPred: sample.discriminator.pointerPred,
      arrayPred: sample.discriminator.arrayPred,
      buildIndex: buildFingerprintIndex,
    };
  }

  // Auto-detect pointer predicate (unary pattern sharing a var with discriminator key)
  let pointerPred = null;
  for (const r of rules) {
    if (!r.discriminator || r.discriminator.pred !== bestPred) continue;
    for (const lp of (r.antecedent.linear || [])) {
      if (predHead(lp) !== bestPred) continue;
      const keyVar = Store.child(lp, keyPos);
      if (Store.tag(keyVar) !== 'metavar') continue;
      for (const lp2 of (r.antecedent.linear || [])) {
        if (lp2 === lp) continue;
        const pred2 = predHead(lp2);
        if (pred2 && Store.arity(lp2) === 1 && Store.child(lp2, 0) === keyVar) {
          pointerPred = pred2;
          break;
        }
      }
      if (pointerPred) break;
    }
    if (pointerPred) break;
  }

  // Self-pointer: unary discriminator where keyPos === groundPos (e.g., pc(0x0))
  // The predicate IS its own pointer — state lookup extracts value from same position
  if (!pointerPred && keyPos === groundPos) {
    pointerPred = bestPred;
  }

  return { pred: bestPred, keyPos, groundPos, pointerPred, buildIndex: buildFingerprintIndex };
}

/**
 * Look up the fingerprint discriminator value from state using fpConfig.
 * Works for any program with a pointer predicate and discriminator predicate.
 */
function fpValue(state, fpConfig) {
  if (!fpConfig || !fpConfig.pointerPred) return null;

  // Step 1: Get pointer fact (e.g., pc(VALUE) — must be exactly one)
  const pointerTagId = Store.TAG[fpConfig.pointerPred];
  if (pointerTagId === undefined) return null;
  const pointerGroup = state.linear.group(pointerTagId);
  if (pointerGroup.length !== 1) return null;
  if (Store.arity(pointerGroup[0]) < 1) return null;
  const keyValue = Store.child(pointerGroup[0], 0);

  // Virtual fingerprint: O(1) ARRAY_TABLE lookup or O(log N) trie navigation
  if (fpConfig.type === 'virtual') {
    const arrayTagId = Store.TAG[fpConfig.arrayPred];
    if (arrayTagId === undefined) return null;
    const arrayGroup = state.linear.group(arrayTagId);
    if (arrayGroup.length !== 1) return null;
    const arrayHash = Store.child(arrayGroup[0], 0);
    const lookup = fpConfig.lookupArrayValue;
    if (!lookup) return null;  // No domain-specific lookup — degrade to full matching
    return lookup(keyValue, arrayHash);
  }

  // Step 2: O(1) lookup via secondary index (e.g., _byKey[pcValue] → code fact)
  if (state._byKey) {
    const fact = state._byKey[keyValue];
    if (fact && Store.arity(fact) > fpConfig.groundPos) {
      return Store.child(fact, fpConfig.groundPos);
    }
  }

  // Fallback: scan facts of discriminator predicate. The fingerprint is
  // only sound when the key selects a UNIQUE discriminator value — with
  // several discriminator facts under one key (SAX-style states,
  // TODO_0309) committing to one would hide the other facts' rules from
  // the candidate set, so ambiguity degrades to null (all claimed rules).
  const discTagId = Store.TAG[fpConfig.pred];
  if (discTagId === undefined) return null;
  const discGroup = state.linear.group(discTagId);
  let found = null;
  for (let i = 0; i < discGroup.length; i++) {
    const h = discGroup[i];
    if (Store.arity(h) <= fpConfig.keyPos) continue;
    if (Store.child(h, fpConfig.keyPos) !== keyValue) continue;
    const gv = Store.child(h, fpConfig.groundPos);
    if (found !== null && gv !== found) return null;
    found = gv;
  }
  return found;
}

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

/** Build secondary fingerprint index on state.
 *  The index is only sound when key → fact is FUNCTIONAL. A key carried
 *  by two distinct discriminator facts (SAX-style states: several `proc`
 *  facts under one destination, TODO_0309) is marked with the 0 sentinel
 *  — falsy, so both consumers (fpValue step 2, matchLinear1 strategy B)
 *  fall through to complete scanning instead of committing to an
 *  arbitrary winner. */
function buildFingerprintIndex(state, fpConfig) {
  const fpTagId = Store.TAG[fpConfig.pred];
  state._byKey = {};
  if (fpTagId !== undefined) {
    const grp = state.linear.group(fpTagId);
    for (let i = 0; i < grp.length; i++) {
      const h = grp[i];
      if (Store.arity(h) > fpConfig.keyPos) {
        const key = Store.child(h, fpConfig.keyPos);
        const prev = state._byKey[key];
        state._byKey[key] = prev !== undefined && prev !== h ? 0 : h;
      }
    }
  }
}

/**
 * All-layers strategy stack for DIRECT callers (tests, benchmarks,
 * tools that bypass the engine context): fingerprint layer (when a
 * dominant discriminator exists) + prediction metadata + disc-tree
 * catch-all — the same stack the 'full' profile builds through
 * engine.buildStrategy (optimizer.js), which is the ONE channel for
 * engine-mediated runs (RES_0143 F2).
 */
function detectStrategy(rules) {
  const layers = [];
  const fpConfig = fpDetect(rules);
  if (fpConfig) {
    layers.push(fpLayer(fpConfig));
    attachPred(rules, fpConfig);
  }
  layers.push(makeDiscTreeLayer());
  const stack = buildStack(rules, layers);
  stack.fpConfig = fpConfig;
  return stack;
}

export { discIndex, fpDetect, fpValue, fpLayer, attachPred, buildFingerprintIndex, detectStrategy };
export default { discIndex, fpDetect, fpValue, fpLayer, attachPred, buildFingerprintIndex, detectStrategy };
