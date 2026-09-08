/**
 * L2 Generic Prover - Search Primitives
 *
 * Extracted from focused/prover.js. Contains ALL generic proof
 * utilities that are independent of focusing discipline:
 *
 * - Helpers: connective, isPositive, isNegative, ruleName, ruleIsInvertible
 * - Core: tryIdentity, applyRule, childDelta, addDelta
 * - Search: applicableRules
 *
 * The focused prover (L3) and manual prover (L4a) import from here.
 */

import Context from './context.js';
import Seq from '../kernel/sequent.js';
import Store from '../kernel/store.js';
import { unify } from '../kernel/unify.js';
import { isAtomic } from '../kernel/ast.js';
/**
 * Create a generic prover for a calculus
 * @param {Object} calculus - Loaded calculus with polarity, rules, etc.
 */
function createGenericProver(calculus) {
  // Zone names from the calculus's declared structure (TODO_0086).
  const ctxStruct = calculus.contextStructure || Seq.DEFAULT_CONTEXT_STRUCTURE;
  const CZ = ctxStruct.consumableZone;
  // Union pool over ALL consumable zones (TODO_0285): aux-zone entries
  // are wrapper-tagged, so the pool is hash-disjoint and Context deltas
  // stay zone-blind. With one consumable zone this IS the CZ array.
  const pool = (seq) => Seq.consumablePool(seq, ctxStruct);
  const singleCZ = !ctxStruct.consumableZones || ctxStruct.consumableZones.length === 1;
  const { isPositive: calcIsPositive, isNegative: calcIsNegative } = calculus;

  // =========================================================================
  // Helpers
  // =========================================================================

  /** Get connective from formula hash (null for atoms/vars) */
  const connective = (h) => {
    const tag = Store.tag(h);
    if (!tag || tag === 'atom' || tag === 'freevar' || tag === 'metavar') return null;
    return tag;
  };

  /** Check if formula is positive (atoms default to positive) */
  const isPositive = (tag) => {
    if (tag === 'atom' || tag === 'freevar' || tag === 'metavar') return true;
    return calcIsPositive(tag);
  };

  /** Check if formula is negative */
  const isNegative = (tag) => {
    if (tag === 'atom' || tag === 'freevar' || tag === 'metavar') return false;
    return calcIsNegative(tag);
  };

  /** Get rule name for a formula at position */
  const ruleName = (h, side) => {
    const conn = connective(h);
    if (!conn) return null;
    return `${conn}_${side}`;
  };

  /** Check if a rule is invertible (uses calculus metadata) */
  const ruleIsInvertible = (tag, side) => {
    const name = `${tag}_${side}`;
    if (calculus.invertible && name in calculus.invertible) {
      return calculus.invertible[name];
    }
    if (side === 'r') return isNegative(tag);
    return isPositive(tag);
  };

  // =========================================================================
  // Core
  // =========================================================================

  /** Try identity axiom: A |- A */
  const tryIdentity = (seq, focusPos, focusIdx) => {
    const linear = pool(seq);

    if (focusPos === 'R') {
      const goal = seq.succedent;
      for (let i = 0; i < linear.length; i++) {
        const theta = unify(linear[i], goal);
        if (theta) {
          const delta = Context.fromArray(linear);
          const remaining = Context.remove(delta, linear[i]);
          return { success: true, theta, delta_out: remaining || Context.empty(), usedIndex: i };
        }
      }
    } else {
      const focused = linear[focusIdx];
      const theta = unify(focused, seq.succedent);
      if (theta) {
        const delta = Context.fromArray(linear);
        const remaining = Context.remove(delta, focused);
        return { success: true, theta, delta_out: remaining || Context.empty(), usedIndex: focusIdx };
      }
    }

    return null;
  };

  /** Apply a rule, creating premises */
  const applyRule = (seq, position, index, ruleSpec) => {
    if (!ruleSpec) return null;

    // Stickiness: rule only fires when succedent has required outer connective
    if (ruleSpec.requiresSuccedentTag) {
      const succTag = Store.isTerm(seq.succedent) ? Store.tag(seq.succedent) : null;
      if (succTag !== ruleSpec.requiresSuccedentTag) return null;
    }

    const formula = position === 'R'
      ? seq.succedent
      : pool(seq)[index];

    const made = ruleSpec.makePremises(formula, seq, index);
    if (!made) return null;
    // Extended contract (TODO_0309): exact axioms return { premises,
    // consume } — the instantiated companion formulas to remove from the
    // pool alongside the principal. Plain rules return the array.
    const premises = Array.isArray(made) ? made : made.premises;
    const consume = Array.isArray(made) ? null : made.consume;

    let delta = Context.fromArray(pool(seq));
    if (position === 'L') {
      delta = Context.remove(delta, formula);
    }
    const consumedList = position === 'L' ? [formula] : [];
    if (consume) {
      for (const h of consume) {
        if (!delta || !Context.has(delta, h)) return null;
        delta = Context.remove(delta, h);
        consumedList.push(h);
      }
    }

    if (ruleSpec.requiresEmptyDelta && !Context.isEmpty(delta || {})) {
      return null;
    }

    return {
      success: true,
      premises,
      delta_consumed: consumedList.length ? Context.fromArray(consumedList) : Context.empty(),
      delta_remaining: delta || Context.empty()
    };
  };

  /** Compute child delta by merging premise's consumable pool with current delta */
  const childDelta = (premise, currentDelta) => {
    const premisePool = pool(premise);
    if (premisePool.length === 0) return currentDelta;
    return Context.merge(currentDelta, Context.fromArray(premisePool));
  };

  /** Add delta resources to the sequent's consumable zones (wrapper-routed) */
  const addDelta = (seq, delta, copy = false) => {
    if (Context.isEmpty(delta)) return seq;

    const additions = Context.toArray(delta);
    if (singleCZ) {
      const currentLinear = seq.contexts[CZ] || [];
      return Seq.seq(
        { ...seq.contexts, [CZ]: [...currentLinear, ...additions] },
        seq.succedent
      );
    }
    const contexts = { ...seq.contexts };
    for (const z of ctxStruct.consumableZones) contexts[z] = [...(contexts[z] || [])];
    for (const h of additions) contexts[Seq.routeZone(ctxStruct, h)].push(h);
    return Seq.seq(contexts, seq.succedent);
  };

  // =========================================================================
  // Search
  // =========================================================================

  /**
   * Enumerate ALL rules that apply to a sequent (no focusing filter).
   * Returns array of { ruleName, position, index, formula }.
   */
  const applicableRules = (seq, specs, alts) => {
    const results = [];
    const linear = pool(seq);
    const succedent = seq.succedent;

    // Right rules
    if (succedent && !isAtomic(succedent)) {
      const tag = connective(succedent);
      if (tag) {
        const base = `${tag}_r`;
        if (specs[base]) results.push({ ruleName: base, position: 'R', index: -1, formula: succedent });
        if (alts[base]) {
          for (const alt of alts[base]) {
            if (specs[alt]) results.push({ ruleName: alt, position: 'R', index: -1, formula: succedent });
          }
        }
      }
    }

    // Left rules
    for (let i = 0; i < linear.length; i++) {
      const h = linear[i];
      if (!isAtomic(h)) {
        const tag = connective(h);
        if (tag) {
          const base = `${tag}_l`;
          if (specs[base]) results.push({ ruleName: base, position: 'L', index: i, formula: h });
          if (alts[base]) {
            for (const alt of alts[base]) {
              if (specs[alt]) results.push({ ruleName: alt, position: 'L', index: i, formula: h });
            }
          }
        }
      }
    }

    // Identity
    const idResult = tryIdentity(seq, 'R', -1);
    if (idResult?.success) {
      results.push({ ruleName: 'id', position: 'R', index: idResult.usedIndex, formula: succedent });
    }

    return results;
  };

  return {
    // Helpers
    connective,
    isPositive,
    isNegative,
    ruleName,
    ruleIsInvertible,

    // Core
    tryIdentity,
    applyRule,
    childDelta,
    addDelta,
    pool,

    // Search
    applicableRules,
  };
}

export { createGenericProver };
export default { createGenericProver };
