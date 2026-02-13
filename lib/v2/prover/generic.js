/**
 * L2 Generic Prover - Search Primitives
 *
 * Extracted from focused/prover.js. Contains ALL generic proof
 * utilities that are independent of focusing discipline:
 *
 * - Helpers: connective, isPositive, isNegative, ruleName, ruleIsInvertible
 * - Core: tryIdentity, applyRule, computeChildDelta, addDeltaToSequent
 * - Search: applicableRules, tryRuleAndRecurse
 *
 * The focused prover (L3) and manual prover (L4a) import from here.
 */

const { ProofTree, leaf } = require('./pt');
const Context = require('./focused/context');
const Seq = require('../kernel/sequent');
const Store = require('../kernel/store');
const { unify } = require('../kernel/unify');
const { isAtomic } = require('../kernel/ast');
const { buildRuleSpecs: buildRuleSpecsFromInterpreter } = require('./rule-interpreter');

/**
 * Create a generic prover for a calculus
 * @param {Object} calculus - Loaded calculus with polarity, rules, etc.
 */
function createGenericProver(calculus) {
  const { isPositive: calcIsPositive, isNegative: calcIsNegative } = calculus;

  // =========================================================================
  // Helpers
  // =========================================================================

  /** Get connective from formula hash (null for atoms/vars) */
  const connective = (h) => {
    const tag = Store.tag(h);
    if (!tag || tag === 'atom' || tag === 'freevar') return null;
    return tag;
  };

  /** Check if formula is positive (atoms default to positive) */
  const isPositive = (tag) => {
    if (tag === 'atom' || tag === 'freevar') return true;
    return calcIsPositive(tag);
  };

  /** Check if formula is negative */
  const isNegative = (tag) => {
    if (tag === 'atom' || tag === 'freevar') return false;
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
    const linear = Seq.getContext(seq, 'linear');

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

    const formula = position === 'R'
      ? seq.succedent
      : Seq.getContext(seq, 'linear')[index];

    const premises = ruleSpec.makePremises(formula, seq, index);
    if (!premises) return null;

    let delta = Context.fromArray(Seq.getContext(seq, 'linear'));
    if (position === 'L') {
      delta = Context.remove(delta, formula);
    }

    return {
      success: true,
      premises,
      theta: [],
      delta_consumed: position === 'L' ? Context.fromArray([formula]) : Context.empty(),
      delta_remaining: delta || Context.empty()
    };
  };

  /** Compute child delta by merging premise's linear context with current delta */
  const computeChildDelta = (premise, currentDelta) => {
    const premiseLinear = premise.contexts.linear || [];
    if (premiseLinear.length === 0) return currentDelta;

    const result = { ...currentDelta };
    for (const h of premiseLinear) {
      result[h] = (result[h] || 0) + 1;
    }
    return result;
  };

  /** Add delta resources to sequent's linear context */
  const addDeltaToSequent = (seq, delta, copy = false) => {
    if (Context.isEmpty(delta)) return seq;

    const currentLinear = seq.contexts.linear || [];
    const additions = [];

    for (const h in delta) {
      const count = delta[h];
      const hash = Number(h);
      for (let i = 0; i < count; i++) {
        additions.push(hash);
      }
    }

    return Seq.seq(
      { ...seq.contexts, linear: [...currentLinear, ...additions] },
      seq.succedent
    );
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
    const linear = Seq.getContext(seq, 'linear');
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

  /**
   * Factor out the duplicated pattern of applying a rule and recursing into premises.
   *
   * @param {Object} seq - Current sequent
   * @param {string} rName - Rule name
   * @param {Object} spec - Rule spec
   * @param {Object} delta - Current delta (remaining resources)
   * @param {Object} state - Prover-specific state
   * @param {Function} searchFn - Recursive search function: (seq, state, depth, delta) => result|null
   * @param {number} depth - Current depth
   * @param {number} maxDepth - Max depth
   * @param {Function} makeState - Function to create child state
   * @returns {Object|null} - { proofTree, delta_out, theta } or null
   */
  const tryRuleAndRecurse = (seq, rName, spec, delta, state, searchFn, depth, maxDepth, makeState) => {
    const side = rName.endsWith('_r') || rName.match(/_r\d+$/) ? 'R' : 'L';
    // Find the formula index for left rules
    let position, index;
    if (side === 'R') {
      position = 'R';
      index = -1;
    } else {
      const linear = Seq.getContext(seq, 'linear');
      const connMatch = rName.match(/^(.+?)_l\d*$/);
      const conn = connMatch ? connMatch[1] : null;
      index = -1;
      for (let i = 0; i < linear.length; i++) {
        if (Store.tag(linear[i]) === conn) { index = i; break; }
      }
      if (index < 0) return null;
      position = 'L';
    }

    const result = applyRule(seq, position, index, spec);
    if (!result?.success) return null;

    const childResults = [];
    let currentDelta = result.delta_remaining;
    let allSuccess = true;

    for (const premise of result.premises) {
      const childDelta = computeChildDelta(premise, currentDelta);
      const premiseWithDelta = addDeltaToSequent(premise, currentDelta, spec.copyContext);
      const childState = makeState ? makeState() : state;
      const childResult = searchFn(premiseWithDelta, childState, depth + 1, childDelta);

      if (!childResult) {
        allSuccess = false;
        break;
      }

      childResults.push(childResult);
      if (!spec.copyContext) {
        currentDelta = childResult.delta_out;
      }
    }

    if (!allSuccess) return null;

    const finalDelta = spec.copyContext && childResults.length > 0
      ? childResults[0].delta_out
      : currentDelta;

    return {
      proofTree: new ProofTree({
        conclusion: seq,
        premisses: childResults.map(r => r.proofTree),
        rule: rName,
        proven: true,
        state: state?.copy?.() ?? state
      }),
      delta_out: finalDelta,
      theta: []
    };
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
    computeChildDelta,
    addDeltaToSequent,

    // Search
    applicableRules,
    tryRuleAndRecurse,
  };
}

/** Build rule specifications from calculus (delegates to rule-interpreter) */
function buildRuleSpecs(calculus) {
  return buildRuleSpecsFromInterpreter(calculus);
}

module.exports = { createGenericProver, buildRuleSpecs };
