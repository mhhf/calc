/**
 * L3 Focused Prover (Andreoli's focusing discipline)
 *
 * Imports generic search primitives from L2 (generic.js).
 * Contains ONLY focusing-specific logic:
 * - findInvertible: find formula with invertible rule
 * - chooseFocus: choose formula to focus on
 * - prove: focused proof search with inversion/focus/blur phases
 */

const { ProofTree, leaf } = require('../pt');
const { FocusedProofState, inversion, focus } = require('./state');
const Context = require('./context');
const Seq = require('../../kernel/sequent');
const Store = require('../../kernel/store');
const { unify } = require('../../kernel/unify');
const { isAtomic } = require('../../kernel/ast');
const { createGenericProver, buildRuleSpecs } = require('../generic');

/**
 * Create a focused prover for a calculus
 * @param {Object} calculus - Loaded calculus with polarity, rules, etc.
 */
function createProver(calculus) {
  const generic = createGenericProver(calculus);

  // Re-export L2 helpers for backward compatibility
  const { connective, isPositive, isNegative, ruleName, ruleIsInvertible,
          tryIdentity, applyRule, computeChildDelta, addDeltaToSequent } = generic;

  // =========================================================================
  // L3: Focusing-specific logic
  // =========================================================================

  /**
   * Find invertible formula (returns { position, index, formula } or null)
   */
  const findInvertible = (seq) => {
    // Check succedent (right)
    if (seq.succedent && !isAtomic(seq.succedent)) {
      const tag = Store.tag(seq.succedent);
      if (ruleIsInvertible(tag, 'r')) {
        return { position: 'R', index: -1, formula: seq.succedent };
      }
    }

    // Check linear context (left)
    const linear = Seq.getContext(seq, 'linear');
    for (let i = 0; i < linear.length; i++) {
      const h = linear[i];
      if (!isAtomic(h)) {
        const tag = Store.tag(h);
        if (ruleIsInvertible(tag, 'l')) {
          return { position: 'L', index: i, formula: h };
        }
      }
    }

    return null;
  };

  /**
   * Choose focus targets
   */
  const chooseFocus = (seq) => {
    const choices = [];

    // Right focus: positive, or non-invertible negative
    if (seq.succedent && !isAtomic(seq.succedent)) {
      const tag = Store.tag(seq.succedent);
      if (isPositive(tag) || !ruleIsInvertible(tag, 'r')) {
        choices.push({ position: 'R', formula: seq.succedent });
      }
    } else if (seq.succedent && isAtomic(seq.succedent)) {
      choices.push({ position: 'R', formula: seq.succedent });
    }

    // Left focus: negative, or non-invertible positive
    const linear = Seq.getContext(seq, 'linear');
    for (let i = 0; i < linear.length; i++) {
      const h = linear[i];
      if (!isAtomic(h)) {
        const tag = Store.tag(h);
        if (isNegative(tag) || !ruleIsInvertible(tag, 'l')) {
          choices.push({
            position: 'L',
            index: i,
            hash: h,
            formula: h
          });
        }
      }
    }

    return choices.reverse();
  };

  /**
   * Apply a rule and recurse into premises (factored from duplicated pattern)
   */
  const applyAndRecurse = (seq, rName, spec, position, index, state, searchFn, depth, delta) => {
    const result = applyRule(seq, position, index, spec);
    if (!result?.success) return null;

    const childResults = [];
    let currentDelta = result.delta_remaining;
    let allSuccess = true;

    for (const premise of result.premises) {
      const childDelta = computeChildDelta(premise, currentDelta);
      const premiseWithDelta = addDeltaToSequent(premise, currentDelta, spec.copyContext);
      const childResult = searchFn(premiseWithDelta, inversion(), depth + 1, childDelta);

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
        state: state.copy()
      }),
      delta_out: finalDelta,
      theta: []
    };
  };

  /**
   * Main proof search (focused discipline)
   */
  const prove = (seq, opts = {}) => {
    const ruleSpecs = opts.rules || {};
    const ruleAlternatives = opts.alternatives || {};
    const maxDepth = opts.maxDepth || 100;

    const search = (seq, state, depth, delta) => {
      if (depth > maxDepth) return null;

      // Phase 0: Try identity FIRST
      const idResult = tryIdentity(seq, 'R', -1);
      if (idResult?.success && Context.isEmpty(idResult.delta_out)) {
        return {
          proofTree: leaf(seq, 'id'),
          delta_out: idResult.delta_out,
          theta: idResult.theta
        };
      }

      // Phase 0.5: Try copy from cartesian
      const cart = Seq.getContext(seq, 'cartesian');
      if (cart.length > 0 && Context.isEmpty(delta) && ruleSpecs.copy) {
        for (let i = 0; i < cart.length; i++) {
          const cartFormula = cart[i];
          const theta = unify(cartFormula, seq.succedent);
          if (theta) {
            const newLinear = [cartFormula];
            const premise = Seq.fromArrays(newLinear, cart, seq.succedent);
            const premiseDelta = Context.fromArray(newLinear);

            const childResult = search(premise, inversion(), depth + 1, premiseDelta);
            if (childResult) {
              return {
                proofTree: new ProofTree({
                  conclusion: seq,
                  premisses: [childResult.proofTree],
                  rule: 'copy',
                  proven: true,
                  state: state.copy()
                }),
                delta_out: Context.empty(),
                theta: []
              };
            }
          }
        }
      }

      // Phase 1: Inversion
      const inv = findInvertible(seq);
      if (inv) {
        const rName = ruleName(inv.formula, inv.position === 'R' ? 'r' : 'l');
        const spec = ruleSpecs[rName];

        if (spec) {
          const result = applyAndRecurse(seq, rName, spec, inv.position, inv.index, state, search, depth, delta);
          if (result) return result;
        }
      }

      // Phase 2: Focus choice
      if (state.isInversion()) {
        const choices = chooseFocus(seq);

        for (const choice of choices) {
          const newState = focus(choice.position, choice.hash);
          const result = search(seq, newState, depth + 1, delta);
          if (result) return result;
        }
      }

      // Phase 3: Focused decomposition
      if (state.isFocused()) {
        const linear = Seq.getContext(seq, 'linear');
        let focusFormula, focusIdx;

        if (state.position === 'R') {
          focusFormula = seq.succedent;
          focusIdx = -1;
        } else {
          focusIdx = linear.findIndex(h => h === state.focusHash);
          if (focusIdx < 0) return null;
          focusFormula = linear[focusIdx];
        }

        // Try identity for atoms
        if (isAtomic(focusFormula)) {
          const idResult = tryIdentity(seq, state.position, focusIdx);
          if (idResult) {
            return {
              proofTree: leaf(seq, state.position === 'R' ? 'id_+' : 'id_-'),
              delta_out: idResult.delta_out,
              theta: idResult.theta
            };
          }
          return null;
        }

        // Check blur condition
        const side = state.position === 'R' ? 'r' : 'l';
        const tag = Store.tag(focusFormula);
        const shouldBlur = ruleIsInvertible(tag, side);

        if (shouldBlur) {
          return search(seq, inversion(), depth, delta);
        }

        // Apply focused rule
        const rName = ruleName(focusFormula, state.position === 'R' ? 'r' : 'l');

        const ruleNames = [];
        if (ruleSpecs[rName]) ruleNames.push(rName);
        if (ruleAlternatives[rName]) {
          for (const alt of ruleAlternatives[rName]) ruleNames.push(alt);
        }

        for (const tryName of ruleNames) {
          const trySpec = ruleSpecs[tryName];
          if (!trySpec) continue;

          if (trySpec.requiresEmptyDelta && !Context.isEmpty(delta)) {
            continue;
          }

          const result = applyAndRecurse(seq, tryName, trySpec, state.position, focusIdx, state, search, depth, delta);
          if (result) return result;
        }
      }

      return null;
    };

    const initialDelta = Context.fromArray(Seq.getContext(seq, 'linear'));
    const result = search(seq, inversion(), 0, initialDelta);

    if (result && Context.isEmpty(result.delta_out)) {
      return { success: true, proofTree: result.proofTree };
    }

    return { success: false, proofTree: null };
  };

  return { prove, findInvertible, chooseFocus, tryIdentity, connective, ruleName, ruleIsInvertible };
}

module.exports = { createProver, buildRuleSpecs };
