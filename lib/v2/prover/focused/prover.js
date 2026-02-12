/**
 * Focused Prover for content-addressed terms
 *
 * All formulas are represented as hashes (numbers).
 * Uses Store to dereference when inspecting structure.
 *
 * Algorithm:
 * 1. Inversion: Apply invertible rules eagerly (negative R, positive L)
 * 2. Focus: Choose formula to focus on (positive R, negative L)
 * 3. Decompose: Apply focused rules until blur or identity
 */

const { ProofTree, fromGoal, leaf } = require('../pt');
const { FocusedProofState, inversion, focus } = require('./state');
const Context = require('./context');
const Seq = require('../../kernel/sequent');
const Store = require('../../kernel/store');
const { unify, match } = require('../../kernel/unify');
const { apply: subApply } = require('../../kernel/substitute');
const { isAtomic } = require('../../kernel/ast');
const { buildRuleSpecs: buildRuleSpecsFromInterpreter } = require('../rule-interpreter');

/**
 * Create a focused prover for a calculus
 * @param {Object} calculus - Loaded calculus with polarity, rules, etc.
 */
function createProver(calculus) {
  const { isPositive: calcIsPositive, isNegative: calcIsNegative, isInvertible, rules, AST } = calculus;

  /**
   * Get connective from formula hash (null for atoms/vars)
   */
  const connective = (h) => {
    const tag = Store.tag(h);
    if (!tag || tag === 'atom' || tag === 'freevar') return null;
    return tag;
  };

  /**
   * Check if formula is positive (atoms default to positive)
   */
  const isPositive = (tag) => {
    if (tag === 'atom' || tag === 'freevar') return true;
    return calcIsPositive(tag);
  };

  /**
   * Check if formula is negative
   */
  const isNegative = (tag) => {
    if (tag === 'atom' || tag === 'freevar') return false;
    return calcIsNegative(tag);
  };

  /**
   * Get rule name for a formula at position
   */
  const ruleName = (h, side) => {
    const conn = connective(h);
    if (!conn) return null;
    return `${conn}_${side}`;
  };

  /**
   * Check if a rule is invertible (uses calculus metadata)
   */
  const ruleIsInvertible = (tag, side) => {
    const name = `${tag}_${side}`;
    if (calculus.invertible && name in calculus.invertible) {
      return calculus.invertible[name];
    }
    if (side === 'r') return isNegative(tag);
    return isPositive(tag);
  };

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
            hash: h,  // Formula IS its hash
            formula: h
          });
        }
      }
    }

    return choices.reverse();
  };

  /**
   * Try identity axiom: A ⊢ A
   */
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

  /**
   * Apply a rule, creating premises
   */
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

  /**
   * Main proof search
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
          const result = applyRule(seq, inv.position, inv.index, spec);
          if (result?.success) {
            const childResults = [];
            let currentDelta = result.delta_remaining;
            let allSuccess = true;

            for (const premise of result.premises) {
              // Compute childDelta directly (avoids round-trip through sequent)
              const childDelta = computeChildDelta(premise, currentDelta);
              const premiseWithDelta = addDeltaToSequent(premise, currentDelta, spec.copyContext);
              const childResult = search(premiseWithDelta, inversion(), depth + 1, childDelta);

              if (!childResult) {
                allSuccess = false;
                break;
              }

              childResults.push(childResult);
              if (!spec.copyContext) {
                currentDelta = childResult.delta_out;
              }
            }

            if (allSuccess) {
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
            }
          }
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
          // Find by hash (now O(1) comparison)
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

          const result = applyRule(seq, state.position, focusIdx, trySpec);
          if (!result?.success) continue;

          const childResults = [];
          let currentDelta = result.delta_remaining;
          let allSuccess = true;

          for (const premise of result.premises) {
            // Compute childDelta directly (avoids round-trip through sequent)
            const childDelta = computeChildDelta(premise, currentDelta);
            const premiseWithDelta = addDeltaToSequent(premise, currentDelta, trySpec.copyContext);
            const childResult = search(premiseWithDelta, inversion(), depth + 1, childDelta);

            if (!childResult) {
              allSuccess = false;
              break;
            }

            childResults.push(childResult);
            if (!trySpec.copyContext) {
              currentDelta = childResult.delta_out;
            }
          }

          if (allSuccess) {
            const finalDelta = trySpec.copyContext && childResults.length > 0
              ? childResults[0].delta_out
              : currentDelta;

            return {
              proofTree: new ProofTree({
                conclusion: seq,
                premisses: childResults.map(r => r.proofTree),
                rule: tryName,
                proven: true,
                state: state.copy()
              }),
              delta_out: finalDelta,
              theta: []
            };
          }
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

  /**
   * Compute child delta by merging premise's linear context with current delta
   * Optimized: avoids Context.fromArray(Seq.getContext(...)) round-trip
   */
  const computeChildDelta = (premise, currentDelta) => {
    const premiseLinear = premise.contexts.linear || [];
    if (premiseLinear.length === 0) return currentDelta;

    // Merge premise's linear formulas into delta (shallow copy + add)
    const result = { ...currentDelta };
    for (const h of premiseLinear) {
      result[h] = (result[h] || 0) + 1;
    }
    return result;
  };

  /**
   * Add delta resources to sequent's linear context
   * Optimized: builds new sequent directly without intermediate objects
   */
  const addDeltaToSequent = (seq, delta, copy = false) => {
    if (Context.isEmpty(delta)) return seq;

    const currentLinear = seq.contexts.linear || [];
    const additions = [];

    // Build additions directly from multiset (avoids Context.toArray allocation)
    for (const h in delta) {
      const count = delta[h];
      const hash = Number(h);
      for (let i = 0; i < count; i++) {
        additions.push(hash);
      }
    }

    // Build new sequent directly (avoids Seq.copy and N addToContext calls)
    return Seq.seq(
      { ...seq.contexts, linear: [...currentLinear, ...additions] },
      seq.succedent
    );
  };

  return { prove, findInvertible, chooseFocus, tryIdentity, connective, ruleName, ruleIsInvertible };
}

/**
 * Build rule specifications from calculus rule ASTs (generic interpreter).
 * Returns the specs object keyed by rule name.
 */
function buildRuleSpecs(calculus) {
  return buildRuleSpecsFromInterpreter(calculus);
}

module.exports = { createProver, buildRuleSpecs };
