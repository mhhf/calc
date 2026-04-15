/**
 * L3 Focused Prover (Andreoli's focusing discipline)
 *
 * Imports generic search primitives from L2 (generic.js).
 * Contains ONLY focusing-specific logic:
 * - findInvertible: find formula with invertible rule
 * - chooseFocus: choose formula to focus on
 * - prove: focused proof search with inversion/focus/blur phases
 */

const { ProofTree, leaf } = require('./pt');
const { FocusedProofState, inversion, focus } = require('./state');
const Context = require('./context');
const Seq = require('../kernel/sequent');
const Store = require('../kernel/store');
const { unify } = require('../kernel/unify');
const { isAtomic } = require('../kernel/ast');
const { createGenericProver } = require('./generic');
const bridge = require('./bridge');
const { MetaCtx } = require('./meta-ctx');

/**
 * Create a focused prover for a calculus
 * @param {Object} calculus - Loaded calculus with polarity, rules, etc.
 */
function createProver(calculus) {
  const generic = createGenericProver(calculus);

  // Re-export L2 helpers for backward compatibility
  const { connective, isPositive, isNegative, ruleName, ruleIsInvertible,
          tryIdentity, applyRule, childDelta, addDelta } = generic;

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
   * Apply a rule and recurse into premises.
   *
   * mc (MetaCtx) is passed explicitly because applyAndRecurse is defined at the
   * createProver level (not inside prove()), so it can't access mc via closure.
   * search() accesses mc via closure from prove().
   *
   * The conclusion sequent is resolved via mc.resolveSeq only when mc.hasBindings()
   * is true — this guard avoids the O(contexts × term_size) cost for the common
   * case of ground proofs (no metavars).
   */
  const applyAndRecurse = (seq, rName, spec, position, index, state, searchFn, depth, delta, opts, mc) => {
    // Mode switch: monad_r bypasses standard premise computation
    if (spec.modeShift) {
      const engineCalc = opts?.engineCalc || null;
      const switchResult = bridge.modeSwitch(seq, engineCalc, opts);
      if (!switchResult) return null;
      return {
        proofTree: switchResult.proofNode,
        delta_out: Context.empty()
      };
    }

    const result = applyRule(seq, position, index, spec);
    if (!result?.success) return null;

    const childResults = [];
    let currentDelta = result.delta_remaining;
    let allSuccess = true;

    for (const premise of result.premises) {
      const cDelta = childDelta(premise, currentDelta);
      const premiseWithDelta = addDelta(premise, currentDelta, spec.copyContext);
      const childResult = searchFn(premiseWithDelta, inversion(), depth + 1, cDelta);

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

    let finalDelta;
    if (spec.discardsContext) {
      // zero_l and similar: discard all remaining linear resources
      finalDelta = Context.empty();
    } else if (spec.copyContext && childResults.length > 0) {
      finalDelta = childResults[0].delta_out;
    } else {
      finalDelta = currentDelta;
    }

    return {
      proofTree: new ProofTree({
        conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
        premises: childResults.map(r => r.proofTree),
        rule: rName,
        proven: true,
        state: state.copy()
      }),
      delta_out: finalDelta
    };
  };

  /**
   * Main proof search (focused discipline)
   */
  const prove = (seq, opts = {}) => {
    const ruleSpecs = opts.rules || {};
    const ruleAlternatives = opts.alternatives || {};
    const maxDepth = opts.maxDepth || 100;
    const mc = new MetaCtx();

    // Proof search follows Andreoli's focusing discipline:
    //   Pre-focusing:  try axioms (identity, copy)
    //   Inversion:     eagerly apply invertible rules (Phase 1)
    //   Focus:         choose a formula to focus on (Phase 2)
    //   Decomposition: apply non-invertible rule to focused formula (Phase 3)
    //   Blur:          when focused formula becomes invertible, return to inversion
    //
    // mc.save()/restore() wraps every choice point (focus loop, rule alternatives).
    // Inversion has no save/restore: if it fails, the failure propagates to the
    // caller's save/restore. Single-path, no branching within inversion.

    const search = (seq, state, depth, delta) => {
      if (depth > maxDepth) return null;

      // Axiom: identity (A ⊢ A) — not part of focusing, checked first
      const idResult = tryIdentity(seq, 'R', -1);
      if (idResult?.success && Context.isEmpty(idResult.delta_out)) {
        mc.absorbTheta(idResult.theta);
        return {
          proofTree: leaf(mc.hasBindings() ? mc.resolveSeq(seq) : seq, 'id'),
          delta_out: idResult.delta_out
        };
      }

      // Axiom: copy from cartesian context — structural rule, pre-focusing
      const cart = Seq.getContext(seq, 'cartesian');
      if (cart.length > 0 && Context.isEmpty(delta) && ruleSpecs.copy) {
        for (let i = 0; i < cart.length; i++) {
          const cartFormula = cart[i];
          const theta = unify(cartFormula, seq.succedent);
          if (theta) {
            const mark = mc.save();
            const newLinear = [cartFormula];
            const premise = Seq.fromArrays(newLinear, cart, seq.succedent);
            const premiseDelta = Context.fromArray(newLinear);

            const childResult = search(premise, inversion(), depth + 1, premiseDelta);
            if (childResult) {
              return {
                proofTree: new ProofTree({
                  conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
                  premises: [childResult.proofTree],
                  rule: 'copy',
                  proven: true,
                  state: state.copy()
                }),
                delta_out: Context.empty()
              };
            }
            mc.restore(mark);
          }
        }
      }

      // Focusing Phase 1 — Inversion: apply invertible rules eagerly
      const inv = findInvertible(seq);
      if (inv) {
        const rName = ruleName(inv.formula, inv.position === 'R' ? 'r' : 'l');
        const spec = ruleSpecs[rName];

        if (spec) {
          const mark = mc.save();
          const result = applyAndRecurse(seq, rName, spec, inv.position, inv.index, state, search, depth, delta, opts, mc);
          if (result) return result;
          mc.restore(mark);
        }
      }

      // Focusing Phase 2 — Focus: choose formula to enter focused phase
      if (state.isInversion()) {
        const choices = chooseFocus(seq);

        for (const choice of choices) {
          const mark = mc.save();
          const newState = focus(choice.position, choice.hash);
          const result = search(seq, newState, depth + 1, delta);
          if (result) return result;
          mc.restore(mark);
        }
      }

      // Focusing Phase 3 — Decomposition: apply non-invertible rule to focused formula
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
            mc.absorbTheta(idResult.theta);
            return {
              proofTree: leaf(mc.hasBindings() ? mc.resolveSeq(seq) : seq, state.position === 'R' ? 'id_+' : 'id_-'),
              delta_out: idResult.delta_out
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
          const mark = mc.save();
          const trySpec = ruleSpecs[tryName];
          if (!trySpec) continue;

          const result = applyAndRecurse(seq, tryName, trySpec, state.position, focusIdx, state, search, depth, delta, opts, mc);
          if (result) return result;
          mc.restore(mark);
        }
      }

      return null;
    };

    const initialDelta = Context.fromArray(Seq.getContext(seq, 'linear'));
    const result = search(seq, inversion(), 0, initialDelta);

    if (result && Context.isEmpty(result.delta_out)) {
      let tree = result.proofTree;
      // Resolve any remaining unground sequents (sibling subtrees
      // constructed before a metavar was bound by a later sibling)
      if (mc.hasBindings()) {
        tree = mc.resolveTree(tree);
      }
      return { success: true, proofTree: tree };
    }

    return { success: false, proofTree: null };
  };

  return { prove, findInvertible, chooseFocus, tryIdentity, connective, ruleName, ruleIsInvertible };
}

module.exports = { createProver };
