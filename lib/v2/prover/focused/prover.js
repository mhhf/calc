/**
 * Focused Prover - Minimal implementation of Andreoli's focusing
 *
 * Algorithm:
 * 1. Inversion: Apply invertible rules eagerly (negative R, positive L)
 * 2. Focus: Choose formula to focus on (positive R, negative L)
 * 3. Decompose: Apply focused rules until blur or identity
 *
 * Resource tracking via content-addressed multisets.
 */

const { ProofTree, fromGoal, leaf } = require('../pt');
const { FocusedProofState, inversion, focus } = require('./state');
const Context = require('./context');
const Seq = require('../../kernel/sequent');
const { unify, match } = require('../../kernel/unify');
const { apply: subApply } = require('../../kernel/substitute');
const { isAtomic } = require('../../kernel/ast');

/**
 * Create a focused prover for a calculus
 * @param {Object} calculus - Loaded calculus with polarity, rules, etc.
 */
function createProver(calculus) {
  const { isPositive: calcIsPositive, isNegative: calcIsNegative, isInvertible, rules, AST } = calculus;

  /**
   * Get connective from formula (null for atoms/vars)
   */
  const connective = (f) => {
    if (!f?.tag) return null;
    if (f.tag === 'atom' || f.tag === 'freevar') return null;
    return f.tag;
  };

  /**
   * Check if formula is positive (atoms default to positive)
   */
  const isPositive = (tag) => {
    if (tag === 'atom' || tag === 'freevar') return true; // Atoms are positive by default
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
  const ruleName = (f, side) => {
    const conn = connective(f);
    if (!conn) return null;
    return `${conn}_${side}`;
  };

  /**
   * Check if a rule is invertible (uses calculus metadata)
   */
  const ruleIsInvertible = (tag, side) => {
    const name = `${tag}_${side}`;
    // Check explicit invertibility annotation first
    if (calculus.invertible && name in calculus.invertible) {
      return calculus.invertible[name];
    }
    // Fall back to polarity-based inference
    if (side === 'r') return isNegative(tag);
    return isPositive(tag);
  };

  /**
   * Find invertible formula (returns { position, index, formula } or null)
   * - Negative on right → invertible (unless explicitly marked not)
   * - Positive on left → invertible (unless explicitly marked not)
   */
  const findInvertible = (seq) => {
    // Check succedent (right)
    if (seq.succedent && !isAtomic(seq.succedent)) {
      const tag = seq.succedent.tag;
      if (ruleIsInvertible(tag, 'r')) {
        return { position: 'R', index: -1, formula: seq.succedent };
      }
    }

    // Check linear context (left)
    const linear = Seq.getContext(seq, 'linear');
    for (let i = 0; i < linear.length; i++) {
      const f = linear[i];
      if (!isAtomic(f) && ruleIsInvertible(f.tag, 'l')) {
        return { position: 'L', index: i, formula: f };
      }
    }

    return null;
  };

  /**
   * Choose focus targets (returns array of { position, index?, hash?, formula })
   * Standard: Positive on right, Negative on left
   * Also: Non-invertible rules (like with_r) need focus even if polarity suggests inversion
   */
  const chooseFocus = (seq) => {
    const choices = [];

    // Right focus: positive, or non-invertible negative (like with_r)
    if (seq.succedent && !isAtomic(seq.succedent)) {
      const tag = seq.succedent.tag;
      if (isPositive(tag) || !ruleIsInvertible(tag, 'r')) {
        choices.push({ position: 'R', formula: seq.succedent });
      }
    } else if (seq.succedent && isAtomic(seq.succedent)) {
      // Atoms are positive, can focus
      choices.push({ position: 'R', formula: seq.succedent });
    }

    // Left focus: negative, or non-invertible positive (rare but possible)
    const linear = Seq.getContext(seq, 'linear');
    for (let i = 0; i < linear.length; i++) {
      const f = linear[i];
      if (!isAtomic(f)) {
        const tag = f.tag;
        if (isNegative(tag) || !ruleIsInvertible(tag, 'l')) {
          choices.push({
            position: 'L',
            index: i,
            hash: String(Seq.hashAST(f)),
            formula: f
          });
        }
      }
    }

    return choices.reverse(); // Try left first
  };

  /**
   * Try identity axiom: A ⊢ A
   * Returns { success, theta, delta_out } or null
   */
  const tryIdentity = (seq, focusPos, focusIdx) => {
    const linear = Seq.getContext(seq, 'linear');

    if (focusPos === 'R') {
      // Right focus: find matching atom in context
      const goal = seq.succedent;
      for (let i = 0; i < linear.length; i++) {
        const theta = unify(linear[i], goal);
        if (theta) {
          // Consume just this resource
          const delta = Context.fromArray(linear);
          const h = Seq.hashAST(linear[i]);
          const remaining = Context.remove(delta, h);
          return { success: true, theta, delta_out: remaining || Context.empty(), usedIndex: i };
        }
      }
    } else {
      // Left focus: match focused formula with succedent
      const focused = linear[focusIdx];
      const theta = unify(focused, seq.succedent);
      if (theta) {
        const delta = Context.fromArray(linear);
        const h = Seq.hashAST(focused);
        const remaining = Context.remove(delta, h);
        return { success: true, theta, delta_out: remaining || Context.empty(), usedIndex: focusIdx };
      }
    }

    return null;
  };

  /**
   * Apply a rule, creating premises
   * @param {Object} seq - Current sequent
   * @param {string} position - 'R' or 'L'
   * @param {number} index - Index in linear context (for L)
   * @param {Object} ruleSpec - Rule specification
   * @returns {{ success, premises, theta, delta_consumed }}
   */
  const applyRule = (seq, position, index, ruleSpec) => {
    if (!ruleSpec) return null;

    const formula = position === 'R'
      ? seq.succedent
      : Seq.getContext(seq, 'linear')[index];

    // Rule spec format: { numPremises, makePremises(formula, seq) -> [sequent] }
    const premises = ruleSpec.makePremises(formula, seq, index);
    if (!premises) return null;

    // Track consumed resources
    let delta = Context.fromArray(Seq.getContext(seq, 'linear'));
    if (position === 'L') {
      const h = Seq.hashAST(formula);
      delta = Context.remove(delta, h);
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
   * @param {Object} seq - Goal sequent
   * @param {Object} opts - { rules: { ruleName: ruleSpec }, maxDepth }
   * @returns {{ success, proofTree }}
   */
  const prove = (seq, opts = {}) => {
    const ruleSpecs = opts.rules || {};
    const maxDepth = opts.maxDepth || 100;

    const search = (seq, state, depth, delta) => {
      if (depth > maxDepth) return null;

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
              // Add remaining resources to premise
              const premiseWithDelta = addDeltaToSequent(premise, currentDelta, spec.copyContext);
              // Delta for child is what's IN the sequent (premise + added delta)
              const childDelta = Context.fromArray(Seq.getContext(premiseWithDelta, 'linear'));
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
              // For copyContext, use the child's delta_out (all children get same delta)
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

      // Phase 2: Focus choice (if not already focused)
      if (state.isInversion()) {
        const choices = chooseFocus(seq);

        for (const choice of choices) {
          const newState = focus(choice.position, choice.hash);
          // Increment depth for focus choice to prevent infinite loops
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
          // Find by hash
          focusIdx = linear.findIndex(f => String(Seq.hashAST(f)) === state.focusHash);
          if (focusIdx < 0) return null; // Focus lost
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
          return null; // Can't close, blur won't help
        }

        // Check blur condition: only blur if the rule is invertible
        // (which means it should have been handled in inversion phase)
        const side = state.position === 'R' ? 'r' : 'l';
        const shouldBlur = ruleIsInvertible(focusFormula.tag, side);

        if (shouldBlur) {
          // Blur and retry in inversion phase
          return search(seq, inversion(), depth, delta);
        }

        // Apply focused rule
        const rName = ruleName(focusFormula, state.position === 'R' ? 'r' : 'l');

        // Collect all applicable rules (including alternatives like with_l1, with_l2)
        const ruleNames = [];
        if (ruleSpecs[rName]) ruleNames.push(rName);
        if (ruleSpecs[rName + '1']) ruleNames.push(rName + '1');
        if (ruleSpecs[rName + '2']) ruleNames.push(rName + '2');

        for (const tryName of ruleNames) {
          const trySpec = ruleSpecs[tryName];
          if (!trySpec) continue;

          // Check requiresEmptyDelta constraint (e.g., promotion rule for !)
          if (trySpec.requiresEmptyDelta && !Context.isEmpty(delta)) {
            continue;
          }

          const result = applyRule(seq, state.position, focusIdx, trySpec);
          if (!result?.success) continue;

          const childResults = [];
          let currentDelta = result.delta_remaining;
          let allSuccess = true;

          for (const premise of result.premises) {
            const premiseWithDelta = addDeltaToSequent(premise, currentDelta, trySpec.copyContext);
            // After applying a rule, blur (the focused formula was consumed/decomposed)
            // Delta for child is what's IN the sequent (premise + added delta)
            const childDelta = Context.fromArray(Seq.getContext(premiseWithDelta, 'linear'));
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
            // For copyContext, use the child's delta_out (all children get same delta)
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

    // Initialize delta from linear context
    const initialDelta = Context.fromArray(Seq.getContext(seq, 'linear'));
    const result = search(seq, inversion(), 0, initialDelta);

    if (result && Context.isEmpty(result.delta_out)) {
      return { success: true, proofTree: result.proofTree };
    }

    return { success: false, proofTree: null };
  };

  /**
   * Add delta resources to sequent's linear context
   */
  const addDeltaToSequent = (seq, delta, copy = false) => {
    if (Context.isEmpty(delta)) return seq;

    const arr = Context.toArray(delta);
    let newSeq = Seq.copy(seq);

    for (const f of arr) {
      newSeq = Seq.addToContext(newSeq, 'linear', f);
    }

    return newSeq;
  };

  return { prove, findInvertible, chooseFocus, tryIdentity, connective, ruleName };
}

/**
 * Build rule specifications from calculus rules
 * This creates the makePremises functions needed by the prover
 */
function buildRuleSpecs(calculus) {
  const { AST, rules, isInvertible } = calculus;
  const specs = {};

  // Helper: create sequent from contexts and succedent
  const mkSeq = (linear, cart, succ) =>
    Seq.fromArrays(linear, cart, succ);

  // Tensor right: A ⊗ B splits context
  specs.tensor_r = {
    numPremises: 2,
    copyContext: false,
    makePremises: (formula, seq, idx) => {
      const [A, B] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      // Split: first premise gets empty, second gets all (will be refined during search)
      return [
        mkSeq([], cart, A),
        mkSeq([], cart, B)
      ];
    }
  };

  // Tensor left: A ⊗ B → A, B (adds A, B to context; delta provides rest)
  specs.tensor_l = {
    numPremises: 1,
    copyContext: false,
    // Adds A, B to premise; delta is added by prover
    extraLinear: (formula) => formula.children, // [A, B]
    makePremises: (formula, seq, idx) => {
      const [A, B] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      return [mkSeq([A, B], cart, seq.succedent)];
    }
  };

  // Loli right: A ⊸ B adds A to context (delta provides rest)
  specs.loli_r = {
    numPremises: 1,
    copyContext: false,
    extraLinear: (formula) => [formula.children[0]], // [A]
    makePremises: (formula, seq, idx) => {
      const [A, B] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      return [mkSeq([A], cart, B)];
    }
  };

  // Loli left: A ⊸ B splits into proving A and using B
  // First premise proves A, second has B (delta split between them)
  specs.loli_l = {
    numPremises: 2,
    copyContext: false,
    extraLinear: (formula, premiseIdx) => premiseIdx === 1 ? [formula.children[1]] : [],
    makePremises: (formula, seq, idx) => {
      const [A, B] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      return [
        mkSeq([], cart, A),  // Prove A with delta
        mkSeq([B], cart, seq.succedent)  // Have B, prove goal with remaining delta
      ];
    }
  };

  // With right: A & B requires proving both with same context (copy mode)
  specs.with_r = {
    numPremises: 2,
    copyContext: true, // Context copied to both premises
    makePremises: (formula, seq, idx) => {
      const [A, B] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      // Delta will be copied to both premises
      return [
        mkSeq([], cart, A),
        mkSeq([], cart, B)
      ];
    }
  };

  // With left 1: A & B → A (adds A)
  specs.with_l1 = {
    numPremises: 1,
    copyContext: false,
    extraLinear: (formula) => [formula.children[0]],
    makePremises: (formula, seq, idx) => {
      const [A, _] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      return [mkSeq([A], cart, seq.succedent)];
    }
  };

  // With left 2: A & B → B (adds B)
  specs.with_l2 = {
    numPremises: 1,
    copyContext: false,
    extraLinear: (formula) => [formula.children[1]],
    makePremises: (formula, seq, idx) => {
      const [_, B] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      return [mkSeq([B], cart, seq.succedent)];
    }
  };

  // One right: I (empty context)
  specs.one_r = {
    numPremises: 0,
    copyContext: false,
    makePremises: (formula, seq, idx) => []
  };

  // One left: 1 → remove (nothing added)
  specs.one_l = {
    numPremises: 1,
    copyContext: false,
    makePremises: (formula, seq, idx) => {
      const cart = Seq.getContext(seq, 'cartesian');
      // Nothing added by rule; delta provides rest
      return [mkSeq([], cart, seq.succedent)];
    }
  };

  // Bang/promotion: !A requires empty linear context
  specs.bang_r = {
    numPremises: 1,
    copyContext: false,
    requiresEmptyDelta: true,
    makePremises: (formula, seq, idx) => {
      const [A] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      return [mkSeq([], cart, A)];
    }
  };

  // Dereliction: !A → A (adds A to linear)
  // Named bang_l for standard rule naming (bang_l is dereliction)
  specs.bang_l = {
    numPremises: 1,
    copyContext: false,
    extraLinear: (formula) => [formula.children[0]],
    makePremises: (formula, seq, idx) => {
      const [A] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      return [mkSeq([A], cart, seq.succedent)];
    }
  };

  // Absorption: !A → A in cartesian (moves to cartesian context)
  specs.absorption = {
    numPremises: 1,
    copyContext: false,
    movesToCartesian: true,
    makePremises: (formula, seq, idx) => {
      const [A] = formula.children;
      const cart = Seq.getContext(seq, 'cartesian');
      // Add A to cartesian, remove !A from linear (handled by rule application)
      return [mkSeq([], [...cart, A], seq.succedent)];
    }
  };

  // Copy: Copy formula from cartesian to linear
  // This is a structural rule that can be applied when A is in cartesian
  specs.copy = {
    numPremises: 1,
    copyContext: false,
    structural: true,
    // makePremises takes a formula from cartesian and adds it to linear
    makePremises: (formula, seq, idx) => {
      // formula here is what we want to copy from cartesian
      const cart = Seq.getContext(seq, 'cartesian');
      const linear = Seq.getContext(seq, 'linear');
      return [mkSeq([...linear, formula], cart, seq.succedent)];
    }
  };

  return specs;
}

module.exports = { createProver, buildRuleSpecs };
