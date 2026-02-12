/**
 * Manual Proof API
 *
 * Single source of truth for interactive proof construction.
 * The UI should delegate ALL proof logic to this module.
 *
 * Design principles:
 * - Prover owns proof state (focus, delta, tree)
 * - UI is pure view layer
 * - All rule application goes through here
 */

const { createProver, buildRuleSpecs } = require('./focused/prover');
const Seq = require('../kernel/sequent');
const { isAtomic } = require('../kernel/ast');
const Context = require('./focused/context');

/**
 * Create a manual proof API for a calculus
 * @param {Object} calculus - Loaded calculus
 */
function createManualProofAPI(calculus) {
  const { specs: ruleSpecs, alternatives } = buildRuleSpecs(calculus);
  const prover = createProver(calculus);

  // =========================================================================
  // Helper functions
  // =========================================================================

  /** Check if rule splits context */
  const isContextSplitting = (ruleName) => {
    return ruleSpecs[ruleName]?.contextSplit === true;
  };

  /** Get all rule names for a connective + side (e.g. 'with', 'l' → ['with_l1', 'with_l2']) */
  const ruleNamesForConnective = (tag, side) => {
    const base = `${tag}_${side}`;
    const names = [];
    if (ruleSpecs[base]) names.push(base);
    if (alternatives[base]) {
      for (const alt of alternatives[base]) names.push(alt);
    }
    return names;
  };

  // =========================================================================
  // Proof State
  // =========================================================================

  /**
   * Create initial proof state from a sequent
   * @param {Object} seq - Sequent to prove
   * @returns {Object} Initial proof state
   */
  function createProofState(seq) {
    return {
      // The sequent being proved at this node
      conclusion: seq,

      // Proof tree children (filled in when rule applied)
      premisses: [],

      // Rule name (null until applied)
      rule: null,

      // Focus state (null = inversion phase)
      focus: null,

      // Delta: remaining linear context to distribute
      // Starts with full linear context
      delta: Context.fromArray(Seq.getContext(seq, 'linear')),

      // Is this node proven?
      proven: false,
    };
  }

  /**
   * Clone proof state (immutable updates)
   */
  function cloneState(state) {
    return {
      conclusion: Seq.copy(state.conclusion),
      premisses: state.premisses.map(cloneState),
      rule: state.rule,
      focus: state.focus ? { ...state.focus } : null,
      delta: { ...state.delta },
      proven: state.proven,
    };
  }

  // =========================================================================
  // Get Applicable Actions
  // =========================================================================

  /**
   * Get all applicable actions for current proof state
   * @param {Object} state - Current proof state
   * @param {Object} [opts] - Options
   * @param {string} [opts.mode='focused'] - 'focused' (focusing discipline) or 'unfocused' (all rules)
   * @returns {Array} List of applicable actions
   */
  function getApplicableActions(state, opts = {}) {
    const mode = opts.mode || 'focused';
    const actions = [];
    const seq = state.conclusion;
    const linear = Seq.getContext(seq, 'linear');
    const succedent = seq.succedent;
    const hasFocus = state.focus !== null;

    // =======================================================================
    // Unfocused mode: all structurally applicable rules, no Focus/Blur
    // =======================================================================
    if (mode === 'unfocused') {
      // Identity: any context formula matching succedent (via unification)
      {
        const idResult = prover.tryIdentity(seq, 'R', -1);
        if (idResult?.success) {
          actions.push({
            type: 'rule',
            name: 'id',
            displayName: 'id',
            position: 'R',
            index: idResult.usedIndex,
            formula: succedent,
            premises: [],
            closesGoal: true,
          });
        }
      }

      // Right rules (all, not just invertible)
      if (succedent && !isAtomic(succedent)) {
        const tag = prover.connective(succedent);
        if (tag) {
          for (const rn of ruleNamesForConnective(tag, 'r')) {
            const action = buildRuleAction(rn, 'R', -1, succedent, seq, state.delta);
            if (action) actions.push(action);
          }
        }
      }

      // Left rules (all, not just invertible)
      for (let i = 0; i < linear.length; i++) {
        const formula = linear[i];
        if (!isAtomic(formula)) {
          const tag = prover.connective(formula);
          if (tag) {
            for (const rn of ruleNamesForConnective(tag, 'l')) {
              const action = buildRuleAction(rn, 'L', i, formula, seq, state.delta);
              if (action) actions.push(action);
            }
          }
        }
      }

      return actions;
    }

    // =======================================================================
    // Focused mode, Phase 1: Inversion (no focus) - only invertible rules
    // =======================================================================
    if (!hasFocus) {
      // Right invertible rules
      if (succedent && !isAtomic(succedent)) {
        const tag = prover.connective(succedent);
        if (tag && prover.ruleIsInvertible(tag, 'r')) {
          for (const rn of ruleNamesForConnective(tag, 'r')) {
            const action = buildRuleAction(rn, 'R', -1, succedent, seq, state.delta);
            if (action) actions.push(action);
          }
        }
      }

      // Left invertible rules
      for (let i = 0; i < linear.length; i++) {
        const formula = linear[i];
        if (!isAtomic(formula)) {
          const tag = prover.connective(formula);
          if (tag && prover.ruleIsInvertible(tag, 'l')) {
            for (const rn of ruleNamesForConnective(tag, 'l')) {
              const action = buildRuleAction(rn, 'L', i, formula, seq, state.delta);
              if (action) actions.push(action);
            }
          }
        }
      }

      // Focus actions (delegate to prover's chooseFocus)
      const focusTargets = prover.chooseFocus(seq);
      for (const target of focusTargets) {
        actions.push({
          type: 'focus',
          name: target.position === 'R' ? 'Focus_R' : 'Focus_L',
          displayName: target.position === 'R' ? 'Focus_R' : 'Focus_L',
          position: target.position,
          index: target.index ?? -1,
          formula: target.formula,
          description: target.position === 'R'
            ? 'Focus on succedent' : 'Focus on context formula',
        });
      }
    }

    // =======================================================================
    // Focused mode, Phase 2: Focused - only rules for focused formula
    // =======================================================================
    if (hasFocus) {
      const focusPos = state.focus.position;
      const focusIdx = state.focus.index;
      const focusFormula = focusPos === 'R'
        ? succedent
        : linear[focusIdx];

      // Identity (for atoms, via unification)
      if (isAtomic(focusFormula)) {
        const idResult = prover.tryIdentity(seq, focusPos, focusIdx);
        if (idResult?.success) {
          actions.push({
            type: 'rule',
            name: 'id',
            displayName: 'id',
            position: focusPos,
            index: idResult.usedIndex,
            formula: focusFormula,
            premises: [],
            closesGoal: true,
          });
        }
      } else {
        // Decomposition rule for focused formula
        const tag = prover.connective(focusFormula);
        if (tag) {
          const side = focusPos === 'R' ? 'r' : 'l';
          const ruleName = `${tag}_${side}`;

          for (const rn of ruleNamesForConnective(tag, side)) {
            const action = buildRuleAction(rn, focusPos, focusIdx, focusFormula, seq, state.delta);
            if (action) actions.push(action);
          }
        }
      }
    }

    return actions;
  }

  /**
   * Build a rule action with computed premises
   */
  function buildRuleAction(ruleName, position, index, formula, seq, delta) {
    const spec = ruleSpecs[ruleName];
    if (!spec?.makePremises) return null;

    const barePremises = spec.makePremises(formula, seq, index);
    if (!barePremises) return null;

    // Compute remaining delta after removing principal formula
    let remainingDelta = delta;
    if (position === 'L') {
      remainingDelta = Context.remove(delta, formula) || Context.empty();
    }

    // Check if context split is needed
    const needsContextSplit = isContextSplitting(ruleName) && !Context.isEmpty(remainingDelta);

    // Compute context entries for split dialog
    const contextEntries = [];
    if (needsContextSplit) {
      for (const h in remainingDelta) {
        const count = remainingDelta[h];
        const hash = Number(h);
        for (let i = 0; i < count; i++) {
          contextEntries.push({
            hash,
            formula: calculus.render(hash, 'ascii'),
            formulaLatex: calculus.render(hash, 'latex'),
          });
        }
      }
    }

    // Compute full premises (with context added)
    const cart = Seq.getContext(seq, 'cartesian');
    const fullPremises = barePremises.map((barePremise, i) => {
      const premiseLinear = barePremise.contexts?.linear || [];

      if (spec.copyContext) {
        // Add full remaining delta to each premise
        const additions = Context.toArray(remainingDelta);
        return Seq.fromArrays([...additions, ...premiseLinear], cart, barePremise.succedent);
      } else if (needsContextSplit) {
        // User will split - for now return bare premise
        return barePremise;
      } else {
        // Non-splitting: distribute delta to first premise only
        if (i === 0) {
          const additions = Context.toArray(remainingDelta);
          return Seq.fromArrays([...additions, ...premiseLinear], cart, barePremise.succedent);
        }
        return barePremise;
      }
    });

    return {
      type: 'rule',
      name: ruleName,
      displayName: ruleName,
      position,
      index,
      formula,
      premises: fullPremises,
      barePremises,
      needsContextSplit,
      contextEntries,
      remainingDelta,
      copyContext: spec.copyContext || false,
      closesGoal: barePremises.length === 0,
    };
  }

  // =========================================================================
  // Apply Action
  // =========================================================================

  /**
   * Apply an action to proof state
   * @param {Object} state - Current proof state
   * @param {Object} action - Action to apply
   * @param {Object} [userInput] - User input for context split
   * @returns {Object} New proof state
   */
  function applyAction(state, action, userInput) {
    const newState = cloneState(state);

    // =======================================================================
    // Focus action
    // =======================================================================
    if (action.type === 'focus') {
      newState.rule = action.displayName;
      newState.premisses = [{
        ...createProofState(state.conclusion),
        focus: {
          position: action.position,
          index: action.index,
          hash: action.formula,
        },
        delta: state.delta,
      }];
      return newState;
    }

    // =======================================================================
    // Rule action
    // =======================================================================
    if (action.type === 'rule') {
      newState.rule = action.displayName;
      newState.focus = null; // Clear focus after rule application

      // Identity - closes the goal
      if (action.name === 'id') {
        newState.premisses = [];
        newState.proven = true;
        return newState;
      }

      // Get premises
      let premises;
      if (action.needsContextSplit && userInput?.split) {
        // User provided split
        premises = computePremisesWithSplit(action, userInput.split);
      } else if (action.needsContextSplit && !userInput) {
        // Need split but none provided - return action with split requirement
        throw new Error('Context split required but not provided');
      } else {
        // Use pre-computed premises
        premises = action.premises;
      }

      // Create child states
      newState.premisses = premises.map(premise => {
        const childState = createProofState(premise);
        // For copyContext rules, children share delta
        // For splitting rules, delta is distributed via split
        // For other rules, delta passes to first child
        return childState;
      });

      newState.proven = premises.length === 0;
      return newState;
    }

    throw new Error(`Unknown action type: ${action.type}`);
  }

  /**
   * Compute premises with user-specified context split
   */
  function computePremisesWithSplit(action, split) {
    const cart = Seq.getContext(action.premises[0], 'cartesian') || [];
    const barePremises = action.barePremises;

    // split = { premise1: [hash, hash, ...], premise2: [hash, hash, ...] }
    const p1Delta = split.premise1 || [];
    const p2Delta = split.premise2 || [];

    return barePremises.map((barePremise, i) => {
      const premiseLinear = barePremise.contexts?.linear || [];
      const additions = i === 0 ? p1Delta : p2Delta;
      return Seq.fromArrays([...additions, ...premiseLinear], cart, barePremise.succedent);
    });
  }

  // =========================================================================
  // Rendering helpers
  // =========================================================================

  /**
   * Render sequent with optional focus highlighting
   * @param {Object} seq - Sequent to render
   * @param {string} format - 'ascii' or 'latex'
   * @param {Object} [focus] - Focus state for highlighting
   */
  function renderSequent(seq, format = 'ascii', focus = null) {
    const linear = Seq.getContext(seq, 'linear');
    const cart = Seq.getContext(seq, 'cartesian');
    const succedent = seq.succedent;

    const renderFormula = (h, highlight = false) => {
      const rendered = calculus.render(h, format);
      if (highlight) {
        if (format === 'latex') return `[${rendered}]`;
        return `[${rendered}]`;
      }
      return rendered;
    };

    // Render linear context with focus highlighting
    const linearParts = linear.map((h, i) => {
      const highlight = focus && focus.position === 'L' && focus.index === i;
      return renderFormula(h, highlight);
    });

    // Render succedent with focus highlighting
    const highlightSucc = focus && focus.position === 'R';
    const succPart = renderFormula(succedent, highlightSucc);

    const cartPart = cart.length > 0 ? cart.map(h => renderFormula(h)).join(', ') + ' ; ' : '';
    const linearPart = linearParts.join(', ');
    const turnstile = format === 'latex' ? '\\vdash' : '|-';

    if (cartPart) {
      return `${cartPart}${linearPart} ${turnstile} ${succPart}`;
    }
    return linearPart ? `${linearPart} ${turnstile} ${succPart}` : `${turnstile} ${succPart}`;
  }

  /**
   * Get abstract rule display (for inference rule visualization)
   */
  function getAbstractRule(ruleName) {
    const schemas = {
      'tensor_r': {
        conclusion: '\\Gamma \\vdash A \\otimes B',
        premises: ['\\Gamma_1 \\vdash A', '\\Gamma_2 \\vdash B'],
      },
      'tensor_l': {
        conclusion: '\\Gamma, A \\otimes B \\vdash C',
        premises: ['\\Gamma, A, B \\vdash C'],
      },
      'loli_r': {
        conclusion: '\\Gamma \\vdash A \\multimap B',
        premises: ['\\Gamma, A \\vdash B'],
      },
      'loli_l': {
        conclusion: '\\Gamma, A \\multimap B \\vdash C',
        premises: ['\\Gamma_1 \\vdash A', '\\Gamma_2, B \\vdash C'],
      },
      'with_r': {
        conclusion: '\\Gamma \\vdash A \\& B',
        premises: ['\\Gamma \\vdash A', '\\Gamma \\vdash B'],
      },
      'with_l1': {
        conclusion: '\\Gamma, A \\& B \\vdash C',
        premises: ['\\Gamma, A \\vdash C'],
      },
      'with_l2': {
        conclusion: '\\Gamma, A \\& B \\vdash C',
        premises: ['\\Gamma, B \\vdash C'],
      },
      'one_r': {
        conclusion: '\\vdash I',
        premises: [],
      },
      'one_l': {
        conclusion: '\\Gamma, I \\vdash C',
        premises: ['\\Gamma \\vdash C'],
      },
      'id': {
        conclusion: 'A \\vdash A',
        premises: [],
      },
      'Focus_L': {
        conclusion: '\\Gamma, A \\vdash C',
        premises: ['\\Gamma, [A] \\vdash C'],
      },
      'Focus_R': {
        conclusion: '\\Gamma \\vdash A',
        premises: ['\\Gamma \\vdash [A]'],
      },
    };

    return schemas[ruleName] || { conclusion: ruleName, premises: [] };
  }

  // =========================================================================
  // Export API
  // =========================================================================

  return {
    // State management
    createProofState,
    cloneState,

    // Actions
    getApplicableActions,
    applyAction,

    // Rendering
    renderSequent,
    getAbstractRule,

    // Utilities
    ruleSpecs,
    isContextSplitting,
    connective: prover.connective,
    ruleIsInvertible: prover.ruleIsInvertible,
  };
}

module.exports = { createManualProofAPI };
