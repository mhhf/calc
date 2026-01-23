/**
 * Focused Prover Module
 *
 * Implements focused proof search as a separate layer from the framework.
 * Focus state is tracked externally (on ProofTree), not in sequent syntax.
 *
 * Architecture:
 * - ProofSearchState: tracks phase (inversion/focus), focus position/id
 * - FocusedProver: implements the focusing discipline
 * - Framework (sequent, mgu, etc.) remains generic
 */

const Calc = require("./calc.js");
const PT = require("./pt.js");
const Sequent = require("./sequent.js");
const substitute = require('./substitute.js');
const mgu = require('./mgu.js');
const { inferAllPolarities, inferAllContextModes } = require('./polarity.js');

/**
 * Proof search state - tracked on ProofTree, not Sequent
 */
class ProofSearchState {
  constructor(opts = {}) {
    this.phase = opts.phase || 'inversion';  // 'inversion' | 'focus'
    this.focusPosition = opts.focusPosition || null;  // 'L' | 'R' | null
    this.focusId = opts.focusId || null;  // for left formulas
  }

  copy() {
    return new ProofSearchState({
      phase: this.phase,
      focusPosition: this.focusPosition,
      focusId: this.focusId
    });
  }

  focus(position, id = null) {
    this.phase = 'focus';
    this.focusPosition = position;
    this.focusId = id;
  }

  blur() {
    this.phase = 'inversion';
    this.focusPosition = null;
    this.focusId = null;
  }

  isFocused() {
    return this.phase === 'focus';
  }
}

/**
 * Focused Prover - implements Andreoli's focusing discipline
 */
class FocusedProver {
  constructor(calculus) {
    this.polarity = inferAllPolarities(calculus.rules);
    this.contextModes = inferAllContextModes(calculus.rules);
    this.rules = calculus.rules;
  }

  /**
   * Get polarity of a formula
   */
  getPolarity(formula) {
    const type = Calc.db.rules[formula.id];
    if (!type) return '';

    // Check inferred polarity
    if (this.polarity[type.ruleName]) {
      return this.polarity[type.ruleName];
    }

    // Check explicit polarity on type
    if (type.polarity) {
      return type.polarity;
    }

    return '';
  }

  /**
   * Check if formula is positive
   */
  isPositive(node) {
    if (node.isTermType && node.isTermType()) {
      return this.getPolarity(node.vals[1]) === 'positive';
    }
    return this.getPolarity(node) === 'positive';
  }

  /**
   * Check if formula is negative
   */
  isNegative(node) {
    if (node.isTermType && node.isTermType()) {
      return this.getPolarity(node.vals[1]) === 'negative';
    }
    return this.getPolarity(node) === 'negative';
  }

  /**
   * Check if formula is atomic (not a complex connective)
   */
  isAtomic(formula) {
    const type = Calc.db.rules[formula.id];
    return type.ruleName === "Formula_Atprop" || type.ruleName === "Formula_Freevar";
  }

  /**
   * Find an invertible rule to apply
   * Returns position ('R' or left-context id) or false
   */
  getInvertibleRule(pt) {
    const succedent = pt.conclusion.succedent;
    const linear_ctx = pt.conclusion.linear_ctx;

    // 1. Check if succedent has a negative complex formula (invertible on right)
    if (succedent.vals && succedent.vals[1]) {
      const formula = succedent.vals[1];
      if (!this.isAtomic(formula) && this.isNegative(succedent)) {
        return 'R';
      }
    }

    // 2. Check for positive complex formula on left (invertible on left)
    const leftId = Object.keys(linear_ctx).find(id => {
      const val = linear_ctx[id].val;
      if (!val.isTermType || !val.isTermType()) return false;
      const formula = val.vals[1];
      if (this.isAtomic(formula)) return false;
      return this.isPositive(val);
    });

    if (leftId) return leftId;

    // 3. Special case: Monad on right
    if (succedent.isMonad && succedent.isMonad()) {
      return 'R';
    }

    return false;
  }

  /**
   * Get potential rules for a focused formula
   */
  getPotentialRules(pt, position, ruleGetter) {
    const formula = position === 'R'
      ? pt.conclusion.succedent.vals[1]
      : pt.conclusion.linear_ctx[position].val.vals[1];

    const type = Calc.db.rules[formula.id];
    const match = type.ruleName.match(/Formula_(.*)/);
    if (!match) return [];

    const connective = match[1];
    const side = position === 'R' ? 'R' : 'L';
    const ruleName = `${connective}_${side}`;

    // Check for alternative rules (e.g., With_L2)
    const potRules = [ruleName];
    if (ruleGetter(`${ruleName}2`)) {
      potRules.push(`${ruleName}2`);
    }

    return potRules;
  }

  /**
   * Choose which formula to focus on
   * Returns array of {position, id} choices
   */
  chooseFocus(pt) {
    const choices = [];
    const seq = pt.conclusion;

    // Positive on right can be focused
    if (seq.succedent.vals && seq.succedent.vals[1]) {
      if (this.isPositive(seq.succedent)) {
        choices.push({ position: 'R', id: null });
      }
    }

    // Negative on left can be focused
    Object.keys(seq.linear_ctx).forEach(id => {
      const val = seq.linear_ctx[id].val;
      if (this.isNegative(val)) {
        choices.push({ position: 'L', id });
      }
    });

    return choices.reverse();  // Try left first (like original)
  }

  /**
   * Try identity rule for positive atom on right
   */
  tryIdentityPositive(pt, state) {
    const formula = pt.conclusion.succedent.vals[1];
    const ctx = pt.conclusion.linear_ctx;

    let theta;
    const matchId = Object.keys(ctx).find(id => {
      const ctxFormula = ctx[id].val.vals[1];
      theta = mgu([[ctxFormula, formula]]);
      return !!theta;
    });

    if (!matchId) return false;

    // Apply substitution
    theta.forEach(([k, v]) => {
      pt.conclusion.succedent = substitute(pt.conclusion.succedent, k, v);
    });

    // Consume the matching formula from context
    const linear_ctx_ = { [matchId]: { num: 1, val: ctx[matchId].val } };
    Sequent.remove_from_antecedent(pt.conclusion, linear_ctx_);

    const delta_out = pt.conclusion.linear_ctx;
    pt.conclusion.linear_ctx = linear_ctx_;
    pt.type = "Id_+";

    return { theta, delta_out };
  }

  /**
   * Try identity rule for negative atom on left
   */
  tryIdentityNegative(pt, state) {
    const focusId = state.focusId;
    const focusedFormula = pt.conclusion.linear_ctx[focusId].val.vals[1];
    const succFormula = pt.conclusion.succedent.vals[1];

    const theta = mgu([[focusedFormula, succFormula]]);
    if (!theta) return false;

    // Apply substitution
    theta.forEach(([k, v]) => {
      pt.conclusion.succedent = substitute(pt.conclusion.succedent, k, v);
    });

    // Consume the focused formula
    const linear_ctx_ = { [focusId]: { num: 1, val: pt.conclusion.linear_ctx[focusId].val } };
    Sequent.remove_from_antecedent(pt.conclusion, linear_ctx_);

    const delta_out = pt.conclusion.linear_ctx;
    pt.conclusion.linear_ctx = linear_ctx_;
    pt.type = "Id_-";

    return { theta, delta_out };
  }

  /**
   * Apply a rule at a given position
   */
  applyRule(pt, ruleName, position, rule) {
    const formula = position === 'R'
      ? pt.conclusion.succedent.vals[1]
      : pt.conclusion.linear_ctx[position].val.vals[1];

    const type = Calc.db.rules[formula.id];
    const name = type.ruleName;

    // Copy rule and propagate persistent context
    rule = rule.map(seq => {
      Object.keys(pt.conclusion.persistent_ctx).forEach(id => {
        seq.persistent_ctx[id] = pt.conclusion.persistent_ctx[id].copy();
      });
      return seq;
    });

    // Compute MGU
    let theta;
    if (position !== 'R') {
      // Left rule: find principal formula in rule by connective name
      const conclusionConnectiveId = Object.keys(rule[0].linear_ctx).find(id => {
        const r = rule[0].linear_ctx[id];
        const isFormula = r.val.isTermType();
        return isFormula && Calc.db.rules[r.val.vals[1].id].ruleName === name;
      });

      if (!conclusionConnectiveId) return false;
      const conclusionConnective = rule[0].linear_ctx[conclusionConnectiveId].val;

      theta = mgu([[conclusionConnective, pt.conclusion.linear_ctx[position].val]]);
      const theta2 = mgu([[rule[0].succedent, pt.conclusion.succedent]]);

      if (!theta || !theta2) return false;

      // Merge thetas
      const theta_keys = theta.map(([a, _]) => a.toString());
      const theta2_key = theta2[0] ? theta2[0][0].toString() : null;

      if (theta2.length > 0 && theta2_key && theta_keys.indexOf(theta2_key) === -1) {
        theta = theta.concat(theta2);
      }
    } else {
      // Right rule: match succedent
      theta = mgu([[rule[0].succedent, pt.conclusion.succedent]]);
      if (!theta) return false;
    }

    // Special case: Bang_L promotes to persistent context
    if (ruleName === "Bang_L") {
      rule.forEach((seq, i) => {
        if (i === 0) return;
        const r = pt.conclusion.linear_ctx[position].val.copy();
        r.vals[1] = r.vals[1].vals[0];
        seq.persistent_ctx[position] = r;
      });
    }

    // Build premises
    pt.premisses = rule.slice(1)
      .map(seq => seq.substitute(theta))
      .map(seq => new PT({ conclusion: seq }));

    // Track consumed resources
    const rmIds = position === 'R' ? [] : [position];
    const linear_ctx = {};
    Object.keys(pt.conclusion.linear_ctx).forEach(id => {
      if (rmIds.indexOf(id) === -1) {
        const r = pt.conclusion.linear_ctx[id];
        linear_ctx[id] = { num: r.num, val: r.val };
      }
    });

    pt.delta_in = linear_ctx;
    pt.type = ruleName;

    return { success: true, theta };
  }

  /**
   * Main proof search entry point
   */
  auto(pt, options = {}) {
    const o = Object.assign({
      negative: [],
      positive: [],
      affine: false,
      mode: 'proof',
      getRule: (name) => options.rules && options.rules[name],
      rules: options.rules || {},
      bwd: options.bwd || []
    }, options);

    // Get or create prover state
    const state = pt.proverState || new ProofSearchState();
    pt.proverState = state;

    let success = false;
    let delta_out = {};
    let theta = [];
    const debug = { technique: '' };

    const free_vars = Sequent.getFreeVariables(pt.conclusion).map(v => v.vals[0]);

    if (pt.type !== "???") return { success: false, delta_out, theta, debug: { head: debug, children: [] } };

    // Phase 1: Inversion - apply invertible rules eagerly
    const invertibleId = this.getInvertibleRule(pt);
    if (invertibleId) {
      const formula = invertibleId === 'R'
        ? pt.conclusion.succedent.vals[1]
        : pt.conclusion.linear_ctx[invertibleId].val.vals[1];

      const type = Calc.db.rules[formula.id];
      const match = type.ruleName.match(/Formula_(.*)/);
      if (match) {
        const ruleName = match[1] + '_' + (invertibleId === 'R' ? 'R' : 'L');
        debug.technique = `invert.${ruleName}`;

        const rule = o.getRule(ruleName);
        if (rule) {
          const result = this.applyRule(pt, ruleName, invertibleId, rule);
          if (result && result.success) {
            return this.continueProof(pt, o, state, result.theta || [], debug);
          }
        }
      }
    }

    // Phase 2: Focus - choose a formula to focus on
    if (!state.isFocused()) {
      // Check for lax/proof mode
      if (pt.conclusion.succedent.isLax && pt.conclusion.succedent.isLax() || o.mode === 'proof') {
        const choices = this.chooseFocus(pt);
        debug.technique = `focus [${choices.length} choices]`;

        for (const choice of choices) {
          state.focus(choice.position, choice.id);
          const result = this.auto(pt, o);
          if (result.success) return result;
          state.blur();
        }
      }
    }

    // Phase 3: Focused decomposition
    if (state.isFocused()) {
      const position = state.focusPosition;
      const focusId = state.focusId;

      const formula = position === 'R'
        ? pt.conclusion.succedent.vals[1]
        : pt.conclusion.linear_ctx[focusId].val.vals[1];

      const isAtom = this.isAtomic(formula);

      if (isAtom) {
        // Try identity rules
        if (position === 'R' && this.isPositive(pt.conclusion.succedent)) {
          debug.technique = 'id+';
          const result = this.tryIdentityPositive(pt, state);
          if (result) {
            pt.delta_in = result.delta_out;
            return {
              success: true,
              delta_out: result.delta_out,
              theta: result.theta,
              debug: { head: debug, children: [] }
            };
          }
        } else if (position === 'L' && this.isNegative(pt.conclusion.linear_ctx[focusId].val)) {
          debug.technique = 'id-';
          const result = this.tryIdentityNegative(pt, state);
          if (result) {
            pt.delta_in = result.delta_out;
            return {
              success: true,
              delta_out: result.delta_out,
              theta: result.theta,
              debug: { head: debug, children: [] }
            };
          }
        }
      } else {
        // Apply focused rule
        const potRules = this.getPotentialRules(pt, position === 'R' ? 'R' : focusId, o.getRule);
        debug.technique = `focused.${potRules.join('|')}`;

        for (const ruleName of potRules) {
          const rule = o.getRule(ruleName);
          if (!rule) continue;

          const result = this.applyRule(pt, ruleName, position === 'R' ? 'R' : focusId, rule);
          if (result && result.success) {
            // Propagate focus state to premises
            pt.premisses.forEach(p => {
              p.proverState = state.copy();
            });
            return this.continueProof(pt, o, state, result.theta || [], debug);
          }
        }
      }

      // Blur if nothing worked
      state.blur();
    }

    pt.proven = false;
    return {
      success: false,
      delta_out,
      theta,
      debug: { head: debug, children: [] }
    };
  }

  /**
   * Continue proof search on premises
   */
  continueProof(pt, o, state, theta, debug) {
    let success = true;
    let delta = pt.delta_in ? { ...pt.delta_in } : {};
    const debug_children = [];

    const propagate = pt.type === "With_R";  // With copies context

    for (let j = 0; j < pt.premisses.length; j++) {
      if (propagate) {
        delta = pt.delta_in ? { ...pt.delta_in } : {};
      }

      const ptp = pt.premisses[j];
      if (theta.length > 0) ptp.conclusion.substitute(theta);
      Sequent.add_to_antecedent_bulk(ptp.conclusion, delta);
      Sequent.remove_structural_variables(ptp.conclusion);

      const result = this.auto(ptp, o);
      debug_children.push(result.debug);

      success = result.success;
      if (!success) break;

      // Propagate theta
      theta = theta.map(([k, v]) => {
        let new_value = v;
        result.theta.forEach(([k_, v_]) => {
          new_value = substitute(new_value, k_, v_);
        });
        return [k, new_value];
      });
      theta = theta.concat(result.theta);
      delta = result.delta_out;
    }

    if (pt.premisses.length === 0) success = true;

    const delta_out = delta;
    const affine = !("affine" in o);
    success = success && (!affine || Object.keys(delta_out).length === 0);

    if (theta) {
      pt.conclusion.substitute(theta);
    }
    pt.proven = success;
    pt.delta_out = delta_out;

    return {
      success,
      delta_out,
      theta,
      debug: { head: debug, children: debug_children }
    };
  }
}

module.exports = {
  ProofSearchState,
  FocusedProver
};
