/**
 * Proofstate - Proof search interface
 *
 * This module provides the main API for automated proof search.
 * It delegates to the FocusedProver for the actual proof search strategy.
 *
 * Focus state is tracked externally (on ProofTree), not in sequent syntax.
 * This keeps the framework layer generic and separates the prover strategy.
 */

const clc = require('cli-color');

const Calc = require("./calc.js");
const PT = require("./pt.js");
const Sequent = require("./sequent.js");
const substitute = require('./substitute.js');
const mgu = require('./mgu.js');
const { FocusedProver, ProofSearchState } = require('./prover.js');

class Proofstate {}

// Singleton prover instance, initialized lazily
let _prover = null;

/**
 * Get or create the prover instance
 */
Proofstate.getProver = function() {
  if (!_prover) {
    _prover = new FocusedProver(Calc.db);
  }
  return _prover;
};

/**
 * Reset the prover (useful for testing)
 */
Proofstate.resetProver = function() {
  _prover = null;
};

/**
 * Check if a formula is atomic (not a complex connective)
 */
const isAtomicFormula = (formula) => {
  if (!formula || !formula.id) return true;
  let type = Calc.db.rules[formula.id];
  if (!type) return true;
  return type.ruleName === "Formula_Atprop" || type.ruleName === "Formula_Freevar";
};

/**
 * Find an invertible rule to apply
 * Returns position ('R' or left-context id) or false
 */
Proofstate.getInvertableRule = function (pt, o) {
  let succedent = pt.conclusion.succedent;
  let linear_ctx = pt.conclusion.linear_ctx;

  // 1. test whether succedent is negative (and not atomic)
  // Only complex negative formulas can be inverted on the right
  if (succedent.vals && succedent.vals[1]) {
    let formula = succedent.vals[1];
    let isNegative = succedent.isNegative && succedent.isNegative({positive: [], negative: []});
    let succNegative = !isAtomicFormula(formula) && isNegative;
    if (succNegative) return "R";
  }

  // 2. test if a complex connective in the linear_ctx is positive
  // Atomic positive formulas shouldn't be inverted - they're handled by Id
  let id = Object.keys(linear_ctx)
    .find(id => {
      let val = linear_ctx[id].val;
      if (!val.isTermType || !val.isTermType()) return false;
      let formula = val.vals[1];
      if (isAtomicFormula(formula)) return false;
      return formula.isPositive && formula.isPositive(o);
    });

  if (id) return id;

  if (pt.conclusion.succedent.isMonad && pt.conclusion.succedent.isMonad()) return "R";

  return false;
};

/**
 * Main proof search entry point
 *
 * @param {PT} pt - Proof tree node
 * @param {Object} o - Options including rules, mode, etc.
 * @returns {Object} - { success, delta_out, theta, debug }
 */
Proofstate.auto = function(pt, o) {
  let affine = !("affine" in o);
  let success = false;
  let actions = [];

  let debug = {};
  let debug_children = [];
  let free_vars = Sequent
    .getFreeVariables(pt.conclusion)
    .map(v => v.vals[0]);
  debug.goal_free_vars = free_vars.join(", ");

  if (o.debug) debug.goal = `${pt.conclusion}`;
  debug.technique = ``;

  if (pt.type !== "???") return { success: false, delta_out: {}, theta: [], debug: { head: debug, children: [] } };

  o = Object.assign({
    negative: [],
    positive: [],
    affine: false
  }, o);

  let delta_out = {};
  let theta = [];

  // Get or create prover state on the proof tree
  let state = pt.proverState || new ProofSearchState();
  pt.proverState = state;

  let invertableId = Proofstate.getInvertableRule(pt, {positive: [], negative: []});

  if (invertableId) {
    // Inversion phase: apply invertible rules
    let formula = invertableId === "R"
      ? pt.conclusion.succedent.vals[1]
      : pt.conclusion.linear_ctx[invertableId].val.vals[1];
    let name = Calc.db.rules[formula.id].ruleName;
    let ruleName = name.match(/(Formula_(.*))/)[2];
    let rule_name = ruleName + "_" + (invertableId === "R" ? invertableId : "L");

    debug.technique += `invert.${rule_name}`;

    actions.push(() => Proofstate.apply(pt, rule_name, invertableId, o.getRule(rule_name)));
  } else if (state.isFocused()) {
    // Focus phase: decompose focused formula
    debug.technique += `focused`;
    let position = state.focusPosition;
    let focusId = state.focusId;

    // For left focus, verify the focused formula is still in context
    if (position === 'L' && (!focusId || !pt.conclusion.linear_ctx[focusId])) {
      // Focus target not found - blur and retry
      state.blur();
      return Proofstate.auto(pt, o);
    }

    let formula = position === 'R'
      ? pt.conclusion.succedent.vals[1]
      : pt.conclusion.linear_ctx[focusId].val.vals[1];

    let name = Calc.db.rules[formula.id].ruleName;
    let isComplex = name !== "Formula_Freevar" && name !== "Formula_Atprop";

    let isNeg = formula.isNegative && formula.isNegative(o);
    let isPos = formula.isPositive && formula.isPositive(o);
    let doBlur = (isNeg && position === "R") || (isPos && position === "L");

    if (doBlur) {
      debug.technique += `.blur `;
      state.blur();
      // Retry with blurred state
      return Proofstate.auto(pt, o);
    } else if (isComplex) {
      let ruleName = name.match(/(Formula_(.*))/)[2];
      let rule_name = ruleName + "_" + position;
      debug.technique += `.apply.${rule_name}`;

      let id = position === "R" ? "R" : focusId;
      actions = Proofstate.getPotRules(pt, id, o).map(rule_name =>
        () => Proofstate.apply(pt, rule_name, id, o.getRule(rule_name))
      );
    } else {
      // Atom in focus - try identity
      let isRight = position === "R";
      let isLeft = position === "L";
      let isNegative = formula.isNegative && formula.isNegative(o);
      let isPositive = formula.isPositive && formula.isPositive(o);

      if (isLeft && isNegative) {
        debug.technique += `.id- `;
        let return_ = Proofstate.tryIdNeg(pt, state);
        if (return_) {
          delta_out = return_.delta_out;
          pt.delta_in = return_.delta_out;
          theta = return_.theta;
          success = true;
        } else {
          pt.delta_in = delta_out;
        }
      } else if (isRight && isPositive) {
        debug.technique += `.id+ `;
        let return_ = Proofstate.tryIdPos(pt, state);
        if (return_) {
          delta_out = return_.delta_out;
          pt.delta_in = return_.delta_out;
          theta = return_.theta;
          success = true;
        } else {
          pt.delta_in = delta_out;
        }
      } else {
        debug.technique += ` ${position} ${formula}`;
      }
    }
  } else if (pt.conclusion.succedent.isNegative && pt.conclusion.succedent.isNegative(o)) {
    // Backward chaining
    debug.technique += `bwd`;
    var rule;
    let rule_name = o.bwd.find(ruleName => {
      rule = o.getRule(ruleName);
      theta = mgu([[pt.conclusion.succedent, rule[0].succedent]]);
      return !!theta;
    });
    if (rule) {
      debug.rule = rule.map(r => r.toString());
      if (theta) debug.bwd_theta = theta.map(([k, v]) => `${k} -> ${v}`);
      debug.technique += "." + rule_name;
      actions.push(() => Proofstate.apply(pt, rule_name, "R", rule));
    }
  } else if ((pt.conclusion.succedent.isLax && pt.conclusion.succedent.isLax()) || o.mode === "proof") {
    // Forward chaining: choose focus
    debug.technique += `fwd `;
    let seq = pt.conclusion;
    let suc = seq.succedent.vals[1];

    // Focus on positive atoms on the right (for identity proofs)
    let isRightFocusable = suc && suc.isPositive && suc.isPositive(o);

    let filter = isRightFocusable ? ["R"] : [];
    let leftFilter = Object.keys(seq.linear_ctx)
      .filter(id => {
        let val = seq.linear_ctx[id].val;
        return val.isNegative && val.isNegative(o);
      });

    filter = filter.concat(leftFilter).reverse();

    debug.technique += filter
      .map(f => f.slice(0, 4)).join("|");

    actions = filter.map(id =>
      () => Proofstate.focus(pt, id)
    );
  }

  debug.num_actions = actions.length;

  if (o.debug_type === "live" && o.debug) console.log(debug);

  // For each nondeterministic choice
  for (var i = 0; i < actions.length; i++) {
    let ret = actions[i]();
    if (!ret.success) continue;
    let delta = Proofstate.copyMS(pt.delta_in);
    let propagate = pt.type === "With_R";
    let nt_debug_children = [];

    // for each premise
    for (let j = 0; j < pt.premisses.length; j++) {
      if (propagate)
        delta = Proofstate.copyMS(pt.delta_in);
      let ptp = pt.premisses[j];
      theta.length > 0 && ptp.conclusion.substitute(theta);
      Sequent.add_to_antecedent_bulk(ptp.conclusion, delta);
      Sequent.remove_structural_variables(ptp.conclusion);

      let result = Proofstate.auto(ptp, o);
      success = result.success;
      nt_debug_children.push(result.debug);
      if (!success) break;
      debug.theta_native = theta.map(([k, v]) => `${k} -> ${v}`);
      debug.theta_propagated = result.theta.map(([k, v]) => `${k} -> ${v}`);

      // Propagate theta
      theta = theta.map(([k, v]) => {
        let new_value = v;
        result.theta.forEach(([k_, v_]) => {
          new_value = substitute(new_value, k_, v_);
        });
        return [k, new_value];
      });
      theta = theta.concat(result.theta);
      debug["theta" + j] = theta.map(([k, v]) => `${k} -> ${v}`);
      delta = result.delta_out;
    }

    if (actions.length > 1) {
      debug_children.push({
        head: {
          technique: `nt.${i}`,
          premisses: pt.premisses.length
        },
        children: nt_debug_children
      });
    } else {
      debug_children = nt_debug_children;
    }

    if (pt.premisses.length === 0) success = true;
    pt.delta_out = delta_out = delta;
    success = success && (!affine || Object.keys(delta_out).length === 0);
    if (success) break;
  }

  // Verify resources
  if (!Object.keys(delta_out).reduceRight((a, id) => a && Object.keys(pt.delta_in).indexOf(id) > -1, true)) {
    success = false;
  } else if (pt.conclusion.linear_ctx) {
    pt.conclusion.linear_ctx = Sequent.remove_from_antecedent(pt.conclusion, delta_out) || pt.conclusion.linear_ctx;
  }

  if (theta) {
    debug.theta = theta.map(([k, v]) => `${k} -> ${v}`);
    pt.conclusion.substitute(theta);
    theta = theta.filter(([k, v]) => {
      return free_vars.indexOf(k.vals[0]) > -1;
    });
  }
  pt.proven = success;

  debug.success = success;
  debug.premisses = pt.premisses.map(pt_ => pt_.conclusion.toString());
  debug.result = Sequent.copy(pt.conclusion);
  return {
    delta_out,
    theta,
    success,
    debug: {
      head: debug,
      children: debug_children
    }
  };
};

/**
 * Get potential rules for a formula at position
 */
Proofstate.getPotRules = function (pt, id, o) {
  let formula = id === "R"
    ? pt.conclusion.succedent.vals[1]
    : pt.conclusion.linear_ctx[id].val.vals[1];
  let name = Calc.db.rules[formula.id].ruleName;
  let ruleName = name.match(/(Formula_(.*))/)[2];
  let rule_name = ruleName + "_" + (id === "R" ? "R" : "L");

  let pot_rules = (rule_name + "2" in o.rules)
    ? [rule_name, rule_name + "2"]
    : [rule_name];

  return pot_rules;
};

/**
 * Apply a rule at position
 */
Proofstate.apply = function (pt, rule_name, id, rule) {
  let formula = id === "R"
    ? pt.conclusion.succedent.vals[1]
    : pt.conclusion.linear_ctx[id].val.vals[1];
  let name = Calc.db.rules[formula.id].ruleName;

  rule = rule
    .map(seq => {
      Object.keys(pt.conclusion.persistent_ctx)
        .forEach(id => {
          seq.persistent_ctx[id] = pt.conclusion.persistent_ctx[id].copy();
        });
      return seq;
    });

  let theta;
  if (id !== "R") {
    let conclusionConnectiveId = Object.keys(rule[0].linear_ctx)
      .find(id => {
        let r = rule[0].linear_ctx[id];
        let isFormula = r.val.isTermType();
        return isFormula && Calc.db.rules[r.val.vals[1].id].ruleName === name;
      });

    if (!conclusionConnectiveId) return { success: false };

    let conclusionConnective = rule[0].linear_ctx[conclusionConnectiveId].val;

    theta = mgu([[conclusionConnective, pt.conclusion.linear_ctx[id].val]]);

    let theta2 = mgu([[rule[0].succedent, pt.conclusion.succedent]]);
    if (!theta || !theta2) return { success: false };

    let theta_keys = theta.map(([a, _]) => a.toString());
    let theta2_key = theta2[0] ? theta2[0][0].toString() : null;

    if (theta2.length > 0 && theta2_key && theta_keys.indexOf(theta2_key) === -1) {
      theta = theta.concat(theta2);
    }
  } else {
    theta = mgu([[rule[0].succedent, pt.conclusion.succedent]]);
    if (!theta) return { success: false };
  }

  // Special cases
  if (rule_name === "Bang_L") {
    rule.forEach((seq, i) => {
      if (i === 0) return null;
      let r = pt.conclusion.linear_ctx[id].val.copy();
      r.vals[1] = r.vals[1].vals[0];
      seq.persistent_ctx[id] = r;
    });
  }

  pt.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    .map(seq => new PT({
      conclusion: seq,
      proverState: pt.proverState ? pt.proverState.copy() : null
    }));

  let rmIds = id === "R" ? [] : [id];
  let linear_ctx = Proofstate.copyMS(pt.conclusion.linear_ctx, rmIds);

  pt.delta_in = linear_ctx;
  pt.type = rule_name;

  return { success: true, theta };
};

/**
 * Try identity rule for positive atom on right
 */
Proofstate.tryIdPos = function (pt, state) {
  let formula = pt.conclusion.succedent.vals[1];
  let ctx = pt.conclusion.linear_ctx;
  var theta;
  let return_;
  let id = Object.keys(ctx).find(id => {
    let ctxFormula = ctx[id].val.vals[1];
    return !!(theta = mgu([[ctxFormula, formula]]));
  });

  if (id) {
    theta.forEach(([k, v]) => {
      pt.conclusion.succedent = substitute(pt.conclusion.succedent, k, v);
    });
    let linear_ctx_ = {
      [id]: {
        num: 1,
        val: ctx[id].val
      }
    };
    Sequent.remove_from_antecedent(pt.conclusion, linear_ctx_);
    return_ = { theta, delta_out: pt.conclusion.linear_ctx };
    pt.conclusion.linear_ctx = linear_ctx_;
    pt.type = "Id_+";
  } else {
    return false;
  }

  return return_;
};

/**
 * Try identity rule for negative atom on left
 */
Proofstate.tryIdNeg = function (pt, state) {
  let focusId = state.focusId;
  let formula = pt.conclusion.linear_ctx[focusId].val.vals[1];
  let theta = mgu([[formula, pt.conclusion.succedent.vals[1]]]);
  let return_;

  if (theta) {
    theta.forEach(([k, v]) => {
      pt.conclusion.succedent = substitute(pt.conclusion.succedent, k, v);
    });
    let linear_ctx_ = {
      [focusId]: {
        num: 1,
        val: pt.conclusion.linear_ctx[focusId].val
      }
    };
    Sequent.remove_from_antecedent(pt.conclusion, linear_ctx_);
    return_ = { theta, delta_out: pt.conclusion.linear_ctx };
    pt.conclusion.linear_ctx = linear_ctx_;
    pt.type = "Id_-";
  } else {
    return_ = false;
  }
  return return_;
};

/**
 * Focus on a formula (without modifying sequent syntax)
 *
 * In focused proof search, focus isolates the focused formula in the sequent:
 * - Left focus: sequent contains only the focused formula
 * - Right focus: sequent has empty left context
 *
 * The other formulas are stored in pt.delta_in for resource tracking by the
 * auto-prover, which adds them back to premises after rule application.
 *
 * For UI display, the parent node's conclusion shows all original formulas,
 * and the child (premise after focus) shows the focused view.
 */
Proofstate.focus = function (pt, id) {
  let seq = Sequent.copy(pt.conclusion);

  // Set up prover state to track focus
  let state = new ProofSearchState();

  if (id === "R") {
    state.focus('R', null);
    pt.delta_in = seq.linear_ctx;
    seq.linear_ctx = {};
  } else {
    state.focus('L', id);
    let r = seq.linear_ctx[id];
    let linear_ctx_ = { [id]: { num: r.num, val: r.val } };
    pt.delta_in = Sequent.remove_from_antecedent(seq, linear_ctx_);
    seq.linear_ctx = linear_ctx_;
  }

  pt.premisses = [new PT({ conclusion: seq, proverState: state })];
  pt.type = "Focus_" + (id === "R" ? id : "L");
  return { success: true };
};

/**
 * Copy multiset (excluding certain IDs)
 */
Proofstate.copyMS = function (ms, except = []) {
  let ms_ = {};
  Object.keys(ms).forEach(id => {
    let r = ms[id];
    if (except.indexOf(id) === -1)
      ms_[id] = { num: r.num, val: r.val };
  });
  return ms_;
};

module.exports = Proofstate;
