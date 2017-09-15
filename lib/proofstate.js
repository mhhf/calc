// TODO - maybe subsitude potential imediatelly into the linear_ctx and remove it on back propagation
const clc = require('cli-color');

const Calc = require("./calc.js");

// const Node = require("./node.js");
const PT = require("./pt.js");
// const calc = require('../ll.json');
// const compare = require('./compare.js');
const Sequent = require("../lib/sequent.js");
const substitute = require('./substitute.js');
const mgu = require('./mgu.js');

// const calcParser = require("../lib/parser.js");
// const Parser = calcParser(calc);
// const parser = Parser.parser;

class Proofstate {}

// returns a complex connective which can be inverted
Proofstate.getInvertableRule = function (pt, o) {
  let succedent = pt.conclusion.succedent;
  let linear_ctx = pt.conclusion.linear_ctx;

  // 1. test wether succedent is negative
  // 2. test if a connective in the linear_ctx is positive
  let succPositive =
    (!succedent.isAtomic(o))
      // TODO - clean this by having a ! .isAtomic
    && succedent.vals[1].isNegative({positive: [], negative: []});
  if(succPositive) return "R"

  let id = Object.keys(linear_ctx)
  .find(id =>
    // TODO - this is ridicilous
    //        simplify this to .isType() or something
    linear_ctx[id].val.isTermType() && linear_ctx[id].val.vals[1].isPositive(o))

  if(id) return id;

  if(pt.conclusion.succedent.isMonad()) return "R";

  return false;
}


/*
 * Proofsearch is distributed in phaes:
 * 1. Invert a sequent untill it is stable
 * 2. ? focus and propagate focus
 * 3. ? blur
 */

let custom_rules_added = false;

// TODO - make intependent success variable
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

  if(o.debug) debug.goal = `${pt.conclusion}`//console.log(`\n\nauto:\n${pt}`);
  debug.technique = ``;

  if(pt.type !== "???") return false;

  o = Object.assign({
    negative: [],
    positive: [],
    affine: false
  }, o)

  let delta_out = {};
  let theta = [];

  let invertableId = Proofstate.getInvertableRule(pt, {positive: [], negative: []});

  if(invertableId) {
    let formula = invertableId === "R"
      ? pt.conclusion.succedent.vals[1]
      : pt.conclusion.linear_ctx[invertableId].val.vals[1]
    let name = Calc.db.rules[formula.id].ruleName;
    let ruleName = name.match(/(Formula_(.*))/)[2];
    let rule_name = ruleName + "_" + (invertableId === "R" ? invertableId : "L");

    debug.technique += `invert.${rule_name}`;

    actions.push(() => Proofstate.apply(pt, rule_name, invertableId, o.getRule(rule_name)))
  } else if(pt.conclusion.focus) { // focused
    debug.technique += `focused`;
    let formula = pt.conclusion.focus.vals[1].vals[0];
    let name = Calc.db.rules[formula.id].ruleName;
    let pos = pt.conclusion.focusPosition;
    let isComplex = name !== "Formula_Freevar" && name !== "Formula_Atprop";

    let doBlur = (formula.isNegative(o) && pos === "R")
              || (formula.isPositive(o) && pos === "L")

    if(doBlur) {
      debug.technique += `.blur `;
      actions.push(() => Proofstate.blur(pt, pos))
    } else if(isComplex) {
      let ruleName = name.match(/(Formula_(.*))/)[2];
      let rule_name = ruleName + "_" + pos;
      debug.technique += `.apply.${rule_name}`;

      let id = pos === "R"
        ? "R"
        : pt.conclusion.focusId;

      actions = Proofstate.getPotRules(pt, id, o).map(rule_name => () => Proofstate.apply(pt, rule_name, id, o.getRule(rule_name)))
    } else { // Atom in focus
      let isRight = pos === "R";
      let isLeft = pos === "L";
      let isNegative = formula.isNegative(o)
      // TODO - isPositive in the same fashion
      let isPositive = formula.isPositive(o)

      if(isLeft && isNegative) {
        debug.technique += `.id- `;
        let return_ = Proofstate.tryIdNeg(pt);
        if(return_) {
          delta_out = return_.delta_out;
          pt.delta_in = return_.delta_out;
          theta = return_.theta;
          success = true;
        } else {
          pt.delta_in = delta_out;
        }
      } else if(isRight && isPositive) {
        debug.technique += `.id+ `;
        let return_ = Proofstate.tryIdPos(pt);
        if(return_) {
          delta_out = return_.delta_out;
          pt.delta_in = return_.delta_out;
          theta = return_.theta;
          success = true;
        } else {
          pt.delta_in = delta_out;
        }
      } else {
        debug.technique += ` ${pos} ${formula}`
      }
    }
  } else if(pt.conclusion.succedent.isNegative(o)) {
    debug.technique += `bwd`;
    var rule;
    let rule_name = o.bwd.find(ruleName => {
      rule = o.getRule(ruleName);

      // TODO - you can do better then simple compare here
      // theta = Sequent.compare(pt.conclusion, rule[0]);
      theta = mgu([[pt.conclusion.succedent, rule[0].succedent]])
      return !!theta;
    });
    debug.rule = rule.map(r => r.toString())
    if(theta) debug.bwd_theta = theta.map(([k, v]) => `${k} -> ${v}`);
    debug.technique += "." + rule_name;
    // let rule = o.getRule(rule_name)
    actions.push(() => Proofstate.apply(pt, rule_name, "R", rule))
  } else if(pt.conclusion.succedent.isLax() || o.mode === "proof") {
    debug.technique += `fwd `;
    // FOCUS
    let seq = pt.conclusion;
    let suc = seq.succedent.vals[1];

    // let isRightFocusable = suc.getPolarity(o) === "positive";

    // let filter = isRightFocusable ? ["R"] : [];
    let filter = [];
    let leftFilter = Object.keys(seq.linear_ctx)
    .filter(id => seq.linear_ctx[id].val.isNegative(o))

    filter = filter.concat(leftFilter).reverse();

    debug.technique += filter
    .map(f => f.slice(0, 4)).join("|")

    actions = filter.map(id =>
      () => Proofstate.focus(pt, id)
    )
  }
  debug.num_actions = actions.length;

  if(o.debug_type === "live" && o.debug) console.log(debug);

  // For each nondeterministic choice
  for(var i = 0; i < actions.length; i++) {
    let ret = actions[i]();
    if(!ret.success) continue;
    let delta = Proofstate.copyMS(pt.delta_in);
    // TODO - get something better here which is a little bit more generic then one rule...
    // explanation: with_R has delta on left AND right and therefore is not object to ressource management
    let propagate = pt.type === "With_R";
    // Container for debug output of possible nondenterminism
    let nt_debug_children = [];
    // for each premisse
    for(let j=0; j < pt.premisses.length; j++) {
      if(propagate)
        delta = Proofstate.copyMS(pt.delta_in)
      let ptp = pt.premisses[j];
      theta.length > 0 && ptp.conclusion.substitute(theta)
      Sequent.add_to_antecedent_bulk(ptp.conclusion, delta);
      Sequent.remove_structural_variables(ptp.conclusion);
      // if(!debug.ptp) debug.ptp = [];
      // debug.ptp.push(ptp.conclusion.toString());
      let result = Proofstate.auto(ptp, o);
      success = result.success;
      nt_debug_children.push(result.debug)
      if(!success) break;
      debug.theta_native = theta.map(([k, v]) => `${k} -> ${v}`);
      debug.theta_propagated = result.theta
      .map(([k, v]) => `${k} -> ${v}`)
      // TODO - propagate theta
      // TODO - restrict theta to variables in pt.conclusion
      // propagate
      /// \theta \leftarrow \theta\theta'
      theta = theta.map(([k, v]) => {
        let new_value = v;
        result.theta.forEach(([k_, v_]) => {
          new_value = substitute(new_value, k_, v_)
        })
        return [k, new_value];
      })
      // concatenate
      theta = theta.concat(result.theta);
      debug["theta"+j] = theta.map(([k, v]) => `${k} -> ${v}`)
      delta = result.delta_out;
    }

    if(actions.length > 1) {
      debug_children.push({head: {
        technique: `nt.${i}`,
        premisses: pt.premisses.length
      }, children: nt_debug_children})
    } else {
      debug_children = nt_debug_children;
    }

    if(pt.premisses.length === 0) success = true;
    pt.delta_out = delta_out = delta;
    success = success
      && (!affine || Object.keys(delta_out).length === 0)
    if(success) break;
  }

  // todo - respect num
  if(!Object.keys(delta_out).reduceRight((a, id) => a && Object.keys(pt.delta_in).indexOf(id) > -1, true)) {
    success = false;
  } else {
    pt.conclusion.linear_ctx = Sequent.remove_from_antecedent(pt.conclusion, delta_out)
  }

  if(theta) {
    debug.theta = theta.map(([k,v]) => `${k} -> ${v}`);
    pt.conclusion.substitute(theta);
    // restrict to the domain
    /// \theta \leftarrow \theta|_{Dom(\theta)\cap free(seq)}
    theta = theta.filter(([k, v]) => {
      return free_vars.indexOf(k.vals[0]) > -1;
    })
  }
  pt.proven = success;

  debug.success = success;
  // debug.theta = theta
  // .map(([k, v]) => `${k} -> ${v}`);
  debug.premisses = pt.premisses.map(pt_ => pt_.conclusion.toString());
  debug.result = Sequent.copy(pt.conclusion)
  return {
    delta_out,
    theta,
    success,
    debug: {
      head: debug,
      children: debug_children
    }
  };
}


Proofstate.getPotRules = function (pt, id, o) {

  let formula = id === "R"
    ? pt.conclusion.succedent.vals[1]
    : pt.conclusion.linear_ctx[id].val.vals[1];
  let name = Calc.db.rules[formula.id].ruleName;
  let isFocused = name === "Focused_Formula"
  if(isFocused) {
    name = Calc.db.rules[formula.vals[0].id].ruleName;
  }
  let ruleName = name.match(/(Formula_(.*))/)[2];
  let rule_name = ruleName + "_" + (id === "R" ? "R" : "L");
  // todo - this might be solved more beutifully
  let pot_rules = (rule_name+"2" in o.rules)
    ? [rule_name, rule_name+"2"]
    : [rule_name]

  return pot_rules;
}

Proofstate.apply = function (pt, rule_name, id, rule) {
  let formula = id === "R"
    ? pt.conclusion.succedent.vals[1]
    : pt.conclusion.linear_ctx[id].val.vals[1]
  let name = Calc.db.rules[formula.id].ruleName;
  // let rule = o.rules[rule_name];

  rule = rule
    // .map(f => parser.parse(f))
    // .map(f => Sequent.fromTree(f))
    // .map(seq => Sequent.copy(seq))
    // propagate persistent ctx
    .map(seq => {
      Object.keys(pt.conclusion.persistent_ctx)
      .forEach(id => {
        seq.persistent_ctx[id] = pt.conclusion.persistent_ctx[id].copy();
      })
      return seq;
    })

  // let unique = Sequent.renameUnique(rule[0]);
  // rule = rule.map((seq, i) =>
  //   i === 0
  //   ? unique.seq
  //   : seq.substitute(unique.theta)
  // )

  let theta;
  if(id !== "R") {
    let conclusionConnectiveId = Object.keys(rule[0].linear_ctx)
      .find(id => {
        let r = rule[0].linear_ctx[id];
        let isFormula = r.val.isTermType();
        return isFormula && Calc.db.rules[r.val.vals[1].id].ruleName === name
      })
    let conclusionConnective = rule[0].linear_ctx[conclusionConnectiveId].val;

    theta = mgu([[conclusionConnective, pt.conclusion.linear_ctx[id].val]])

    let theta2 = mgu([[rule[0].succedent, pt.conclusion.succedent]]);
    if(!theta || !theta2) return false;

    let theta_keys = theta.map(([a, _]) => a.toString());
    let theta2_key = theta2[0][0].toString();

    if(theta2.length > 0 && theta_keys.indexOf(theta2_key) === -1) {
      theta = theta.concat(theta2);
    } else {
      console.log(`todo - compare on equality of substitution, fail otherwise`);
    }
  } else {
    theta = mgu([[rule[0].succedent, pt.conclusion.succedent]]);
    if(!theta) return false;
  }

  // Special cases
  if(rule_name === "Bang_L") {
    rule.forEach((seq, i) => {
      if(i === 0) return null;
      let r = pt.conclusion.linear_ctx[id].val.copy();
      r.vals[1] = r.vals[1].vals[0];
      seq.persistent_ctx[id] = r;
    })
  }

  pt.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    // .map(seq => {console.log(seq.toString()); return seq})
    .map(seq => new PT({
      conclusion: seq,
    }))

  let rmIds = id === "R" ? [] : [id];
  let linear_ctx = Proofstate
    .copyMS(pt.conclusion.linear_ctx, rmIds);

  pt.delta_in = linear_ctx;
  pt.type = rule_name;

  return {success: true};
}

Proofstate.tryIdPos = function (pt) {
  let formula = pt.conclusion.focus.vals[1].vals[0];
  let ctx = pt.conclusion.linear_ctx;
  var theta;
  let return_;
  let id = Object.keys(ctx).find(id => !!(theta = mgu([[ctx[id].val.vals[1], formula]])))

  if(id) {
    theta.forEach(([k, v]) => { pt.conclusion.succedent = substitute(pt.conclusion.succedent, k, v) })
    let linear_ctx_ = {[id]: {
      num: 1,
      val: ctx[id].val
    }}
    Sequent.remove_from_antecedent(pt.conclusion, linear_ctx_)
    return_ = {theta, delta_out: pt.conclusion.linear_ctx};
    pt.conclusion.linear_ctx = linear_ctx_;
    pt.type = "Id_+"
  } else {
    return false;
  }

  return return_;
}

// TODO - extend to different quantities on the succedent
Proofstate.tryIdNeg = function (pt) {
  let formula = pt.conclusion.focus.vals[1].vals[0];
  // let isId = formula.toString() === pt.conclusion.succedent.vals[1].toString();
  // assuming substitution is in normal form
  // TODO - normalize
  // TODO - do I have to do type checking here?
  let theta = mgu([[formula, pt.conclusion.succedent.vals[1]]])
  let return_;

  if(theta) {
    // clear structural variables, check if premisse is empty
    theta.forEach(([k, v]) => { pt.conclusion.succedent = substitute(pt.conclusion.succedent, k, v) })
    let id = Object.keys(pt.conclusion.linear_ctx)
    .find(id => pt.conclusion.linear_ctx[id].val === pt.conclusion.focus)
    let linear_ctx_ = {[id]: {
      num: 1,
      val: pt.conclusion.focus
    }}
    Sequent.remove_from_antecedent(pt.conclusion, linear_ctx_)
    return_ = {theta, delta_out: pt.conclusion.linear_ctx};
    pt.conclusion.linear_ctx = linear_ctx_;
    pt.type = "Id_-"
  } else {
    return_ = false;
  }
  return return_;
}

Proofstate.focus = function (pt, id) {
  let seq = Sequent.copy(pt.conclusion);
  // console.log(seq.toString());

  if(id === "R") {
    pt.delta_in = seq.linear_ctx;
    seq.linear_ctx = {};
    seq.succedent.doFocus();
  } else {
    let linear_ctx = {};
    let r = seq.linear_ctx[id]
    let linear_ctx_ = {[id]: {num:r.num, val: r.val}};
    pt.delta_in = Sequent.remove_from_antecedent(seq, linear_ctx_);
    seq.linear_ctx = linear_ctx_;
    linear_ctx_[id].val.doFocus();
  }

  seq.ffocus();
  pt.premisses = [new PT({conclusion: seq})];
  pt.type = "Focus_" + (id === "R" ? id : "L")
  return {success: true};
}

Proofstate.blur = function (pt, pos = "R") {
  let seq = Sequent.copy(pt.conclusion);
  Sequent.blur(seq);

  let rmIds = pos === "R" ? [] : [seq.focusId];

  let linear_ctx = Proofstate
    .copyMS(seq.linear_ctx, rmIds);

  let linear_ctx_ = {};

  rmIds.forEach(id => {
    linear_ctx_[id] = seq.linear_ctx[id];
  })

  seq.linear_ctx = linear_ctx_;

  seq.ffocus()

  pt.delta_in = linear_ctx;
  pt.premisses = [new PT({conclusion: seq})];
  pt.type = "blur_" + pos;
  return {success: true};
}


// TODO - push this into Sequent?
Proofstate.copyMS = function (ms, except = []) {
  let ms_ = {};
  Object.keys(ms).forEach(id => {
    let r = ms[id];
    if(except.indexOf(id) === -1)
      ms_[id] = {num: r.num, val: r.val}
  })
  return ms_;
}

module.exports = Proofstate;
