// TODO - maybe subsitude potential imediatelly into the linear_ctx and remove it on back propagation
const clc = require('cli-color');

const Node = require("./node.js");
const PT = require("./pt.js");
const calc = require('../ll.json');
const compare = require('./compare.js');
const Sequent = require("../lib/sequent.js");

const calcParser = require("../lib/parser.js");
const Parser = calcParser(calc);
const parser = Parser.parser;

const rules = {};
Object.keys(calc.rules)
  .forEach(ctxName => {
  if(ctxName === "RuleStruct") return null;
  let ctx = calc.rules[ctxName];
  Object.keys(ctx).forEach(ruleName => {
    rules[ruleName] = ctx[ruleName];
    // let ruleNode = parser.parse(rule[0])
    // let potSeq = Sequent.fromTree(ruleNode)
    // let res = Sequent.compare(potSeq, seq);
  })
})

class Proofstate {}

// returns a complex connective which can be inverted
Proofstate.getInvertableRule = function (pt) {
  let succedent = pt.conclusion.succedent;
  let linear_ctx = pt.conclusion.linear_ctx;

  // 1. test wether succedent is negative
  // 2. test if a connective in the linear_ctx is positive
  let succPositive =
    succedent.ruleConstructor !== "Formula_Freevar"
    // && succedent.ruleConstructor !== "Structure_Focused_Term_Formula"
    && succedent.vals[1].getPolarity() === "negative";
  if(succPositive) return "R"

  let id = Object.keys(linear_ctx)
  .find(id => linear_ctx[id].val.ruleConstructor !== "Formula_Freevar" && linear_ctx[id].val.vals[1].getPolarity() === "positive")

  if(id) return id;

  return false;
}

Proofstate.auto = function(pt, o) {
  let affine = o.affine;

  if(o.debug) console.log(`\n\nauto:\n${pt.conclusion}`);

  if(pt.type !== "???") return false;

  // propagate auto solver to the premisses
  const exec = function () {
    let delta = pt.delta_in;
    for(let i=0; i < pt.premisses.length; i++) {
      let ptp = pt.premisses[i];
      Sequent.add_to_antecedent_bulk(ptp.conclusion, delta);
      Sequent.remove_structural_variables(ptp.conclusion);
      let delta_ = Proofstate.auto(ptp, o);
      if(!delta_) {
        return false;
        console.log(clc.red(`ERROR: no delta out received, therefore couldn't proove sequent: \n${ptp.conclusion}`));
      }
      delta = delta_;
    }
    // console.log(`pt ${pt.type} delta: ${Object.keys(delta)}`);
    pt.delta_out = delta;
    return delta;
  }

  o = Object.assign({
    negative: [],
    positive: [],
    affine: true
  }, o)

  let delta_out = {};

  let isFocused = pt.conclusion.focus;
  // console.log(!!isFocused);
  // console.log(pt.toString());
  let invertableRule = Proofstate.getInvertableRule(pt);

  if(invertableRule) {
    let formula = invertableRule === "R"
      ? pt.conclusion.succedent.vals[1]
      : pt.conclusion.linear_ctx[invertableRule].val.vals[1]
    let name = formula.ruleConstructor;
    let ruleName = name.match(/(Formula_(.*))/)[2];
    let fullname = ruleName + "_" + (invertableRule === "R" ? invertableRule : "L");
    Proofstate.apply(pt, fullname, invertableRule)
    pt.type = fullname;
    delta_out = exec();
  } else if(isFocused) {
    let formula = pt.conclusion.focus.vals[1].vals[0];
    let name = formula.ruleConstructor;
    let pos = pt.conclusion.focusPosition;
    let isComplex = name !== "Formula_Freevar" && name !== "Formula_Atprop";
    let pol = formula.getPolarity(o);

    let doBlur = (pol === "negative" && pos === "R")
              || (pol === "positive" && pos === "L")

    if(doBlur) {
      Proofstate.blur(pt, pos);
      delta_out = exec();
    } else if(isComplex) {
      let ruleName = name.match(/(Formula_(.*))/)[2];
      let fullname = ruleName + "_" + pos;

      let isRight = pt.conclusion.focus === pt.conclusion.succedent;
      let id = isRight
        ? "R"
        : pt.conclusion.focusId;

      let pot_rules = Proofstate.getPotRules(pt, id)
      // todo - fork
      let success;
      for(let i=0; i<pot_rules.length; i++) {
        success = Proofstate.apply(pt, pot_rules[i], id);
        if(!success) {
          delta_out = false;
          continue;
        }
        pt.type = fullname;
        delta_out = exec();
        if(delta_out) break;
      }
    } else { // Freevar in focus
      let isRight = pos === "R";
      let isLeft = pos === "L";
      let isNegative = o.negative
        .indexOf(formula.toString()) > -1;
      let isPositive = o.positive
        .indexOf(formula.toString()) > -1;

      if(isLeft && isNegative) {
        delta_out = Proofstate.tryIdNeg(pt);
        pt.delta_in = delta_out;
      } else if(isRight && isPositive) {
        console.log(`todo: Id_Pos`);
      }
      delta_out = exec();
    }
  } else { // nothing in focus
    // FOCUS
    let seq = pt.conclusion;
    let suc = seq.succedent.vals[1];

    let isRightFocusable = suc.getPolarity(o) === "positive";

    let filter = isRightFocusable ? ["R"] : [];
    let leftFilter = Object.keys(seq.linear_ctx)
    .filter(id => {
      let r = seq.linear_ctx[id].val;
      return r.ruleConstructor !== "Structure_Freevar"
        && r.vals[1].getPolarity(o) === "negative"
    })

    filter = filter.concat(leftFilter);

    let delta = false;
    for (var i = 0; i < filter.length; i++) {
      if(filter[i] === "R") {
        if(o.debug && filter.length > 1) console.log(`NONDETERMINISM: focusing on ${pt.conclusion.succedent}`);
        Proofstate.focusR(pt);
      } else {
        if(o.debug && filter.length > 1) console.log(`NONDETERMINISM: focusing on ${pt.conclusion.linear_ctx[filter[i]].val}`);
        Proofstate.focusL(pt, filter[i])
      }
      delta = exec();
      if(delta) break;
    }
    delta_out = delta;
  }

  if(!affine && Object.keys(delta_out).length > 0) delta_out = false;
  // todo - respect num
  if(!Object.keys(delta_out).reduceRight((a, id) => a && Object.keys(pt.delta_in).indexOf(id) > -1, true)) {
    delta_out = false;
  } else {
    pt.conclusion.linear_ctx = Sequent.remove_from_antecedent(pt.conclusion, delta_out)
  }

  return delta_out;
}


Proofstate.getPotRules = function (pt, id) {

  let formula = id === "R"
    ? pt.conclusion.succedent.vals[1]
    : pt.conclusion.linear_ctx[id].val.vals[1];
  let name = formula.ruleConstructor;
  let isFocused = name === "Focused_Formula"
  if(isFocused) {
    name = formula.vals[0].ruleConstructor;
  }
  let ruleName = name.match(/(Formula_(.*))/)[2];
  let fullname = ruleName + "_" + (id === "R" ? "R" : "L");
  // todo - this might be solved more beutifully
  let pot_rules = (fullname+"2" in rules)
    ? [fullname, fullname+"2"]
    : [fullname]

  return pot_rules;
}

Proofstate.apply = function (pt, fullname, id) {
  let formula = id === "R"
    ? pt.conclusion.succedent.vals[1]
    : pt.conclusion.linear_ctx[id].val.vals[1]
  let name = formula.ruleConstructor;
  let rule = rules[fullname]

  rule = rule
    .map(f => parser.parse(f))
    .map(f => Sequent.fromTree(f))

  let theta;
  if(id !== "R") {
    let conclusionConnectiveId = Object.keys(rule[0].linear_ctx)
      .find(id => {
        let r = rule[0].linear_ctx[id];
        let isFormula = r.val.ruleConstructor === "Structure_Term_Formula"
          || r.val.ruleConstructor === "Structure_Focused_Term_Formula"
        return isFormula && r.val.vals[1].ruleConstructor === name
      })
    let conclusionConnective = rule[0].linear_ctx[conclusionConnectiveId].val;

    theta = compare(conclusionConnective, pt.conclusion.linear_ctx[id].val)

    let theta2 = compare(rule[0].succedent, pt.conclusion.succedent);
    if(!theta || !theta2) return false;

    let theta_keys = theta.map(([a, _]) => a.toString());
    let theta2_key = theta2[0][0].toString();

    if(theta2.length > 0 && theta_keys.indexOf(theta2_key) === -1) {
      theta = theta.concat(theta2);
    } else {
      console.log(`todo - compare on equality of substitution, fail otherwise`);
    }
  } else {
    theta = compare(rule[0].succedent, pt.conclusion.succedent);
    if(!theta) return false;
  }

  pt.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    .map(seq => new PT({
      conclusion: seq,
    }))

  let rmIds = id === "R" ? [] : [id];
  let linear_ctx = Proofstate
    .copyMS(pt.conclusion.linear_ctx, rmIds);

  pt.delta_in = linear_ctx;

  return true;
}


// TODO - extend to different quantities on the succedent
Proofstate.tryIdNeg = function (pt) {
  let formula = pt.conclusion.focus.vals[1].vals[0];
  let isId = formula.toString() === pt.conclusion.succedent.vals[1].toString();
  let return_ = {};

  if(isId) {
    // clear structural variables, check if premisse is empty
    let id = Object.keys(pt.conclusion.linear_ctx)
    .find(id => pt.conclusion.linear_ctx[id].val === pt.conclusion.focus)
    let linear_ctx_ = {[id]: {
      num: 1,
      val: pt.conclusion.focus
    }}
    Sequent.remove_from_antecedent(pt.conclusion, linear_ctx_)
    return_ = pt.conclusion.linear_ctx;
    pt.conclusion.linear_ctx = linear_ctx_;
    pt.type = "Id_-"
  } else {
    return_ = false;
    // console.log(`nop: ${formula.toString()}  -- ${pt.conclusion.succedent.vals[1].toString()}`);
  }
  return return_;
}

Proofstate.focusR = function (pt) {
  let seq = Sequent.copy(pt.conclusion);

  pt.delta_in = seq.linear_ctx;
  seq.linear_ctx = {};
  seq.succedent.doFocus();
  seq.ffocus();

  let ptp = new PT({conclusion: seq});
  pt.premisses = [ptp];
  pt.type = "Focus_R"
}

Proofstate.focusL = function (pt, id) {
  let seq = Sequent.copy(pt.conclusion);
  let linear_ctx = {};
  let r = seq.linear_ctx[id]
  let linear_ctx_ = {[id]: {num:r.num, val: r.val}};
  pt.delta_in = Sequent.remove_from_antecedent(seq, linear_ctx_);
  seq.linear_ctx = linear_ctx_;
  linear_ctx_[id].val.doFocus();
  seq.ffocus();

  pt.premisses = [new PT({conclusion: seq})];
  pt.type = "Focus_L"
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

  // pt.delta_in = ;
  pt.delta_in = linear_ctx;
  pt.premisses = [new PT({conclusion: seq})];
  pt.type = "blur_" + pos;
}


// TODO - push this into Sequent?
Proofstate.getAtoms = function (seq) {

  const getAtoms = function (n) {
    if(n.ruleName != "Formula"
      || ((n.ruleConstructor !== "Formula_Freevar")
        && (n.ruleConstructor !== "Formula_Atprop"))
    ) {
      return n.vals
        .map(getAtoms)
        .reduceRight((a,e) => a.concat(e), []);
    } else {
      return [[n.toString(), n]];
    }
  }

  let atoms = Object.keys(seq.linear_ctx)
    .map(id => seq.linear_ctx[id].val)
    .map(getAtoms)
    .reduceRight((a,e) => a.concat(e), []);

  let aa = {};
  atoms.forEach(a => aa[a[0]] = true)

  return Object.keys(aa);
}

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
