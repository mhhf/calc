// TODO - maybe subsitude potential imediatelly into the antecedent and remove it on back propagation
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

Proofstate.resPolarity = function (r, o = {positive: [], negative: []}) {
  let isVar = r.ruleConstructor === "Formula_Freevar";
  const polarityMap = calc.calc_structure_rules_meta.polarity;
  let isPositiveVar = (isVar && o.positive.indexOf(r.toString()) > -1);
  let isPositiveFormula = (!isVar && polarityMap[r.ruleConstructor] === "positive")
  let isPositive = isPositiveVar || isPositiveFormula;
  let isNegativeVar = (isVar && o.negative.indexOf(r.toString()) > -1);
  let isNegativeFormula = (!isVar && polarityMap[r.ruleConstructor] === "negative")
  let isNegative = isNegativeVar || isNegativeFormula;

  return isPositive ? "positive" : (isNegative ? "negative" : "")
}

// returns a complex connective which can be inverted
Proofstate.getInvertableRule = function (pt) {
  let succedent = pt.conclusion.succedent;
  let antecedent = pt.conclusion.antecedent;

  // 1. test wether succedent is negative
  // 2. test if a connective in the antecedent is positive
  let succPositive =
    succedent.ruleConstructor !== "Formula_Freevar"
    // && succedent.ruleConstructor !== "Structure_Focused_Term_Formula"
    && Proofstate.resPolarity(succedent.vals[1]) === "negative";
  if(succPositive) return "R"

  let id = Object.keys(antecedent)
  .find(id => antecedent[id].val.ruleConstructor !== "Formula_Freevar" && Proofstate.resPolarity(antecedent[id].val.vals[1]) === "positive")

  if(id) return id;

  return false;
}

Proofstate.auto = function(pt, o) {
  let affine = o.affine;

  if(o.debug) console.log(`\n\nauto:\n${pt}`);

  if(pt.type !== "???") return false;

  // propagate auto solver to the premisses
  const exec = function () {
    let delta = pt.delta_in;
    for(let i=0; i < pt.premisses.length; i++) {
      let ptp = pt.premisses[i];
      Sequent.add_to_antecedent(ptp.conclusion, delta);
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

  if(invertableRule && invertableRule === "R") {
    // console.log(`todo: invert ${pt.conclusion.succedent} on the right`);
    Proofstate.invertR(pt)
    delta_out = exec();
  } else if(invertableRule) {
    Proofstate.invertL(pt, invertableRule)
    delta_out = exec();
    // console.log(`compare ${compare(pt.conclusion.)}`);

  } else if(isFocused) {
    let formula = pt.conclusion.focus.vals[1].vals[0];
    let name = formula.ruleConstructor;
    let pos = pt.conclusion.focusPosition;
    let isComplex = name !== "Formula_Freevar";
    let pol = Proofstate.resPolarity(formula);

    if(isComplex && pol === "positive" && pos === "L") {
      Proofstate.blurL(pt);
      delta_out = exec();
    } else if(isComplex && pol === "negative" && pos === "R") {
      Proofstate.blurR(pt);
      delta_out = exec();
    } else if(isComplex) {
      let ruleName = name.match(/(Formula_(.*))/)[2];
      let fullname = ruleName + "_" + pos;
      let ruleNode = rules[fullname]
        .map(f => parser.parse(f))
        .map(f => Sequent.fromTree(f))


      let isRight = pt.conclusion.focus === pt.conclusion.succedent;
      let id = isRight
        ? "R"
        : pt.conclusion.focusId;
      let pot_rules = Proofstate.getPotRules(pt, id)
      // todo - fork
      let success;
      for(let i=0; i<pot_rules.length; i++) {
        if(isRight) {
          success = Proofstate.applyR(pt, pot_rules[i], id);
        } else {
          success = Proofstate.applyL(pt, pot_rules[i], id);
        }
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

      // TODO - populate and handle __out__;
      if(isLeft && isNegative) {
        delta_out = Proofstate.tryIdNeg(pt);
        pt.delta_in = delta_out;
      } else if(isLeft && isPositive) {
        Proofstate.blurL(pt);
      } else if(isRight && isNegative) {
        Proofstate.blurR(pt);
      } else if(isRight && isPositive) {
        console.log(`todo: Id_Pos`);
      }
      delta_out = exec();
    }
  } else { // nothing in focus
    // FOCUS
    let seq = pt.conclusion;
    let suc = seq.succedent.vals[1];

    let isRightFocusable = Proofstate.resPolarity(suc, o) === "positive";

    let filter = isRightFocusable ? ["R"] : [];
    let leftFilter = Object.keys(seq.antecedent)
    .filter(id => {
      let r = seq.antecedent[id].val;
      return r.ruleConstructor !== "Structure_Freevar"
        && Proofstate.resPolarity(r.vals[1], o) === "negative"
    })

    filter = filter.concat(leftFilter);

    let delta = false;
    for (var i = 0; i < filter.length; i++) {
      if(filter[i] === "R") {
        if(o.debug && filter.length > 1) console.log(`NONDETERMINISM: focusing on ${pt.conclusion.succedent}`);
        Proofstate.focusR(pt);
      } else {
        if(o.debug && filter.length > 1) console.log(`NONDETERMINISM: focusing on ${pt.conclusion.antecedent[filter[i]].val}`);
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
    pt.conclusion.antecedent = Sequent.remove_from_antecedent(pt.conclusion, delta_out)
  }

  return delta_out;
}


Proofstate.getPotRules = function (pt, id) {

  let formula = id === "R"
    ? pt.conclusion.succedent.vals[1]
    : pt.conclusion.antecedent[id].val.vals[1];
  let name = formula.ruleConstructor;
  let isFocused = name === "Focused_Formula"
  if(isFocused) {
    name = formula.vals[0].ruleConstructor;
  }
  let ruleName = name.match(/(Formula_(.*))/)[2];
  let fullname = ruleName + "_" + (id === "R" ? "R" : "L");
  // todo - this might be solved more beutifully
  let pot_rules = (fullname+"2" in rules)
    ? [rules[fullname], rules[fullname+"2"]]
    : [rules[fullname]]

  pot_rules = pot_rules
    .map(rule =>
        rule
          .map(f => parser.parse(f))
          .map(f => Sequent.fromTree(f))
    )

  return pot_rules;
}

Proofstate.applyR = function (pt, rule) {

  let theta = compare(rule[0].succedent, pt.conclusion.succedent);
  if(!theta) return false;

  pt.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    .map(seq => new PT({
      conclusion: seq,
    }))

  pt.delta_in = pt.conclusion.antecedent;
  return true;
}

Proofstate.applyL = function (pt, rule, id) {
  // todo - simplify
  let conclusionConnective = rule[0].focus;

  let theta = compare(conclusionConnective, pt.conclusion.antecedent[id].val)

  let theta2 = compare(rule[0].succedent, pt.conclusion.succedent);
  if(!theta || !theta2) return false;

  let theta_keys = theta.map(([a, _]) => a.toString());
  let theta2_key = theta2[0][0].toString();

  if(theta2.length > 0 && theta_keys.indexOf(theta2_key) === -1) {
    theta = theta.concat(theta2);
  } else {
    console.log(`todo - compare on equality of substitution, fail otherwise`);
  }

  pt.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    .map(seq => new PT({
      conclusion: seq,
    }))

  // todo - Sequent. remove from antecedent function?
  Object.keys(pt.conclusion.antecedent)
  .forEach(id_ => {
    let r = pt.conclusion.antecedent[id_].val;
    let isNotStructure = r.ruleConstructor !== "Structure_Freevar";
    let isNotActive = id_ !== id;
    if(isNotStructure && isNotActive) {
      pt.delta_in[id] = {
        val: r,
        num: pt.conclusion.antecedent[id].num
      }
    }
  })
  return true;
}


// TODO - extend to different quantities on the succedent
Proofstate.tryIdNeg = function (pt) {
  let formula = pt.conclusion.focus.vals[1].vals[0];
  let isId = formula.toString() === pt.conclusion.succedent.vals[1].toString();
  let return_ = {};

  if(isId) {
    // clear structural variables, check if premisse is empty
    let id = Object.keys(pt.conclusion.antecedent)
    .find(id => pt.conclusion.antecedent[id].val === pt.conclusion.focus)
    let antecedent_ = {[id]: {
      num: 1,
      val: pt.conclusion.focus
    }}
    Sequent.remove_from_antecedent(pt.conclusion, antecedent_)
    return_ = pt.conclusion.antecedent;
    pt.conclusion.antecedent = antecedent_;
    pt.type = "Id_-"
  } else {
    return_ = false;
    // console.log(`nop: ${formula.toString()}  -- ${pt.conclusion.succedent.vals[1].toString()}`);
  }
  return return_;
}

Proofstate.invertR = function (pt) {
  let formula = pt.conclusion.succedent.vals[1];
  let name = formula.ruleConstructor;
  let ruleName = name.match(/(Formula_(.*))/)[2];
  let fullname = ruleName + "_R";
  let rule = rules[fullname]

  rule = rule
    .map(f => parser.parse(f))
    .map(f => Sequent.fromTree(f))

  let conclusionConnective = rule[0].succedent;

  let theta = compare(conclusionConnective, pt.conclusion.succedent)

  pt.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    .map(seq => new PT({
      conclusion: seq,
    }))

  pt.type = fullname;
  pt.delta_in = pt.conclusion.antecedent;

}

Proofstate.invertL = function (pt, id) {
  let formula = pt.conclusion.antecedent[id].val.vals[1];
  let name = formula.ruleConstructor;
  let ruleName = name.match(/(Formula_(.*))/)[2];
  let fullname = ruleName + "_L";
  let rule = rules[fullname]

  rule = rule
    .map(f => parser.parse(f))
    .map(f => Sequent.fromTree(f))

  let conclusionConnectiveId = Object.keys(rule[0].antecedent)
    .find(id => {
      let r = rule[0].antecedent[id];
      let isFormula = r.val.ruleConstructor === "Structure_Term_Formula";
      return isFormula && r.val.vals[1].ruleConstructor === name
    })
  let conclusionConnective = rule[0].antecedent[conclusionConnectiveId].val;

  let theta = compare(conclusionConnective, pt.conclusion.antecedent[id].val)

  let theta2 = compare(rule[0].succedent, pt.conclusion.succedent);

  let theta_keys = theta.map(([a, _]) => a.toString());
  let theta2_key = theta2[0][0].toString();

  if(theta2.length > 0 && theta_keys.indexOf(theta2_key) === -1) {
    theta = theta.concat(theta2);
  } else {
    console.log(`todo - compare on equality of substitution, fail otherwise`);
  }

  pt.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    .map(seq => new PT({
      conclusion: seq,
    }))
  // console.log("pt.conclusion", pt.conclusion.toString());

  pt.type = fullname;

  // console.log(theta.map(([k, v]) => `${k} => ${v}`));

  Object.keys(pt.conclusion.antecedent)
  .forEach(id_ => {
    let r = pt.conclusion.antecedent[id_].val;
    let isNotStructure = r.ruleConstructor !== "Structure_Freevar";
    let isNotActive = id_ !== id;
    if(isNotStructure && isNotActive) {
      pt.delta_in[id] = {
        val: r,
        num: pt.conclusion.antecedent[id].num
      }
    }
  })

}

Proofstate.focusR = function (pt) {
  let seq = Sequent.copy(pt.conclusion);

  pt.delta_in = seq.antecedent;
  seq.antecedent = {};
  seq.succedent.doFocus();
  seq.ffocus();

  let ptp = new PT({conclusion: seq});
  pt.premisses = [ptp];
  pt.type = "Focus_R"
}

Proofstate.focusL = function (pt, id) {
  let seq = Sequent.copy(pt.conclusion);
  let antecedent = {};
  let r = seq.antecedent[id]
  let antecedent_ = {[id]: {num:r.num, val: r.val}};
  pt.delta_in = Sequent.remove_from_antecedent(seq, antecedent_);
  seq.antecedent = antecedent_;
  antecedent_[id].val.doFocus();
  seq.ffocus();

  pt.premisses = [new PT({conclusion: seq})];
  pt.type = "Focus_L"
}


Proofstate.blurL = function (pt) {
  // todo - is seq still focused?
  let seq = Sequent.copy(pt.conclusion);
  seq.antecedent[seq.focusId].val.doUnfocus();
  let antecedent = {};
  Object.keys(seq.antecedent).forEach(id => {
    let r = seq.antecedent[id];
    if(id !== seq.focusId)
      antecedent[id] = {num: r.num, val: r.val}
  })
  let antecedent_ = {[seq.focusId]: seq.antecedent[seq.focusId]}
  seq.antecedent = antecedent_;

  pt.delta_in = antecedent;
  pt.premisses = [new PT({conclusion: seq})];
  pt.type = "blur_L";
}

Proofstate.blurR = function (pt) {
  let antecedent = {};
  Object.keys(pt.conclusion.antecedent)
  .forEach(id => {
    let r = pt.conclusion.antecedent[id];
    antecedent[id] = {val: r.val.copy(), num: r.num}
  })
  let succedent = pt.conclusion.succedent.copy();
  succedent.doUnfocus();
  let seq = new Sequent({
    antecedent: {},
    succedent
  })
  pt.delta_in = pt.conclusion.antecedent;
  pt.premisses = [new PT({conclusion: seq})];
  pt.type = "blur_R";
}



// TODO - push this into Sequent?
Proofstate.getAtoms = function (seq) {

  const getAtoms = function (n) {
    if(n.ruleName != "Formula"
      || (n.ruleConstructor !== "Formula_Freevar")
    ) {
      return n.vals
        .map(getAtoms)
        .reduceRight((a,e) => a.concat(e), []);
    } else {
      return [[n.toString(), n]];
    }
  }

  let atoms = Object.keys(seq.antecedent)
    .map(id => seq.antecedent[id].val)
    .map(getAtoms)
    .reduceRight((a,e) => a.concat(e), []);

  let aa = {};
  atoms.forEach(a => aa[a[0]] = true)

  return Object.keys(aa);
}

module.exports = Proofstate;
