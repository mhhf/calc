// TODO - maybe subsitude potential imediatelly into the antecedent and remove it on back propagation
const clc = require('cli-color');

const Node = require("./node.js");
const PT = require("./pt.js");
const calc = require('../ll.json');
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

Proofstate.resPolarity = function (r, o) {
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

Proofstate.auto = function(pt, o) {
  o = Object.assign({
    negative: [],
    positive: []
  }, o)

  let out = {};

  let isUnsolved = pt.type === "???"
  let isFocused = pt.conclusion.focus;

  if(isUnsolved && isFocused) {
    let formula = pt.conclusion.focus.vals[1].vals[0];
    let name = formula.ruleConstructor;
    let pos = pt.conclusion.focusPosition;
    let isComplex = name !== "Formula_Freevar";

    if(isComplex) {
      let ruleName = name.match(/(Formula_(.*))/)[2];
      let fullname = ruleName + "_" + pos;
      let ruleNode = rules[fullname]
        .map(f => parser.parse(f))
        .map(f => Sequent.fromTree(f))

      Proofstate.apply(pt, ruleNode, fullname)
    } else { // Freevar in focus
      let isRight = pos === "R";
      let isLeft = pos === "L";
      let isNegative = o.negative
        .indexOf(formula.toString()) > -1;
      let isPositive = o.positive
        .indexOf(formula.toString()) > -1;

      // TODO - populate and handle __out__;
      if(isLeft && isNegative) {
        out = Proofstate.tryIdNeg(pt);
        pt.unusedRessources = out;
      } else if(isLeft && isPositive) {
        Proofstate.blurL(pt);
      } else if(isRight && isNegative) {
        Proofstate.blurR(pt);
      } else if(isRight && isPositive) {
        console.log(`todo: Id_Pos`);
      }
    }
    let delta = pt.unusedRessources;
    pt.premisses
      .reverse()
      .forEach(ptp => {
      Sequent.add_to_antecedent(ptp.conclusion, delta);
      Sequent.remove_structural_variables(ptp.conclusion);
      let delta_ = Proofstate.auto(ptp, o);
      if(!delta_) {
        console.log(clc.red(`ERROR: no delta out received, therefore couldn't proove sequent: ${ptp.conclusion}`));
      }
      delta = delta_ || {};
    })
    out = delta;
  } else if(isUnsolved) { // nothing in focus
    let seq = pt.conclusion;
    let suc = seq.succedent.vals[1];
    let isVar = suc.ruleConstructor === "Formula_Freevar";
    let polarityMap = calc.calc_structure_rules_meta.polarity;
    if(Proofstate.resPolarity(suc, o) === "positive") {
      Proofstate.focusR(pt);
      pt.premisses.forEach(ptp => {
        Proofstate.auto(ptp, o);
      })
    } else {
      let filter = Object.keys(seq.antecedent)
        .map(id => seq.antecedent[id].val)
        .filter(node => node.ruleConstructor !== "Structure_Freevar")
        .filter(r => Proofstate.resPolarity(r.vals[1], o) === "negative")

      // TODO fork antecedent focus ${filter}
      console.log(`todo - fork antecedent focus ${filter}`);
      if(filter.length > 0) {
        Proofstate.focusL(pt, filter[0])
      }
      pt.premisses.forEach(ptp => {
        Proofstate.auto(ptp, o);
      });
      // TODO - fork
    }
  } else {
    // TODO dunno what to do here, type is not ???, maybe propagate
    console.log(`todo - dunno what to do here, type is not ???, maybe propagate`);
  }
  return out;
}


Proofstate.apply = function(pt, rule, type) {
  pt.type = type;
  let theta = Sequent.compare(rule[0], pt.conclusion)

  pt.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    .map(seq => new PT({
      conclusion: seq,
    }))

  pt.unusedRessources = {};
  // let pot = pt.conclusion.potentialRessources;
  // Object.keys(pot)
  // .forEach(id => {
  //   let r = pot[id];
  //   pt.unusedRessources[id] = {num: r.num, val: r.val}
  // })
  let antecedent = pt.conclusion.antecedent;

  Object.keys(antecedent)
  .forEach(id => {
    let r = antecedent[id].val;
    let isNotStructure = r.ruleConstructor !== "Structure_Freevar";
    let isNotInFocus =  pt.conclusion.focus && r !== pt.conclusion.focus
    if(isNotStructure && isNotInFocus) {
      pt.unusedRessources[id] = {
        val: r,
        num: antecedent[id].num
      }
    }
  })

  // pt.premisses.forEach(p => {
  //   p.conclusion.potentialRessources = pt.unusedRessources;
  // })
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
    // Object.keys()
    //   // .map(id => pt.conclusion.antecedent[id].val)
    //   .forEach(id => {
    //     let r = pt.conclusion.antecedent[id].val;
    //     let quantity = pt.conclusion.antecedent[id].num;
    //     if(r.ruleConstructor === "Structure_Freevar") {
    //       // to nothing - ignore potential structures
    //     } else if(r === pt.conclusion.focus) {
    //       if(quantity !== 1) {
    //         return_[id] = {num: quantity - 1, val: r}
    //       } else {
    //         antecedent_[id] = {num: 1, val: r};
    //       }
    //     } else {
    //       return_[id] = {num: quantity - 1, val: r}
    //     }
    //   })
    // // TODO - if no error
    // // TODO - return
    // pt.conclusion.antecedent = antecedent_;
    pt.type = "Id_Neg"
    // let pot = pt.conclusion.potentialRessources
    // Object.keys(pot)
    // .forEach(id => {
    //   let r = pot[id];
    //   if(id in return_) {
    //     return_[id].num += r.num;
    //   } else {
    //     return_[id] = {num: r.num, val: r.val}
    //   }
    // })
  } else {
    return_ = false;
    console.log(`nop: ${formula.toString()}  -- ${pt.conclusion.succedent.vals[1].toString()}`);
  }
  return return_;
}

Proofstate.focusL = function (pt, value) {
  // let pot = pt.conclusion.potentialRessources

  let id = Object.keys(pt.conclusion.antecedent)
  .find(id => pt.conclusion.antecedent[id].val === value)

  if(id) {
    pt.conclusion.antecedent[id] = {val: value, num: 1};
    console.log(`todo - make sure context is empty`);
    let rule = [
    "?X, * :   F? A   |- * : F? C",
    "?X, * : [ F? A ] |- * : F? C"
    ];
    rule = rule
      .map(f => parser.parse(f))
      .map(f => Sequent.fromTree(f))
    Proofstate.apply(pt, rule, "focus_L");
  }
}

Proofstate.focusR = function (pt) {
  let rule = [
  "?X |- * :   F? C  ",
  "?X |- * : [ F? C ]"
  ];
  rule = rule
    .map(f => parser.parse(f))
    .map(f => Sequent.fromTree(f))
  Proofstate.apply(pt, rule, "focus_R");
}

Proofstate.blurL = function (pt) {
  let rule = [
  "?X, * : [ F? A ] |- * : F? C",
  "?X, * :   F? A   |- * : F? C"];
  rule = rule
    .map(f => parser.parse(f))
    .map(f => Sequent.fromTree(f))
  Proofstate.apply(pt, rule, "blur_L");
}

Proofstate.blurR = function (pt) {
  let rule = [
  "?X |- * : [ F? C ]",
  "?X |- * :   F? C  "];
  rule = rule
    .map(f => parser.parse(f))
    .map(f => Sequent.fromTree(f))
  Proofstate.apply(pt, rule, "blur_R");
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
