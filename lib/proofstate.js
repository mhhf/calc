// TODO - maybe subsitude potential imediatelly into the antecedent and remove it on back propagation
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

class Proofstate {

  constructor(seq) {
    this.pt = new PT({
      conclusion: seq
    })
    this.active = [this.pt]; // active pointers to ??? pt state
    this.passive = [];
    this.negative = Proofstate.getAtoms(this.pt.conclusion);
    this.positive = []; //Proofstate.getAtoms(this.pt.conclusion);
    // TODO - get all variables and formulas and assign polarity to them.
  }

  auto(pt, o = {}) {

    const resPolarity = (r) => {
      let isVar = r.ruleConstructor === "Formula_Freevar";
      const polarityMap = calc.calc_structure_rules_meta.polarity;
      let isPositiveVar = (isVar && this.positive.indexOf(r.toString()) > -1);
      let isPositiveFormula = (!isVar && polarityMap[r.ruleConstructor] === "positive")
      let isPositive = isPositiveVar || isPositiveFormula;
      let isNegativeVar = (isVar && this.negative.indexOf(r.toString()) > -1);
      let isNegativeFormula = (!isVar && polarityMap[r.ruleConstructor] === "negative")
      let isNegative = isNegativeVar || isNegativeFormula;

      return isPositive ? "positive" : (isNegative ? "negative" : "")
    }

    if(pt.type === "???" && pt.conclusion.focus) {
      let formula = pt.conclusion.focus.vals[1].vals[0];
      let name = formula.ruleConstructor;
      let pos = pt.conclusion.focusPosition;
      if(name !== "Formula_Freevar") {
        let ruleName = name.match(/(Formula_(.*))/)[2];
        let fullname = ruleName + "_" + pos;
        let ruleNode = rules[fullname]
          .map(f => parser.parse(f))
          .map(f => Sequent.fromTree(f))
        // TODO immutable pt
        console.log(`todo - immutable pt`);
        Proofstate.apply(pt, ruleNode, fullname)
        pt.premisses.forEach(ptp => {
          this.auto(ptp, o);
        })
      } else { // Freevar in focus
        let isRight = pos === "R";
        let isLeft = pos === "L";
        let isNegative = this.negative
          .indexOf(formula.toString()) > -1;
        let isPositive = this.positive
          .indexOf(formula.toString()) > -1;

        let out = {};
        // TODO - populate and handle __out__;
        if(isLeft && isNegative) {
          out = Proofstate.tryIdNeg(pt);
        } else if(isLeft && isPositive) {
          out = Proofstate.blurL(pt);
        } else if(isRight && isNegative) {
          out = Proofstate.blurR(pt);
          pt.premisses.forEach(ptp => {
            this.auto(ptp, o);
          })
        } else if(isRight && isPositive) {
          console.log(`todo: Id_Pos`);
          // this.passive.push(pt);
        }
        if(out) {
          console.log(`todo - propagate out - remove out from potential`);
          let pot = pt.conclusion.potentialRessources;
          let pot_ = {};
          Object.keys(pot)
          .forEach(id => {
            let r = pot[id];
            if(id in out && r.num > out.num) {
              pot_[id] = {val: r.val, num: r.num - out.num}
            } else if(!(id in out)) {
              pot_[id] = r;
            }
          })
          pt.conclusion.potentialRessources = pot_;
        }
      }
    } else if(pt.type === "???") { // nothing in focus
      let seq = pt.conclusion;
      let suc = seq.succedent.vals[1];
      let isVar = suc.ruleConstructor === "Formula_Freevar";
      let polarityMap = calc.calc_structure_rules_meta.polarity;
      if(resPolarity(suc) === "positive") {
        Proofstate.focusR(pt);
      } else {
        let filterReal = Object.keys(seq.antecedent)
          .map(id => seq.antecedent[id].val)
          .filter(node => node.ruleConstructor !== "Structure_Freevar")
          .filter(r => resPolarity(r.vals[1]) === "negative")

        let filterPot = Object.keys(seq.potentialRessources)
          .map(id => seq.potentialRessources[id].val)
          .filter(r => resPolarity(r.vals[1]) === "negative")

        let filter = filterReal.concat(filterPot);
        console.log(`TODO - focus antecedent ${filter}`);
        if(filter.length > 0) {
          Proofstate.focusL(pt, filter[0])
          // this.active = this.active.concat(pt.premisses);
          pt.premisses.forEach(ptp => {
            this.auto(ptp, o);
          })
        }
        // TODO - fork
      }
      // this.passive.push(pt);
    } else {
      // TODO dunno what to do here, type is not ???, maybe propagate
      console.log(`todo - dunno what to do here, type is not ???, maybe propagate`);
    }
    return pt;
  }


  toString() {
    return this.pt.toString();
  }

}
Proofstate.apply = function(pt, rule, type) {
  pt.type = type;
  // console.log(`comparing \n${rule[0].toString()}\n${pt.conclusion.toString()}`);
  let theta = Sequent.compare(rule[0], pt.conclusion)

  pt.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    // TODO - why does this not work?
    // .map(seq => {
    //   let pot = pt.conclusion.potentialRessources;
    //   Object.keys(pot)
    //   .forEach(id => {
    //     let r = pot[id];
    //     seq.potentialRessources[id] = {num: r.num, val: r.val}
    //   })
    //   return seq;
    // })
    .map(seq => new PT({
      conclusion: seq,
    }))


  pt.unusedRessources = {};
  let pot = pt.conclusion.potentialRessources;
  Object.keys(pot)
  .forEach(id => {
    let r = pot[id];
    pt.unusedRessources[id] = {num: r.num, val: r.val}
  })
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

  pt.premisses.forEach(p => {
    p.conclusion.potentialRessources = pt.unusedRessources;
  })
}

// TODO - extend to different quantities on the succedent
Proofstate.tryIdNeg = function (pt) {
  let formula = pt.conclusion.focus.vals[1].vals[0];
  let isId = formula.toString() === pt.conclusion.succedent.vals[1].toString();
  let return_ = {};
  if(isId) {
    // clear structural variables, check if premisse is empty
    let antecedent_ = {};
    let isError = false;
    Object.keys(pt.conclusion.antecedent)
      // .map(id => pt.conclusion.antecedent[id].val)
      .forEach(id => {
        let r = pt.conclusion.antecedent[id].val;
        if(r.ruleConstructor === "Structure_Freevar") {
          // to nothing - ignore potential structures
        } else if(r === pt.conclusion.focus) {
          let quantity = pt.conclusion.antecedent[id].num;
          if(quantity !== 1) {
            return_[id] = {num: quantity - 1, val: r}
          } else {
            antecedent_[id] = {num: 1, val: r};
          }
        } else {
          return_[id] = {num: quantity - 1, val: r}
        }
      })
    // TODO - if no error
    // TODO - return
    pt.conclusion.antecedent = antecedent_;
    pt.type = "Id_Neg"
    let pot = pt.conclusion.potentialRessources
    Object.keys(pot)
    .forEach(id => {
      let r = pot[id];
      if(id in return_) {
        return_[id].num += r.num;
      } else {
        return_[id] = {num: r.num, val: r.val}
      }
    })
  } else {
    return_ = false;
    console.log(`nop: ${formula.toString()}  -- ${pt.conclusion.succedent.vals[1].toString()}`);
  }
  return return_;
}

Proofstate.focusL = function (pt, value) {
  let pot = pt.conclusion.potentialRessources

  let id = Object.keys(pot)
  .find(id => pot[id].val === value)

  if(id) {
    pt.conclusion.antecedent[id] = {val: value, num: 1};
    // TODO - remove one id from pot
    console.log(`todo - remove one id from pot after putting it in antecedent`);
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
