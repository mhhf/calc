
const DEBUG = !!process.env["DEBUG"];

const helper = require("./helper.js");

const rightPad = (str, max) => {
  let bufferLength = max - str.toString().length;
  if(bufferLength < 0) bufferLength = 0;
  return " ".repeat(bufferLength);
}

// TODO clean this whole class up:
// TODO - rename Node to AST
class Node {
  constructor (ruleName, ruleConstructor, vals) {
    this.ruleName = ruleName;
    this.ruleConstructor = ruleConstructor;
    this.type = Node.calc.calc_structure[ruleName][ruleConstructor];
    this.vals = vals;
  }
  // TODO - rename in to clone
  copy() {
    return new Node(this.ruleName, this.ruleConstructor,
      this.vals.map(v => (typeof v === "object") ? v.copy() : v))
  }
  doFocus() {
    if(this.ruleConstructor === "Structure_Term_Formula") {
      let formula = this.vals[1];
      if(this.isLax()) formula = this.vals[1].vals[0];
      this.ruleConstructor = "Structure_Focused_Term_Formula"
      this.type = Node.calc.calc_structure[this.ruleName][this.ruleConstructor];
      this.vals[1] = new Node("FFormula", "Focused_Formula", [formula])
    } else {
      console.log("neee");
    }
  }
  doUnfocus() {
    if(this.ruleConstructor === "Structure_Focused_Term_Formula") {
      this.ruleConstructor = "Structure_Term_Formula"
      this.type = Node.calc.calc_structure[this.ruleName][this.ruleConstructor];
      this.vals[1] = this.vals[1].vals[0];
    } else {
      console.log("neee");
    }
  }
  getPolarity(o = {positive: [], negative: []}) {
    if(this.ruleName === "Structure") return "";

    let isVar = this.ruleConstructor === "Formula_Freevar";
    let isAtprop = this.ruleConstructor === "Formula_Atprop";
    let isAtomic = isVar || isAtprop;

    let name = isVar ? this.toString() : this.vals[0].vals[0];

    // TODO - think about refactor this
    const polarityMap = o.calc.calc_structure_rules_meta.polarity;
    let isPositiveVar = (isAtomic && o.positive.indexOf(name) > -1);
    let isPositiveFormula = (!isAtomic && polarityMap[this.ruleConstructor] === "positive")
    let isPositive = isPositiveVar || isPositiveFormula;
    let isNegativeVar = (isAtomic && o.negative.indexOf(name) > -1);
    let isNegativeFormula = (!isAtomic && polarityMap[this.ruleConstructor] === "negative")
    let isNegative = isNegativeVar || isNegativeFormula;

    return isPositive ? "positive" : (isNegative ? "negative" : "")
  }
  isTermType() {
    return this.ruleConstructor === "Structure_Term_Formula"
        || this.ruleConstructor === "Structure_Focused_Term_Formula"
  }
  isNegative(o) {
    return this.isTermType() && this.vals[1].getPolarity(o) === "negative"
    || this.getPolarity(o) === "negative"
  }
  isPositive(o) {
    return this.isTermType() && this.vals[1].getPolarity(o) === "positive"
    || this.getPolarity(o) === "positive"
  }
  isLax() {
    let lax = this.ruleConstructor === "Structure_Term_Formula" && this.vals[1].ruleConstructor === "Formula_Lax";
    return lax;
  }
  isFocus() {
    return this.ruleConstructor === "Structure_Focused_Term_Formula" && this.vals[1].ruleConstructor === "Focused_Formula";
  }
  isMonad() {
    return this.ruleConstructor === "Structure_Term_Formula"
        && this.vals[1].ruleConstructor === "Formula_Monad"
  }

  getFreeVariables() {

  }

  // TODO - isClosed - contain no free variables






  // TODO - construct dynamic head table
  // toTree(attrs = []) {
  //   let ev, evaluate = ev = (v,i) =>
  //     (typeof v === "string")
  //       ? {
  //         head: {
  //           name: v,
  //           constr: v
  //         }
  //       }
  //       : v.toTree(attrs)
  //
  //   let formula = " '" +this.toString() + "'";
  //
  //   let precedence = (this.type.precedence || [0]);
  //   let constr = (typeof this.ruleConstructor === "string") ? this.ruleConstructor : "-";
  //
  //   let attrTypes = {
  //     "ascii": (this.type.ascii || "").replace(/\_/g,"").trim(),
  //     "constr": constr,
  //     "formula": formula,
  //     "name": this.ruleConstructor,
  //     "precedence": precedence.join(', '),
  //     "ownprecedence": precedence[precedence.length - 1],
  //     "childprecedence": precedence.slice(0, -1).join(', ')
  //   };
  //
  //   let head = {};
  //   attrs.forEach(attr => {
  //     head[attr] = attrTypes[attr];
  //   });
  //
  //   let children = this.vals.length > 0
  //     ? this.vals.map(ev)
  //     : [];
  //
  //   return {head, children};
  // }

  // Should brackets be drawn for child i
  // TODO - clean up
  // TODO - brackets depend on style - isabelle should paint them more often
  toString(o) {
    o = Object.assign({
      style: "ascii_se",
      brackets: true
    }, o);
    let tmp = this.type[o.style] ||
      o.style === "ascii_se" && this.type["ascii"] ||
      o.style === "isabelle_se" && this.type["isabelle"] ||
      o.style === "latex_se" && this.type["latex"] ||
      " _ ";
    // if(DEBUG)
    //   console.log(`STRINGIFY ${this.ruleName}`);
    // here two cases can occur:
    // 1. number of _ matches the number of values
    // 2. otherwise (I assume there is just one _ !!)
    let i=0;
    let TMP_REGEX = /\s+(_)|(_)\s+|^(_)$/;

    if((tmp.match(/\_/g) || []).length >= this.vals.length) {
      while((tmp.match(TMP_REGEX) || []).length > 0) {
        let b = Node.isBrackets({
          style: o.style,
          i,
          node: this
        });
        let isString = this.type.type === "string" || Array.isArray(this.type.type) && this.type.type[i] === "string";
        let isDrawString = o.style === "isabelle_se" && (!("shallow" in this.type) || this.type.shallow) && isString;
        let s = isDrawString ? "''" : '';
        tmp = tmp.replace(TMP_REGEX, (b?'( ':' ')+ s + this.vals[i++].toString(o) + s + (b?' )':' '));
      }
    }
    return tmp.replace(/\s+/g, " ").trim();
  }
  // formatTree({attrs, node, calc}) {
  //   let tree = Node.toTree({
  //     node,
  //     calc,
  //     attrs
  //   })
  //   const table = helper.foldPreorder(tree, attrs[0])
  //   return helper.formatDb(table, attrs);
  // }
}

// TODO - simplify brackets
Node.isBrackets = function ({ style, i, node }) {
  let thisPrecedence = node.type.precedence[node.type.precedence.length - 1];
  let childPrecedence = node.vals[i].type && node.vals[i].type.precedence && node.vals[i].type.precedence[node.vals[i].type.precedence.length - 1] || 0;
  let child_has_enougth_children = typeof node.vals[i] === "object" && node.vals[i].vals.length >= 1;
  let latexBrackets = typeof node.vals[i] !== "object" ||
    !("latex_brackets" in node.vals[i].type) || node.vals[i].type.latex_brackets;

  let b = child_has_enougth_children
    && node.vals.length > 1
    && thisPrecedence >= childPrecedence
    && latexBrackets
    && i != 1 // ignore right infix operators
    || style === "isabelle_se"
    && (
         typeof node.vals[i] === "object"
      && !!node.vals[i].type.isabelle_se
      && node.vals[i].type.isabelle_se != "_"
      || child_has_enougth_children
      && node.vals.length > 1
      && latexBrackets
    )

  return b;
}

Node.formatTree = function ({attrs, node, calc}) {
  let tree = Node.toTree({
    node,
    calc,
    attrs
  })
  const table = helper.foldPreorder(tree, attrs[0])
  return helper.formatDb(table, attrs);
}

Node.toTree = function ({node, calc, attrs}) {
  let ev, evaluate = ev = (v,i) =>
    (typeof v === "string")
      ? {
        head: {
          name: v,
          constr: v
        }
      }
      : Node.toTree({node: v, calc, attrs})

  let formula = ` '${node}'`
  // TODO - remove type alltogether
  let __type = calc.calc_structure[node.ruleName][node.ruleConstructor];

  let precedence = (__type.precedence || [0]);
  let constr = (typeof node.ruleConstructor === "string") ? node.ruleConstructor : "-";

  let attrTypes = {
    "ascii": (__type.ascii || "").replace(/\_/g,"").trim(),
    "constr": constr,
    "formula": formula,
    "name": node.ruleConstructor,
    "precedence": precedence.join(', '),
    "ownprecedence": precedence[precedence.length - 1],
    "childprecedence": precedence.slice(0, -1).join(', ')
  };

  let head = {};
  attrs.forEach(attr => {
    head[attr] = attrTypes[attr];
  });

  let children = node.vals.length > 0
    ? node.vals.map(ev)
    : [];

  return {head, children};
}


module.exports = function grammarNode(calc) {
  Node.calc = calc;
  return Node;
}

