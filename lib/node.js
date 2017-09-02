
const DEBUG = !!process.env["DEBUG"];

const helper = require("./helper.js");


const rightPad = (str, max) => {
  let bufferLength = max - str.toString().length;
  if(bufferLength < 0) bufferLength = 0;
  return " ".repeat(bufferLength);
}

// TODO clean this whole class up:
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
      this.ruleConstructor = "Structure_Focused_Term_Formula"
      this.type = Node.calc.calc_structure[this.ruleName][this.ruleConstructor];
      this.vals[1] = new Node("FFormula", "Focused_Formula", [this.vals[1]])
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
    let isVar = this.ruleConstructor === "Formula_Freevar";
    let isAtprop = this.ruleConstructor === "Formula_Atprop";
    let isAtomic = isVar || isAtprop;

    const polarityMap = Node.calc.calc_structure_rules_meta.polarity;
    let isPositiveVar = (isAtomic && o.positive.indexOf(this.toString()) > -1);
    let isPositiveFormula = (!isAtomic && polarityMap[this.ruleConstructor] === "positive")
    let isPositive = isPositiveVar || isPositiveFormula;
    let isNegativeVar = (isAtomic && o.negative.indexOf(this.toString()) > -1);
    let isNegativeFormula = (!isAtomic && polarityMap[this.ruleConstructor] === "negative")
    let isNegative = isNegativeVar || isNegativeFormula;

    return isPositive ? "positive" : (isNegative ? "negative" : "")
  }






  // TODO - construct dynamic head table
  toTree(attrs = []) {
    let ev, evaluate = ev = (v,i) =>
      (typeof v === "string")
        ? {
          head: {
            name: v,
            constr: v
          }
        }
        : v.toTree(attrs)

    let formula = " '" +this.toString() + "'";

    let precedence = (this.type.precedence || [0]);
    let constr = (typeof this.ruleConstructor === "string") ? this.ruleConstructor : "-";

    let attrTypes = {
      "ascii": (this.type.ascii || "").replace(/\_/g,"").trim(),
      "constr": constr,
      "formula": formula,
      "name": this.ruleConstructor,
      "precedence": precedence.join(', '),
      "ownprecedence": precedence[precedence.length - 1],
      "childprecedence": precedence.slice(0, -1).join(', ')
    };

    let head = {};
    attrs.forEach(attr => {
      head[attr] = attrTypes[attr];
    });

    let children = this.vals.length > 0
      ? this.vals.map(ev)
      : [];

    return {head, children};
  }
  // Should brackets be drawn for child i
  // TODO - clean up
  // TODO - brackets depend on style - isabelle should paint them more often
  isBrackets( style, i ) {
    let thisPrecedence = this.type.precedence[this.type.precedence.length - 1];
    let childPrecedence = this.vals[i].type && this.vals[i].type.precedence && this.vals[i].type.precedence[this.vals[i].type.precedence.length - 1] || 0;
    let child_has_enougth_children = typeof this.vals[i] === "object" && this.vals[i].vals.length >= 1;
    let latexBrackets = typeof this.vals[i] !== "object" ||
      !("latex_brackets" in this.vals[i].type) || this.vals[i].type.latex_brackets;

    let b = child_has_enougth_children
      && this.vals.length > 1
      && thisPrecedence >= childPrecedence
      && latexBrackets
      && i != 1 // ignore right infix operators
      || style === "isabelle_se"
      && (
           typeof this.vals[i] === "object"
        && !!this.vals[i].type.isabelle_se
        && this.vals[i].type.isabelle_se != "_"
        || child_has_enougth_children
        && this.vals.length > 1
        && latexBrackets
      )

    return b;
  }
  toString(o) {
    o = Object.assign({
      style: "ascii",
      brackets: true
    }, o);
    let tmp = this.type[o.style] ||
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
        let b = this.isBrackets(o.style, i);
        let isString = this.type.type === "string" || Array.isArray(this.type.type) && this.type.type[i] === "string";
        let isDrawString = o.style === "isabelle_se" && (!("shallow" in this.type) || this.type.shallow) && isString;
        let s = isDrawString ? "''" : '';
        tmp = tmp.replace(TMP_REGEX, (b?'( ':' ')+ s + this.vals[i++].toString(o) + s + (b?' )':' '));
      }
    }
    return tmp.replace(/\s+/g, " ").trim();
  }
  formatTree(attrs) {
    let tree = this.toTree(attrs)
    const table = helper.foldPreorder(tree, attrs[0])
    return helper.formatDb(table, attrs);
  }
}


module.exports = function grammarNode(calc) {
  Node.calc = calc;
  return Node;
}

