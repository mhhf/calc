
const DEBUG = !!process.env["DEBUG"];

const helper = require("./helper.js");
const Calc = require("./calc.js");

const rightPad = (str, max) => {
  let bufferLength = max - str.toString().length;
  if(bufferLength < 0) bufferLength = 0;
  return " ".repeat(bufferLength);
}

// TODO clean this whole class up:
// TODO - rename Node to AST
class Node {
  constructor (id, vals) {
    // this.type = type;
    this.id = id;
    // console.log("set id:"+id);
    this.vals = vals;
  }
  // TODO - rename in to clone
  copy() {
    return new Node(this.id,
      this.vals.map(v => (typeof v === "object") ? v.copy() : v))
  }
  doFocus() {
    if(Calc.db.rules[this.id].ruleName === "Structure_Term_Formula") {
      let formula = this.vals[1];
      if(this.isLax()) formula = this.vals[1].vals[0];
      this.id = Calc.db.toIds["Structure"]["Structure_Focused_Term_Formula"];
      this.vals[1] = new Node(Calc.db.toIds["FFormula"][ "Focused_Formula"], [formula])
    } else {
      console.log("neee");
    }
  }
  doUnfocus() {
    if(Calc.db.rules[this.id].ruleName === "Structure_Focused_Term_Formula") {
      this.id = Calc.db.toIds["Structure"]["Structure_Term_Formula"];
      this.vals[1] = this.vals[1].vals[0];
    } else {
      console.log("neee");
    }
  }
  isAtomic(o) {
    let type = Calc.db.rules[this.id];
    let isVar = type.ruleName === "Formula_Freevar";
    let isAtprop = type.ruleName === "Formula_Atprop";
    let isAtomic = isVar || isAtprop;
    return isAtomic;
  }
  getPolarity(o = {positive: [], negative: []}) {
    let type = Calc.db.rules[this.id];
    if(type.ctxName === "Structure") return "";

    if("polarity" in type) return type.polarity;

    // let isAtomic = this.isAtomic(o);
    let isVar = type.ruleName === "Formula_Freevar";

    let name = isVar
      ? this.toString()
      : this.vals[0].vals[0];

    if(o.positive.indexOf(name) > -1) return "positive";
    if(o.negative.indexOf(name) > -1) return "negative";

    return "";
  }
  isTermType() {
    let type = Calc.db.rules[this.id];
    return type.isTermType;
  }
  isNegative(o) {
    // console.log(`isNegative ${this} ${this.isTermType()}`);
    return this.isTermType() && this.vals[1].getPolarity(o) === "negative"
    || this.getPolarity(o) === "negative"
  }
  isPositive(o) {
    return this.isTermType() && this.vals[1].getPolarity(o) === "positive"
    || this.getPolarity(o) === "positive"
  }
  isLax() {
    let type = Calc.db.rules[this.id];
    let lax = type.ruleName === "Structure_Term_Formula" && Calc.db.rules[this.vals[1].id].ruleName === "Formula_Lax";
    return lax;
  }
  isFocus() {
    let type = Calc.db.rules[this.id];
    return type.ruleName === "Structure_Focused_Term_Formula" && Calc.db.rules[this.vals[1].id].ruleName === "Focused_Formula";
  }
  isMonad() {
    let type = Calc.db.rules[this.id];
    return type.ruleName === "Structure_Term_Formula"
        && Calc.db.rules[this.vals[1].id].ruleName === "Formula_Monad"
  }

  getFreeVariables() {

  }



  // Should brackets be drawn for child i
  // TODO - clean up
  // TODO - brackets depend on style - isabelle should paint them more often
  toString(o) {
    return Node.toString(this, Object.assign({rules: Calc.db.rules}, o));
    // return `(${this.id} ${this.vals.map(v => v.toString()).join(" ")})`;
  }
}

Node.toString = function (node, o) {
  if(typeof node === "string") return node;
  o = Object.assign({
    style: "ascii_se",
    brackets: true,
  }, o);
  let type = o.rules[node.id];
  let tmp = type[o.style] ||
    o.style === "ascii_se" && type["ascii"] ||
    o.style === "isabelle_se" && type["isabelle"] ||
    o.style === "latex_se" && type["latex"] ||
    " _ ";
  // here two cases can occur:
  // 1. number of _ matches the number of values
  // 2. otherwise (I assume there is just one _ !!)
  let i=0;
  let TMP_REGEX = /\s+(_)|(_)\s+|^(_)$/;

  if((tmp.match(/\_/g) || []).length >= node.vals.length) {
    while((tmp.match(TMP_REGEX) || []).length > 0) {
      let b = Node.isBrackets({
        style: o.style,
        i,
        node,
        rules: o.rules
      });
      let isString = type.type === "string" || Array.isArray(type.type) && type.type[i] === "string";
      let isDrawString = o.style === "isabelle_se" && (!("shallow" in type) || type.shallow) && isString;
      let s = isDrawString ? "''" : '';
      tmp = tmp.replace(TMP_REGEX, (b?'( ':' ')+ s + Node.toString(node.vals[i++], o) + s + (b?' )':' '));
    }
  }
  return tmp.replace(/\s+/g, " ").trim();
}

// TODO - simplify brackets
Node.isBrackets = function ({ style, i, node, rules }) {
  let type = rules[node.id];
  let thisPrecedence = type.precedence.slice(-1)[0];
  let child_type = rules[node.vals[i].id]
  let childPrecedence =child_type
    && child_type.precedence
    && child_type.precedence[child_type.precedence.length - 1] || 0;
  let child_has_enougth_children = typeof node.vals[i] === "object" && node.vals[i].vals.length >= 1;
  let latexBrackets = typeof node.vals[i] !== "object" ||
    !("latex_brackets" in child_type) || child_type.latex_brackets;

  let b = child_has_enougth_children
    && node.vals.length > 1
    && thisPrecedence >= childPrecedence
    && latexBrackets
    && i != 1 // ignore right infix operators
    || style === "isabelle_se"
    && (
         typeof node.vals[i] === "object"
      && !!child_type.isabelle_se
      && child_type.isabelle_se != "_"
      || child_has_enougth_children
      && node.vals.length > 1
      && latexBrackets
    )

  return b;
}

Node.formatTree = function ({attrs, node, rules}) {
  let tree = Node.toTree({
    node,
    attrs,
    rules
  })
  const table = helper.foldPreorder(tree, attrs[0])
  return helper.formatDb(table, attrs);
}

Node.toTree = function ({node, rules, attrs}) {
  let ev, evaluate = ev = (v,i) =>
    (typeof v === "string")
      ? {
        head: {
          name: v,
          constr: v
        }
      }
      : Node.toTree({node: v, rules, attrs})

  let formula = ` '${node}'`
  // TODO - remove type alltogether
  let __type = rules[node.id];

  let precedence = (__type.precedence || [0]);
  let constr = (typeof __type.ruleName === "string") ? __type.ruleName : "-";

  let attrTypes = {
    "ascii": (__type.ascii || "").replace(/\_/g,"").trim(),
    "constr": constr,
    "formula": formula,
    "name": __type.ruleName,
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

module.exports = Node;

// module.exports = function grammarNode(calc) {
//   Node.calc = calc;
//   return Node;
// }

