
const DEBUG = !!process.env["DEBUG"];

// TODO - do i even need this?
const rightPad = (str, max) => {
  let bufferLength = max - str.toString().length;
  if(bufferLength < 0) bufferLength = 0;
  return " ".repeat(bufferLength);
}

class Node {
  constructor (ruleName, ruleConstructor, vals) {
    this.ruleName = ruleName;
    this.ruleConstructor = ruleConstructor;
    this.type = Node.calc.calc_structure[ruleName][ruleConstructor];
    this.vals = vals;
  }
  // TODO - construct dynamic head table
  toTree(prefix = "", last = false, attrs = []) {
    let tp, tree_prefix = tp =
      (prefix, last = false) =>
        prefix + (last ? "└ ": "├ ");
    let tn, tree_name = tn = this.ruleConstructor;
    let il, is_last = il = i => this.vals.length - 1 === i;
    let ev, evaluate = ev = (v,i) => (typeof v === "string") ? tp(prefix + (last?"  ":"│ "), il(i)) + v : v.toTree(prefix + (last? "  ":"│ "), il(i), attrs)

    let formula = " '" +this.toString() + "'";
    let location = tp(prefix, last) + tn;

    let draw = str => o => str + rightPad(str, o.width)

    let precedence = (this.type.precedence || [0]);

    let attrTypes = {
      "location": draw(location),
      "formula": draw(formula),
      "precedence": draw(precedence.join(', ')),
      "ownprecedence": draw(precedence[precedence.length - 1]),
      "childprecedence": draw(precedence.slice(0, -1).join(', '))
    };

    let line = attrs
    .map(attr => attrTypes[attr.type](attr))
    .join("");

    // Format
    let children = this.vals.length > 0 ? "\n" + this.vals.map(ev).join("\n") : "";

    return `${line}${children}`;
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
    // here two cases can occur:
    // 1. number of _ matches the number of values
    // 2. otherwise (I assume there is just one _ !!)
    let i=0;

    // TODO - lol, clean this scarry shit up
    const isBrackets = i => {
      let thisPrecedence = this.type.precedence[this.type.precedence.length - 1];
      let childPrecedence = this.vals[i].type && this.vals[i].type.precedence && this.vals[i].type.precedence[this.vals[i].type.precedence.length - 1] || 0;
      let child_has_enougth_children = typeof this.vals[i] === "object" && this.vals[i].vals.length > 1;
      let latexBrackets = typeof this.vals[i] !== "object" ||
        !("latex_brackets" in this.vals[i].type) || this.vals[i].type.latex_brackets;
      let b = child_has_enougth_children && this.vals.length > 1 && thisPrecedence >= childPrecedence && latexBrackets;
      return b;
    }

    // TODO - clean this up -- i don't need the if case here
    if((tmp.match(/\_/g) || []).length >= this.vals.length) {
      while((tmp.match(/\s+(_)|(_)\s+|^(_)$/) || []).length > 0) {
        let b = isBrackets(i);
        tmp = tmp.replace(/\s+(_)|(_)\s+|^(_)$/, (b?'( ':' ') + this.vals[i++].toString(o) + (b?' )':' '));
      }
    } else if((tmp.match(/\_/g) || []).length === 1) {
        tmp = tmp.replace("_", this.vals.map((v, i) => {
        return (isBrackets(i)?'( ': '') + v.toString(o) + (isBrackets(i)?' )':'');
      }).join(" "));
    }
    return tmp;
  }
}


module.exports = function grammarNode(calc) {
  Node.calc = calc;
  return Node;

}

