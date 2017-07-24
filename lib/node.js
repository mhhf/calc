
const DEBUG = !!process.env["DEBUG"];

const helper = require("./helper.js");


const rightPad = (str, max) => {
  let bufferLength = max - str.toString().length;
  if(bufferLength < 0) bufferLength = 0;
  return " ".repeat(bufferLength);
}

// TODO clean this whole class up:
//      - generate tree view based on graphviz
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
    let ev, evaluate = ev = (v,i) => (typeof v === "string") ? [[tp(prefix + (last?"  ":"│ "), il(i)) + v]] : v.toTree(prefix + (last? "  ":"│ "), il(i), attrs)

    let formula = " '" +this.toString() + "'";
    let location = tp(prefix, last) + tn;

    let draw = str => o => str  //+ rightPad(str, o.width)

    let precedence = (this.type.precedence || [0]);

    let attrTypes = {
      "location": draw(location),
      "formula": draw(formula),
      "precedence": draw(precedence.join(', ')),
      "ownprecedence": draw(precedence[precedence.length - 1]),
      "childprecedence": draw(precedence.slice(0, -1).join(', '))
    };

    let line = attrs
    .map(attr => attrTypes[attr](attr));

    let children = this.vals.length > 0 ? this.vals.map(ev) : [];

    if(typeof children[0] !== "string") {
      children = children
      .reduceRight((a,e) => e.concat(a), [])
    }
    return ([line]).concat(children);
  }
  // Should brackets be drawn for child i
  // TODO - clean up
  isBrackets( i ) {
    let thisPrecedence = this.type.precedence[this.type.precedence.length - 1];
    let childPrecedence = this.vals[i].type && this.vals[i].type.precedence && this.vals[i].type.precedence[this.vals[i].type.precedence.length - 1] || 0;
    let child_has_enougth_children = typeof this.vals[i] === "object" && this.vals[i].vals.length > 1;
    let latexBrackets = typeof this.vals[i] !== "object" ||
      !("latex_brackets" in this.vals[i].type) || this.vals[i].type.latex_brackets;

    let b = child_has_enougth_children
      && this.vals.length > 1
      && thisPrecedence >= childPrecedence
      && latexBrackets
      && i != 1; // ignore right infix operators
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

    // TODO - clean this up -- i don't need the if case here
    if((tmp.match(/\_/g) || []).length >= this.vals.length) {
      while((tmp.match(/\s+(_)|(_)\s+|^(_)$/) || []).length > 0) {
        let b = this.isBrackets(i);
        tmp = tmp.replace(/\s+(_)|(_)\s+|^(_)$/, (b?'( ':' ') + this.vals[i++].toString(o) + (b?' )':' '));
      }
    } else if((tmp.match(/\_/g) || []).length === 1) {
        tmp = tmp.replace("_", this.vals.map((v, i) => {
        return (this.isBrackets(i)?'( ': '') + v.toString(o) + (this.isBrackets(i)?' )':'');
      }).join(" "));
    }
    return tmp;
  }
  formatTree(attrs) {
    // TODO - refactor tree to obj data
    let tree = this.toTree("", true, attrs)
    console.log(tree);

    // TODO - export parts into helpers - formatDb(db, attrs)

    let treeSizes = tree.reduceRight((a, row) => row.map( (s,i) => Math.max(s && s.toString().length || 0, a[i] || 0) ), []);
    let SPACE = 3;
    let formattedTree = tree
    .map(e => e.map((str, i) => str + rightPad(str, treeSizes[i])).join(" ".repeat(SPACE)))
    .join("\n");
    let title = attrs.map((attr, i) => attr.toUpperCase() + rightPad(attr, treeSizes[i])).join(" ".repeat(SPACE))
    return (`${title}\nRoot\n`+formattedTree);
  }
}

module.exports = function grammarNode(calc) {
  Node.calc = calc;
  return Node;

}

