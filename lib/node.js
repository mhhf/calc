
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

    let ev, evaluate = ev = (v,i) =>
      (typeof v === "string")
        ? {
          head: {
            location: tp(prefix + (last?"  ":"│ "), il(i)) + v
          }
        }
        : v.toTree(prefix + (last? "  ":"│ "), il(i), attrs)

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

    let head = {};
    attrs.forEach(attr => {
      head[attr] = attrTypes[attr](attr);
    });

    let children = this.vals.length > 0 ? this.vals.map(ev) : [];

    // if(typeof children[0] !== "string") {
    //   children = children
    //   .reduceRight((a,e) => e.concat(a), [])
    // }
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
        let isString = this.type.type === "string";
        let isDrawString = o.style === "isabelle_se" && (!("shallow" in this.type) || this.type.shallow) && isString;
        let s = isDrawString ? "''" : '';
        tmp = tmp.replace(TMP_REGEX, (b?'( ':' ')+ s + this.vals[i++].toString(o) + s + (b?' )':' '));
      }
    }
    return tmp.replace(/\s+/g, " ").trim();
  }
  formatTree(attrs) {
    // TODO - refactor tree to obj data
    let tree = this.toTree("", true, attrs)

    let table = [];
    const preorder = function (tree) {
      table.push(tree.head)
      // TODO - do i need children which are not arrays?
      let childs = Array.isArray(tree.children) ? tree.children : ("children" in tree ? [tree.children] : [])
      childs.forEach(preorder);
    }

    preorder(tree);

    return helper.formatDb(table, attrs);
  }
}

module.exports = function grammarNode(calc) {
  Node.calc = calc;
  return Node;

}

