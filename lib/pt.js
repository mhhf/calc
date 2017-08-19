// TODO - check
// TODO - serialize - latex/ ascii-linear structure/ html
// TODO - premisses are NOT formulas, but proof trees themselves
const calc = require('../ll.json');
const helper = require("../lib/helper.js");
const Sequent = require("../lib/sequent.js");
const katex = require("katex");

class PT {
  constructor(params) {
    this.premisses = params.premisses || [];
    this.conclusion = params.conclusion;
    this.type = params.type || "???";
    this.unusedRessources = [];
    this.potentialRessources = params.potentialRessources || [];
  }

  apply(rule, type) {
    this.type = type;
    let theta = Sequent.compare(rule[0], this.conclusion)
    // console.log(JSON.stringify(theta, false, 2));
    this.premisses = rule.slice(1)
    .map(seq => seq.substitute(theta))
    .map(seq => new PT({conclusion: seq}))

    this.unusedRessources = Object.keys(this.conclusion
    .antecedent)
    .map(id => this.conclusion.antecedent[id].val)
    .filter(r => r !== this.conclusion.focus.val)

  }

  toTree() {
    let conclusion = this.conclusion.toString();
    let type = this.type;

    let head = {
      conclusion,
      type
    };

    let children = this.premisses
      .map(seq => seq.toTree())

    return {
      head,
      children
    }
  }

  toString(o = {}) {
    let html;
    if(o.style === "html") {
      o.style = "latex";
      html = "html"
    }
    var pre, con;
    // let pre = this.premisses
    // .map(f => f.toString(Object.assign(o, {highlight: this.unusedRessources})));
    // let con = this.conclusion
    // .toString(o);

    // TODO - export the actual rendering maybe to another module?
    switch (html || o.style) {
      case "html":
        pre = this.premisses
          .map(f => f.toString(Object.assign(o, {highlight: this.unusedRessources})));
        con = this.conclusion
          .toString(o);
        pre = pre
        .map(f => katex.renderToString(f))
        .map(f => `<span class="formula">${f}</span>`)
        .join("")
        pre = `<span class="premisses">${pre}</span>`;
        con = katex.renderToString(con);
        con = `<span class="formula">${con}</span>`;
        con = `<span class="conclusion">${con}</span>`;
        let rules = `<span class="rules">${pre+con}</span>`
        let name = `<span class="name">${this.type}</span>`;
        return `<span class="inferenceRule">${rules}${name}</span>`;
        break;
      case "latex":
        pre = this.premisses
          .map(f => f.toString(Object.assign(o, {highlight: this.unusedRessources})));
        con = this.conclusion
          .toString(o);
        pre = pre.map(f => `{${f}}`).join("")
        let out = `\\prftree[r]{${this.type}}${pre}{${con}}`;
        console.log(out);
        break;
      default:
        // TODO - return an actual tree structure?
        // pre = pre.join("     ");
        // let line = (pre.length > con.length ? pre : con)
        // .replace(/./g,"-")+"  "+this.type
        // console.log(`${pre}\n${line}\n${con}`);
        // console.log(JSON.stringify(this.toTree(), false, 2));
        let tree = this.toTree()
        let table = helper.foldPreorder(tree, "type")
        console.log(helper.formatDb(table, ["type", "conclusion"]));
    }
  }
}

PT.fromNodeArray = function (array) {
  let conclusion = array[0];
  let premisses = array
    .slice(1)

  return new PT({
    premisses,
    conclusion
  })
}

// PT.fromAsciiArray = function (array) {
//   let conclusion_ascii = array[0];
//   let premisses_ascii = array
//     .slice(1)
//     .filter(e => e !== "")
//
//   let conclusion = parser.parse(conclusion_ascii);
//   let premisses = premisses_ascii
//     .map(f => parser.parse(f))
//   return new PT({
//     premisses,
//     conclusion
//   })
// }

module.exports = PT;
