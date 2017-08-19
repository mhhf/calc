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
    .premisses)
    .map(id => this.conclusion.premisses[id].val)
    .filter(r => r !== this.conclusion.focus.val)

  }

  toTree() {

  }

  toString(o = {}) {
    let html;
    if(o.style === "html") {
      o.style = "latex";
      html = "html"
    }
    let pre = this.premisses
    .map(f => f.toString(Object.assign(o, {highlight: this.unusedRessources})));
    let con = this.conclusion
    .toString(o);

    // TODO - export the actual rendering maybe to another module?
    switch (html || o.style) {
      case "html":
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
        pre = pre.map(f => `{${f}}`).join("")
        let out = `\\prftree[r]{${this.type}}${pre}{${con}}`;
        console.log(out);
        break;
      default:
        // TODO - return an actual tree structure?
        pre = pre.join("     ");
        let line = (pre.length > con.length ? pre : con)
        .replace(/./g,"-")+"  "+this.type
        console.log(`${pre}\n${line}\n${con}`);
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
