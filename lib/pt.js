// TODO - check
// TODO - serialize - latex/ ascii-linear structure/ html
// TODO - premisses are NOT formulas, but proof trees themselves
const calc = require('../ll.json');
const helper = require("../lib/helper.js");
const Sequent = require("../lib/sequent.js");
const katex = require("katex");

const calcParser = require("../lib/parser.js");
const Parser = calcParser(calc);
const parser = Parser.parser;

class PT {
  constructor(params) {
    this.premisses = params.premisses || [];
    this.conclusion = params.conclusion;
    this.type = params.type || "???";
    this.delta_in = {};
    this.delta_out = {};
    this.proven = false;
  }

  toTree() {
    let conclusion = this.conclusion.toString();
    let type = this.type;

    // let ptR = this.conclusion.potentialRessources;
    // let pot = //potentialRessources;
    //   Object.keys(ptR)
    //   .map(id => ptR[id].val)
    //   .map(r => r.toString())
    //   .join("; ")

    let delta_in = Object.keys(this.delta_in)
      .map(id => this.delta_in[id].val)
      .map(r => r.toString())
      .join("; ")

    let delta_out = Object.keys(this.delta_out)
    .map(id => this.delta_out[id].val.toString())
    .join(", ")

    let proven = this.proven ? "x" : "-";

    let head = {
      conclusion,
      type,
      delta_out,
      // pot,
      delta_in,
      proven
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
    // .map(f => f.toString(Object.assign(o, {highlight: this.delta_in})));
    // let con = this.conclusion
    // .toString(o);

    // TODO - export the actual rendering maybe to another module?
    switch (html || o.style) {
      case "html":
        pre = this.premisses
          .map(f => f.toString(Object.assign(o, {
            highlight: Object.keys(this.delta_in),
            style: html || o.style
          })));
        con = this.conclusion
          .toString(o);
      // console.log(pre);
        pre = pre
        // .map(f => katex.renderToString(f))
        .map(f => `<span class="formula">${f}</span>`)
        .join("")
        pre = `<span class="premisses">${pre}</span>`;
        con = katex.renderToString(con);
        con = `<span class="formula">${con}</span>`;
        con = `<span class="conclusion">${con}</span>`;
        let rules = `<span class="rules">${pre+con}</span>`
        let name = `<span class="name">${katex.renderToString(this.type)}</span>`;
        return `<span class="inferenceRule">${rules}${name}</span>`;
        break;
      case "latex":
        pre = this.premisses
          .map(f => f.toString(o));
        con = this.conclusion.toString(o);
        pre = pre.map(f => `{${f}}`).join("")
        let out = `\\prftree[r]{$${this.type}$}${pre}{${con}}`;
        return out;
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
        return helper.formatDb(table, ["type", "proven", "conclusion"]); // , "delta_in", "delta_out"
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
