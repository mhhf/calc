const {parser, lexer} = require("../lib/llt_compiler.js");
const fs = require("fs");

const calc = require('../ll.json');


class Ruleset {}

module.exports = Ruleset;

const read = function (path) {
  let o = {filetype: "utf8"};
  return fs
    .readFileSync(path, o)
    .toString()
}

const parse = function (code) {
  return parser.parse(code)
}

const flatten = (a, rs) => a.concat(rs)
const log = e => {console.log(e); return e;}

// TODO - forward chaining rules plz
// TODO - ? model bwd as names: string list ?
Ruleset.init = function (o = {}) {
  // Backward-chaining rules:
  // name => rule list
  let bwd = {};
  // Forward-chaining rules:
  // name => rule list
  let fwd = {};
  // All rules:
  // name => rule list
  let all_rules = {};

  let std_libs = o.std_libs || ["programs/main.llt"]

  let rules = std_libs
    .map(read)
    .map(parse)
    .map(e => e.bwd)
    .reduceRight(flatten, [])


  rules.forEach((r, i) => {
    bwd["custom_"+i] = r;
    all_rules["custom_"+i] = r;
  });

  Object.keys(calc.rules)
    .forEach(ctxName => {
    if(ctxName === "RuleStruct") return null;
    let ctx = calc.rules[ctxName];
    Object.keys(ctx)
      .forEach(ruleName => {
      all_rules[ruleName] = ctx[ruleName];
    })
  })

  return {
    bwd,
    fwd,
    rules: all_rules
  }

}
