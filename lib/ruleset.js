const {parser, lexer} = require("../lib/llt_compiler.js");
const Calc = require("./calc.js");
const fs = require("fs");

// const calc = require('../ll.json');
// const Calc = require("./calc.js");
// Calc.init();

const calcParser = require("../lib/parser.js");

const Sequent = require("../lib/sequent.js");


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

  const Parser = calcParser();
  const seq_parser = Parser.parser;
  const calc = Calc.calc;
  // Backward-chaining rules:
  // name => rule list
  let bwd = [];
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
    bwd.push("custom_"+i);
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

  Object.keys(all_rules)
  .forEach(ruleName => {
    let rule = all_rules[ruleName];
    rule = rule
      .filter(f => f !== "")
      .map(f => seq_parser.parse(f))
      .map(f => Sequent.fromTree(f))
      all_rules[ruleName] = rule;
  })

  // TODO - variables get missing by renameUnique which are unique to the premisses - make a rename unique for rule list with first getting all the vars and then substituting them
  const getRule = name => {
    let rule = all_rules[name];
    let unique = Sequent.renameUniqueArray(rule);
    // console.log(`rule: \n${unique.seqs.join("\n")}`);
    return unique.seqs;
  }

  return {
    bwd,
    fwd,
    rules: all_rules,
    getRule
  }

}
