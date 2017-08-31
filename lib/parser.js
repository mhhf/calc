// TODO - remove latex_brakcets variable since this can be inferred from the context
//
//
// TODO - get precedence right - generate overview in doc with characteristic symbols and stuff

var Jison = require("jison");
var Parser = Jison.Parser;

var clc = require('cli-color');

var calcNode = require("./node.js");
const DEBUG = !!process.env["DEBUG"];

const FORMAT_PORPS = [
  "isabelle",
  "isabelle_se",
  "ascii",
  "latex",
  "latex_se"
];

var grammar = {
    "lex": {
        "rules": [
           ["\\s+",                    "/* skip whitespace */"],
           ["\\(",                     "return '('"],
           ["\\)",                     "return ')'"]
        ]
    },
    "bnf": {
      "Start": [["Sequent EOF", "return $1;"]]
    },
    "start": "Start",
    // TODO - add connectives automatically

    "operators": [
        ["right", ","],
        ["right", "-o"],
        ["right", "xx"],
        ["right", "&&"],
        ["right", "."],
    ],

};


let symbols = {};
let numSymbols = 0;

let NT = {};

function constructParsingRule (k, rules, rule, brackets = false) {
  let type = rules[rule];
  let syntax = rules[rule].ascii || "";
  let types = Array.isArray(rules[rule].type) ? rules[rule].type : (rules[rule].type ? [rules[rule].type] : [] );
  let terms = syntax.split("_")
  let precedence = rules[rule].precedence;
  var newterms = "";
  var newexp = "";
  let selfReferential = (types.indexOf(k) > -1);

  types.forEach(t => {
    NT[t] = true;
  });

  // Add found symbols to symbol list to pars them
  terms = terms
    .map(t => {
      if(t !== "") {
        t = t.trim();
        if(!t.match(/^\s*$/))
          symbols[t] = t;
        return t;
      } else {
        return "";
      }
    }).join(" _ ");

  if (terms === "") {
    newterms = " "+types.join(" ")+" "
  } else {
    let i = 0;
    newterms = terms;
    while(newterms.indexOf("_") > -1) {
      newterms = newterms.replace(/\_/, types[i++])
    }
  }

  // TODO - fix this criteria, term is hacky
  let bracketCondition = selfReferential && k !== "Term" ;

  if(brackets && bracketCondition) {
    newterms = "(" + newterms + ")";
  } else if(brackets && !bracketCondition) {
    return null;
  }

  newexp = newterms
  .split(/\s+/)
  .filter(s => s !== "")
  .map((s,i) => (NT[s] ? ("$"+(i+1)) : ""))
  .filter(s => s !== "").join(', ');

  let reducable = types.length === 0;

  // console.log("\n\n");
  // console.log("Kontext", k);
  // console.log("Rule:", rule);
  // console.log("syntax", syntax);
  // console.log("types", types);
  // console.log("terms", terms);
  // console.log("precedence", precedence);
  // console.log("newterms:", newterms);
  // console.log("newexp:", newexp);
  // console.log("---");
  // console.log("reducable", (reducable) ? clc.green("YAY".repeat(4)): "");
  // console.log("kinr", (types.indexOf(k) > -1) ? clc.green("YAY"): "");

  return [newterms, `$$ = new yy.Node("${k}", "${rule}", [${newexp}]);`];
}

function constructDepOrder(calc) {
  let depGraph = {};
  let keys = Object.keys(calc)
    .forEach(ctxName => {
    let ctx = calc[ctxName];
    let deps = {};
      Object.keys(ctx)
      .forEach(ruleName => {
      let rule = ctx[ruleName];
      if("type" in rule) (Array.isArray(rule.type) ? rule.type : [])
          .forEach(t => deps[t] = true)
    })
    depGraph[ctxName] = Object.keys(deps);
  });
  let depGraphStr = JSON.stringify(depGraph, false, 2);
  let depOrder = [];
  let got = true;
  let rmKey = key => Object.keys(depGraph)
    .forEach(k => {
      let i = depGraph[k].indexOf(key);
      if(i > -1) {
        depGraph[k].splice(i, 1);
      }
    })
  // rm mutual
  Object.keys(depGraph)
  .forEach(key => {
    let i = depGraph[key].indexOf(key);
    if(i > -1) {
      depGraph[key].splice(i, 1)
    }
  })
  rmKey("string");
  while (got) {
    got = false;
    let rmEl = Object.keys(depGraph)
    .find(e => depGraph[e].length == 0)
    if(rmEl) {
      got = true;
      depOrder.push(rmEl);
      delete depGraph[rmEl];
      rmKey(rmEl);
    }
  }
  return depOrder;
}

function genParser(calc) {
  // TODO - reduce reducable rules:
  //
  // CLEANING CALC
  // 1.       go over each context and find context(CC) with only reducable rules (RR)
  // 2.       go over each context (NC) and each constructor (NR)
  // 2.1      reducable context (CC) appears in (RR).types
  // 2.1.1    remove (NR) from (NC)
  // 2.1.2    for each constructor (RR) in (CC)
  // 2.1.2.1  add a new Rule (NN) to (NC) with following props:
  //        - defaults are is (NR)
  //        - remove (CC) from (NR).types
  //        - propagate (RR) specifics (to display types)
  // 2.2 reducable rule NOT appears in types

  var calc_ = {};

  let calc_structure = constructDepOrder(calc.calc_structure);

  // TODO - assumption: one rule can only have ONE reducable context
  // 1.
  let reducable_ctxs = [];
  calc_structure
  .forEach(ctxName => {
    let ctx = calc.calc_structure[ctxName];
    let has_only_reducable_rules = Object.keys(ctx)
    .map(ruleName => (ctx[ruleName].type || []).length === 0)
    .reduceRight((a, t) => a && t, true);
    if(has_only_reducable_rules) {
      // if(DEBUG) console.log(clc.green(`CONTEXT ${ctxName} IS REDUCABLE`));
      reducable_ctxs.push(ctxName);
    }
  })
  // 2.
  calc_structure
  .forEach(ctxName => {
    if(reducable_ctxs.indexOf(ctxName) > -1) return null;
    let ctx = calc.calc_structure[ctxName];
    let ctx_ = {};
    Object.keys(ctx).forEach(ruleName => {
      let rule = ctx[ruleName];
      let types = Array.isArray(rule.type)
        ? rule.type
        : (rule.type
          ? [rule.type]
          : [])
      let reducable_ctx = reducable_ctxs
        .map(reducable_ctx_name => types.indexOf(reducable_ctx_name) > -1 ? reducable_ctx_name : false)
        .reduceRight((a, t) => a || t, false);

      // 2.1
      if(reducable_ctx) {
        // if(DEBUG)
        //   console.log(`RULE ${ctxName}.${ruleName} has reducable ctx "${reducable_ctx}"`);
        // 2.1.1    remove (NR) from (NC)
        let position = types.indexOf(reducable_ctx);
        let types_ = types.slice(0, position).concat(types.slice(position + 1))
        var precedence_;
        if("precedence" in rule) {
          precedence_ = rule.precedence.slice(0, position).concat(rule.precedence.slice(position + 1))
        }
        // 2.1.2    for each constructor (RR) in (CC)
        Object.keys(calc.calc_structure[reducable_ctx])
        .forEach(tmpRuleName => {
          let rule_ = {};
          let tmpRule = calc.calc_structure[reducable_ctx][tmpRuleName];
          const genSyntax = function (key) {
            return (types.map(
              t => (reducable_ctxs.indexOf(t) > -1)
                ? ` ${tmpRule[key] || ""} `
                : " _ ").join(""))
                .replace(/\s+/g, " ").trim()
          }
          FORMAT_PORPS
            .filter(type => rule[type] || tmpRule[type])
            .forEach(type => rule_[type] = genSyntax(type));
          rule_.type = types_;
          if("precedence" in rule) {
            rule_.precedence = precedence_;
          }

          rule_ = Object.assign({}, rule, rule_);

          // if parent rule should be ignored in shallow embedding
          // and child rule not
          // new rule should be NOT shallow
          if(
            "shallow" in rule
            && !rule.shallow
            && (!("shallow" in tmpRule)
              || tmpRule.shallow)
          ) {
            delete rule_.shallow;
          }

          if(DEBUG) {
            console.log(clc.green(`\n\nHERE I SHOULD DO SOMETHING`));
            console.log(clc.red(position));
            console.log(JSON.stringify(rule,false,2));
            console.log(JSON.stringify(tmpRule, false, 2));
            console.log("---");
            console.log(`Rule_: ${JSON.stringify(rule_, false, 2)}`);
            console.log("\n");
          }
          // TODO - update precedence
          // TODO - what if i want to specify mixfix notation?
          ctx_[tmpRuleName] = rule_;
        })
      } else {
        ctx_[ruleName] = rule;
      }

    })
    calc_[ctxName] = ctx_;
  })


  Object.assign(calc, {"calc_structure": calc_});

  var Node = calcNode(calc);


  Object.keys(calc.calc_structure).forEach( k => {
    // console.log(`--- ${k} \n\n`);
    let rules = calc.calc_structure[k];
    let constructors = Object.keys(rules).map( r => constructParsingRule(k, rules, r) );
    let constructorsBrackets = Object.keys(rules).map( r => constructParsingRule(k, rules, r, true) ).filter(f => f !== null);
    grammar.bnf[k] = constructors.concat(constructorsBrackets);
    // grammar.bnf[k] = constructors;
  })


  Object.keys(symbols).forEach(s => {
    let smb = "\\" + s.split("").join("\\");
    grammar.lex.rules.push([smb, `return '${s}';`])
  });

  grammar.lex.rules.push( ["\\w+", "return 'string';"]);
  grammar.lex.rules.push( ["$", "return 'EOF';"]);


  // if(DEBUG) {
  //   Object.keys(grammar.bnf).forEach(k => {
  //     let rules = grammar.bnf[k].map(r => r[0].trim())
  //     console.log(`${k} = \n    ${rules.join("\n  | ")}\n`);
  //   })
  //   // console.log("\n\n", JSON.stringify(grammar, false, 2));
  // }


  var parser = new Parser(grammar);
  parser.yy.Node = Node;
  return {
    parser,
    grammar,
    calc
  };
}



module.exports = genParser;
