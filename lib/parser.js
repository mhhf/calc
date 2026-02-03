/**
 * Parser generator - v1 Jison parser from ll.json
 *
 * @deprecated This is v1 code. Use lib/v2 instead for new code.
 *   const v2 = require('./lib/v2');
 *   const formula = await v2.parseFormula('A -o B');
 *   const sequent = await v2.parseSequent('A, B |- C');
 */

// TODO - remove latex_brakcets variable since this can be inferred from the context
//
//
// TODO - get precedence right - generate overview in doc with characteristic symbols and stuff

var Jison = require("jison");
var Parser = Jison.Parser;

var clc = require('cli-color');

var Node = require("./node.js");
const DEBUG = typeof process !== 'undefined' && !!process.env["DEBUG"];
const Calc = require("./calc.js");

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
        ["right", "*"],
        ["right", "&"],
        ["right", "."],
        ["left", ":"],
        ["left", "!"],
        ["left", "lax"],
    ],

};


let symbols = {};
let numSymbols = 0;

let NT = {};

function constructParsingRule (k, rules, rule, brackets = false, calc) {
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

  let id = Calc.db.toIds[k][rule];
  let _type = Calc.db.rules[id];
  return [newterms, `$$ = new yy.Node(${id}, [${newexp}]);`];
}


function genParser(calc) {
  // Initialize Calc if not already done
  if (!Calc.initialized) {
    Calc.init(calc);
  }
  calc = Calc.calc;
  // console.log(calc);
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


  // var Node = calcNode(calc);


  Object.keys(calc.calc_structure)
    .forEach( k => {
    let rules = calc.calc_structure[k];
    let constructors = Object.keys(rules).map( r => constructParsingRule(k, rules, r, false, calc) );
    let constructorsBrackets = Object.keys(rules).map( r => constructParsingRule(k, rules, r, true, calc) ).filter(f => f !== null);
    grammar.bnf[k] = constructors.concat(constructorsBrackets);
  })


  Object.keys(symbols).forEach(s => {
    let smb = s.split("")
    .map(c => {
      let code = c.charCodeAt(0);
      if(code >= 65 && code <= 90
      || code >= 97 && code <= 122) {
        return c;
      } else {
        return "\\"+c;
      }
    })
    .join("")
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
    calc,
    Calc
  };
}



module.exports = genParser;
