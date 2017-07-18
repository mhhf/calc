var Jison = require("jison");
var Parser = Jison.Parser;

var calc = require("./ll.json");
var Node = require("./node.js")(calc);
const DEBUG = !!process.env["DEBUG"];

var grammar = {
    "lex": {
        "rules": [
           ["\\s+",                    "/* skip whitespace */"],
           ["\\(",                     "return '('"],
           ["\\)",                     "return ')'"],
           [":",                     "return ':'"]
        ]
    },
    "bnf": {
      "Start": [["Sequent EOF", "return $1;"]]
    },
    "start": "Start",

    "operators": [
        ["left", ","],
        ["left", "-o"],
        ["left", "xx"]
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

  types.forEach(t => {
    NT[t] = true;
  });

  // Add found symbols to symbol list to pars them
  terms = terms
    .map(t => {
      if(t !== "") {
        t = t.trim();
        symbols[t] = t;
        return t;
      } else {
        return "";
      }
    }).join(" _ ");

  if (terms === "") {
    newterms = types.join(" ")
  } else {
    let i = 0;
    newterms = terms;
    while(newterms.indexOf("_") > -1) {
      newterms = newterms.replace(/\_/, types[i++])
    }
  }

  if(brackets && terms === "") {
    newterms = "( " + newterms + " )";
  } else if(brackets && terms !== "") {
    return null;
  }

  newexp = newterms
  .split(/\s+/)
  .filter(s => s !== "")
  .map((s,i) => (NT[s] ? ("$"+(i+1)) : ""))
  .filter(s => s !== "").join(', ');

  // console.log("\n\nRule:", rule);
  // console.log("syntax", syntax);
  // console.log("types", types);
  // console.log("terms", terms);
  // console.log("precedence", precedence);
  // console.log("newterms:", newterms);
  // console.log("newexp:", newexp);

  return [newterms, `$$ = new yy.Node("${k}", "${rule}", [${newexp}]);`];
}


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

if(DEBUG) {
  Object.keys(grammar.bnf).forEach(k => {
    let rules = grammar.bnf[k].map(r => r[0])
    console.log(`${k} = \n  ${rules.join(" |\n  ")}\n`);
  })
}


var parser = new Parser(grammar);
parser.yy.Node = Node;

module.exports = parser;
