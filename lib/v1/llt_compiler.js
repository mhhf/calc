var Jison = require("jison");
const Lexer = require("jison-lex");
const ebnfParser = require("ebnf-parser");
const Parser = Jison.Parser;
const Calc = require("./calc.js");
const Node = require("./node.js");
const calc_ = require("../../ll.json");
Calc.init(calc_);
const calc = Calc.calc;


const fs = require("fs");
const bnfGrammar = fs.readFileSync("src/llt.jison", "utf8");
const grammar = ebnfParser.parse(bnfGrammar)


let NT = {};
let symbols = {};
let numSymbols = 0;
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

let rules = calc.calc_structure["Formula"];
let constructors = Object.keys(rules)
  .filter( r => !calc.calc_structure["Formula"][r].skip_end_user_syntax )
  .map( r => constructParsingRule("Formula", rules, r, false, calc) );
let constructorsBrackets = Object.keys(rules)
  .filter( r => !calc.calc_structure["Formula"][r].skip_end_user_syntax )
  .map( r => constructParsingRule("Formula", rules, r, true, calc) ).filter(f => f !== null);
let l = constructors.concat(constructorsBrackets);
grammar.bnf["Formula"] = l;
// console.log(JSON.stringify(l, false, 2));

// console.log(grammar);



const parser = new Parser(grammar);
const lexer = new Lexer(grammar.lex);

const TYPES = {
  type: {},
  bwd: {},
  fwd: {}
};

const lookupType = function (el) {

}

const LLT = {
  type: function (type_def) {
    let type = type_def.pop();
    if(!(type in TYPES)) TYPES[type] = {};
    let constructor = type_def[0];
    let args = type_def.slice(1);
    if(constructor in TYPES[type]) console.log(`ERROR: constructor "${constructor}" of type ${type} already defined!!\n`);
    TYPES[type][constructor] = args;
    let args_string = args.length > 0 ? `(${args.join(' * ')})`: ''
    // console.log(`type: \n  ${constructor}${args_string}:${type}\n`);
  },
  bwd_def: function (rule_def) {

    // LOL - TODO - go directly to Node/ Sequent parsing
    //       and not over intermediate serialized step

    const lop = function (ressourceName, i, tv) {
      let type = ressourceName in TYPES.bwd
        ? TYPES.bwd[ressourceName][i]
        : ressourceName in TYPES.pred
          ? TYPES.pred[ressourceName][i]
          : console.log("UNDEFINED");

      let str = tv in TYPES[type]
        ? `TT? ${tv}`
        : `T? ${tv}`;
      return str;
    }

    const unfoldRule = function (rule) {
      let ressourceName = rule[0];
      let args = rule.slice(1);
      let args_str = args
        .map((param, i) => {
          return !Array.isArray(param)
            ? lop(ressourceName, i, param)
            : param.map(tv => {
                // TODO - error handling
                return lop(ressourceName, i, tv)
              })
              .join(' . ')
        })
        .join(', ')
      return `${ressourceName}(${args_str})`;
    }

    let bwd_rule = rule_def
      .map(unfoldRule)
      .map(str => `I |- -- : ${str}`);

    LLT.db.bwd.push(bwd_rule);

  },
  // This parses words to node
  toNode: function (def) {
    const foldParams = (ressourceName, params) => {

      let typeset = Object.assign({}, TYPES.bwd, TYPES.pred);
      let allParams = params.map((p, i) => {
        let type = typeset[ressourceName][i];
        if(Array.isArray(p)) {
          let paramList = p.map(pi => {
            if(pi in TYPES[type]) {
              let id = Calc.db.toIds["Term"]["Term_Atterm"];
              let id_ = Calc.db.toIds["Atterm"]["Atterm"];
              return new Node(id, [
                new Node(id_, [pi])
              ]);
            } else {
              let id = Calc.db.toIds["Term"]["Term_Freevar"];
              return new Node(id, [pi])
            }
          })
          if(paramList.length == 1) {
            return paramList[0];
          } else {
            let id = Calc.db.toIds["Term"]["Term_Concatenate"];
            return paramList
              .slice(1)
              .reduce((a, e) => {
                return new Node(id, [a, e]);
              }, paramList[0]);
          }
        } if(p in TYPES[type]) {
          let id = Calc.db.toIds["Term"]["Atterm"];
          let id_ = Calc.db.toIds["Atterm"]["Atterm"];
          return new Node(id, [
            new Node(id_, [p])
          ]);
        } else {
          let id = Calc.db.toIds["Term"]["Term_Freevar"];
          return new Node(id, [p])
        }
      })
      if(allParams.length == 1) {
        let id = Calc.db.toIds["TermList"]["Term_Atterm"];
        return new Node(id, [allParams[0]]);
      } else {
        let id = Calc.db.toIds["TermList"]["Term_Bin_Op"];
        let id_ = Calc.db.toIds["TermList"]["Term_Atterm"];
        return allParams
          .slice(0, -1)
          .reduceRight((a, e) => {
          return new Node(id, [e, a]);
        }, new Node(id_, [allParams.slice(-1)[0]]))
      }
    }

    if(def.length === 1) {
      let id = Calc.db.toIds["Atprop"]["Atprop"]
      return new Node(id, [def[0]]);
    } else {
      let id = Calc.db.toIds["Atprop"]["Atprop_Parametric"]
      let params = foldParams(def[0], def.slice(1))
      return new Node(id, [def[0]].concat(params));
    }
  },
  fwd_def: function (def) {
    LLT.db.fwd.push(def);
    // LLT.db.fwd.push(def)
    // console.log(`fwd: ${def}`);
  },
  ctx_def: function (name, ressources) {
    console.log(`ctx ${name}: ${ressources}`);
  }
}
LLT.db = {
  bwd: [],
  fwd: []
};
parser.yy.LLT = LLT;
parser.yy.Node = Node;

module.exports = {parser, lexer};


