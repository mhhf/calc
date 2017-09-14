var Jison = require("jison");
const Lexer = require("jison-lex");
const ebnfParser = require("ebnf-parser");
const Parser = Jison.Parser;


const fs = require("fs");
const bnfGrammar = fs.readFileSync("src/llt.jison", "utf8");
const grammar = ebnfParser.parse(bnfGrammar)
const parser = new Parser(grammar);
const lexer = new Lexer(grammar.lex);

const TYPES = {
  type: {},
  bwd: {}
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
      let type = TYPES.bwd[ressourceName][i]

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

    // let def_str = bwd_rule
    //   .join('\n')

    // console.log(`bwd_def: \n${def_str}\n`);
  },
  fwd_def: function (def) {
    const foldFormula = function (ast) {
      switch (ast[0]) {
        case "-o":
          console.log("Formula_Loli");
          ast.slice(1).map(f => foldFormula(f))
          break;
        case "*":
          console.log("Formula_Tensor");
          foldFormula(ast.slice(1))
          break;
        default:
          console.log(`default`, JSON.stringify(ast, false, 2));
      }
    }

    foldFormula(def);

    LLT.db.fwd.push(def)
    // console.log(`fwd:`, JSON.stringify(def, false, 2));
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

module.exports = {parser, lexer};


