// TODO - to get rid of shift-reduce conflicts for "e bin_op e" expressions, I cannot have non-terminal bin_op rules, therefore they should be propagated up to generate multiple "e '+' e" rules.

// TODO - draw brackets if the precedence is not clear

var Jison = require("jison");
var Parser = Jison.Parser;

var calc = require("./ll.json");

const buffer = (str, max) => {
  let bufferLength = max - str.toString().length;
  if(bufferLength < 0) bufferLength = 0;
  return " ".repeat(bufferLength);
}

class Node {
  constructor (ruleName, ruleConstructor, vals) {
    this.ruleName = ruleName;
    this.ruleConstructor = ruleConstructor;
    this.type = calc.calc_structure[ruleName][ruleConstructor];
    this.vals = vals;
  }
  // TODO - construct dynamic head table
  toTree(prefix = "", last = false, attrs = []) {
    let tp, tree_prefix = tp =
      (prefix, last = false) =>
        prefix + (last ? "└ ": "├ ");
    let tn, tree_name = tn = this.ruleConstructor;
    let il, is_last = il = i => this.vals.length - 1 === i;
    let ev, evaluate = ev = (v,i) => (typeof v === "string") ? tp(prefix + (last?"  ":"│ "), il(i)) + v : v.toTree(prefix + (last? "  ":"│ "), il(i), attrs)

    let formula = " '" +this.toString() + "'";
    let location = tp(prefix, last) + tn;

    let draw = str => o => str + buffer(str, o.width)

    let precedence = (this.type.precedence || [0]);

    let attrTypes = {
      "location": draw(location),
      "formula": draw(formula),
      "precedence": draw(precedence.join(', ')),
      "ownprecedence": draw(precedence[precedence.length - 1]),
      "childprecedence": draw(precedence.slice(0, -1).join(', '))
    };

    let line = attrs
    .map(attr => attrTypes[attr.type](attr))
    .join("");

    // Format
    let children = this.vals.length > 0 ? "\n" + this.vals.map(ev).join("\n") : "";

    return `${line}${children}`;
  }
  toString(o) {
    o = Object.assign({
      style: "ascii",
      brackets: true
    }, o);
    let tmp = this.type[o.style] ||
      o.style === "isabelle_se" && this.type["isabelle"] ||
      o.style === "latex_se" && this.type["latex"] ||
      " _ ";
    // here two cases can occur:
    // 1. number of _ matches the number of values
    // 2. otherwise (I assume there is just one _ !!)
    let i=0;

    // TODO - lol, clean this scarry shit up
    const isBrackets = i => {
      let thisPrecedence = this.type.precedence[this.type.precedence.length - 1];
      let childPrecedence = this.vals[i].type && this.vals[i].type.precedence && this.vals[i].type.precedence[this.vals[i].type.precedence.length - 1] || 0;
      let child_has_enougth_children = typeof this.vals[i] === "object" && this.vals[i].vals.length > 1;
      let latexBrackets = typeof this.vals[i] !== "object" ||
        !("latex_brackets" in this.vals[i].type) || this.vals[i].type.latex_brackets;
      let b = child_has_enougth_children && this.vals.length > 1 && thisPrecedence >= childPrecedence && latexBrackets;
      return b;
    }

    // TODO - clean this up -- i don't need the if case here
    if((tmp.match(/\_/g) || []).length >= this.vals.length) {
      while((tmp.match(/\s+(_)|(_)\s+|^(_)$/) || []).length > 0) {
        let b = isBrackets(i);
        tmp = tmp.replace(/\s+(_)|(_)\s+|^(_)$/, (b?'( ':' ') + this.vals[i++].toString(o) + (b?' )':' '));
      }
    } else if((tmp.match(/\_/g) || []).length === 1) {
        tmp = tmp.replace("_", this.vals.map((v, i) => {
        return (isBrackets(i)?'( ': '') + v.toString(o) + (isBrackets(i)?' )':'');
      }).join(" "));
    }
    return tmp;
  }
}

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

// console.log(JSON.stringify(grammar, false, 2));

Jison.print = () => {}
var parser = new Parser(grammar);
parser.yy.Node = Node;


let latexFormula = function (str) {
  let node = parser.parse(str);
  string = node.toString({style: "latex_se", brackets: true});
  // string = string.replace(/^\((.*)\)$/, (a, b) => b);
  return string;
}

let latexRule = function (name, fs) {
  let latexFs = fs.reverse()
  .map(f => f === "" ? "" : latexFormula(f))
  .map(f => `{${f}}`)
  .join('');
  return `\\prftree[r]{$${name}$}${latexFs}`;
}

let formulaStr = "(?X, ?X), ?Y |- F?A xx F?B";
let node = parser.parse(formulaStr)

const formatTree = function (node, attrs) {
  let title = attrs.map(attr => attr.type.toUpperCase() + buffer(attr.type, attr.width)).join("")
  console.log(`${title}\n\nRoot\n`+node.toTree("", true, attrs))
}

// formatTree(node, [
//     {
//       type: "location",
//       width: 30
//     },
//     {
//       type: "ownprecedence",
//       width: 20
//     },
//     {
//       type: "childprecedence",
//       width: 16
//     }
//   ])

// console.log(latexFormula(formulaStr))


const rewriteLatexRule = function (str) {
  // Rewrite rules are bullshit
  const latexRewriteRules = [
    [ /\?\ X(\d*)/g, "\\Gamma$1" ],
    [ /\?\ Y(\d*)/g, "\\Delta$1" ],
    [ /\?\ Z(\d*)/g, "\\Theta$1" ],
    [ /\?\_F\ /g, "" ],
    [ /\?\_F\ /g, "" ],
    [ /\?\_F\ /g, "" ]
  ]
  // rewrite the result
  latexRewriteRules.forEach(rule => {
    str = str.replace(rule[0], (_, n) => rule[1].replace("$1", n === "" ? "" : "_" + n));
  })
  return str;
}

let calculus = [];
Object.keys(calc.rules).forEach(ctx => {
  calculus.push(`\n\n\\subsubsection*{${ctx}}\n\n`)
  calculus.push(`\\begin{tabularx}{\\linewidth}{CCC}\n`)
  Object.keys(calc.rules[ctx]).forEach((ruleName, i) => {
    let latexRuleName = calc.calc_structure_rules[ctx][ruleName].latex;
    let ruleDef = calc.rules[ctx][ruleName];
    let result = latexRule(latexRuleName, ruleDef);
    let formattedResult = rewriteLatexRule(result);
    calculus.push("  "+formattedResult);
    if(i < Object.keys(calc.rules[ctx]).length - 1) {
      if(i>0 && (i+1)%3 === 0) {
        calculus.push("\n\\\\\\\\\n");
      } else {
        calculus.push("\n&\n");
      }
    }
  })
  calculus.push(`\n\\end{tabularx}\n`)
})

console.log(calculus.join(""));

