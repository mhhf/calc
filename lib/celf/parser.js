/**
 * Celf Parser
 *
 * Parses pure Celf syntax as used in optimism-mde.
 * Returns an AST suitable for further processing.
 */

const ohm = require('ohm-js');
const fs = require('fs');
const path = require('path');

// Load grammar
const grammarPath = path.join(__dirname, 'grammar.ohm');
const grammarText = fs.readFileSync(grammarPath, 'utf8');
const grammar = ohm.grammar(grammarText);

// AST Node types
const AST = {
  // Program level
  Program: (declarations) => ({
    type: 'Program',
    declarations
  }),

  // Comment (preserved for documentation)
  Comment: (text) => ({
    type: 'Comment',
    text
  }),

  // Type declaration: name: type.
  TypeDecl: (name, typeExpr) => ({
    type: 'TypeDecl',
    name,
    typeExpr
  }),

  // Type expressions
  TypeArrow: (left, right) => ({
    type: 'TypeArrow',
    left,
    right
  }),

  TypeLoli: (left, right) => ({
    type: 'TypeLoli',
    left,
    right
  }),

  TypeKeyword: () => ({
    type: 'TypeKeyword'  // The 'type' keyword itself
  }),

  TypeAtom: (name) => ({
    type: 'TypeAtom',
    name
  }),

  // Clause declaration: name: head <- premises.
  ClauseDecl: (name, head, premises) => ({
    type: 'ClauseDecl',
    name,
    head,
    premises
  }),

  // Terms
  TermForward: (antecedent, consequent) => ({
    type: 'TermForward',
    antecedent,
    consequent
  }),

  TermLoli: (left, right) => ({
    type: 'TermLoli',
    left,
    right
  }),

  TermTensor: (left, right) => ({
    type: 'TermTensor',
    left,
    right
  }),

  TermBang: (inner) => ({
    type: 'TermBang',
    inner
  }),

  TermApp: (func, arg) => ({
    type: 'TermApp',
    func,
    arg
  }),

  TermVar: (name) => ({
    type: 'TermVar',
    name
  }),

  TermIdent: (name) => ({
    type: 'TermIdent',
    name
  })
};

// Semantics
const semantics = grammar.createSemantics().addOperation('toAST', {
  Program(declarations) {
    return AST.Program(declarations.children.map(d => d.toAST()).filter(d => d));
  },

  Comment(commentNode) {
    return AST.Comment(commentNode.sourceString.replace(/^%\s*/, '').trim());
  },

  TypeDecl(name, _colon, typeExpr, _dot) {
    return AST.TypeDecl(name.sourceString, typeExpr.toAST());
  },

  // Type = TypeLoli ("->" Type)?
  // Ohm flattens optional: 3 args (typeLoli, arrowOpt, typeOpt)
  Type(typeLoli, arrowOpt, typeOpt) {
    const left = typeLoli.toAST();
    if (arrowOpt.children.length === 0) {
      return left;
    }
    const right = typeOpt.children[0].toAST();
    return AST.TypeArrow(left, right);
  },

  // TypeLoli = TypeAtom ("-o" TypeLoli)?
  // Ohm flattens optional: 3 args (typeAtom, loliOpt, typeLoli)
  TypeLoli(typeAtom, loliOpt, typeLoliOpt) {
    const left = typeAtom.toAST();
    if (loliOpt.children.length === 0) {
      return left;
    }
    const right = typeLoliOpt.children[0].toAST();
    return AST.TypeLoli(left, right);
  },

  TypeAtom_typeKeyword(_type) {
    return AST.TypeKeyword();
  },

  TypeAtom_paren(_lparen, type, _rparen) {
    return type.toAST();
  },

  TypeAtom_atom(ident) {
    return AST.TypeAtom(ident.sourceString);
  },

  ClauseDecl(name, _colon, term, backChain) {
    const premises = backChain.toAST();
    return AST.ClauseDecl(name.sourceString, term.toAST(), premises);
  },

  // clauseName = ident ("/" ident)* - Ohm flattens the Iter
  clauseName(name, slashes, suffixIdents) {
    return this.sourceString;
  },

  BackChain_premise(_arrow, term, rest) {
    const premises = rest.toAST();
    return [term.toAST(), ...premises];
  },

  BackChain_end(_dot) {
    return [];
  },

  Term_forward(antecedent, _loli, _lbrace, consequent, _rbrace) {
    return AST.TermForward(antecedent.toAST(), consequent.toAST());
  },

  Term_loliTerm(left, _loli, right) {
    return AST.TermLoli(left.toAST(), right.toAST());
  },

  TermTensor_tensor(left, _star, right) {
    return AST.TermTensor(left.toAST(), right.toAST());
  },

  TermBang_bang(_bang, inner) {
    return AST.TermBang(inner.toAST());
  },

  // Application = Atom+ (fold left-associatively)
  Application(atoms) {
    const atomList = atoms.children.map(a => a.toAST());
    return atomList.reduce((acc, atom) => AST.TermApp(acc, atom));
  },

  Atom_paren(_lparen, term, _rparen) {
    return term.toAST();
  },

  Atom_var(v) {
    return AST.TermVar(v.sourceString);
  },

  Atom_ident(id) {
    return AST.TermIdent(id.sourceString);
  },

  // Pass-through rules
  TermTensor(e) { return e.toAST(); },
  TermBang(e) { return e.toAST(); },
  Atom(e) { return e.toAST(); },
  Declaration(e) { return e.toAST(); },
  Term(e) { return e.toAST(); },
  TypeAtom(e) { return e.toAST(); },

  // Terminals
  ident(_start, _rest) {
    return this.sourceString;
  },

  identStart(_char) {
    return this.sourceString;
  },

  var(_first, _rest) {
    return this.sourceString;
  },

  _iter(...children) {
    return children.map(c => c.toAST());
  },

  _terminal() {
    return this.sourceString;
  }
});

/**
 * Parse Celf source code
 * @param {string} source - Celf source code
 * @returns {Object} AST or error object
 */
function parse(source) {
  const matchResult = grammar.match(source);
  if (matchResult.failed()) {
    return {
      success: false,
      error: matchResult.message,
      shortMessage: matchResult.shortMessage
    };
  }
  return {
    success: true,
    ast: semantics(matchResult).toAST()
  };
}

/**
 * Parse a Celf file
 * @param {string} filePath - Path to .mde file
 * @returns {Object} AST or error object
 */
function parseFile(filePath) {
  const source = fs.readFileSync(filePath, 'utf8');
  const result = parse(source);
  if (!result.success) {
    result.filePath = filePath;
  }
  return result;
}

/**
 * Get the grammar for external use (e.g., extending)
 */
function getGrammar() {
  return grammar;
}

module.exports = {
  parse,
  parseFile,
  getGrammar,
  AST
};
