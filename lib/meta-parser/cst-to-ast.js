/**
 * Tree-sitter based Celf Parser
 *
 * High-performance parser for MDE/Celf syntax using tree-sitter.
 * Handles deeply nested expressions without stack overflow.
 * Works in both Node.js and browser (via WASM).
 *
 * API compatible with the Ohm-based parser (lib/celf/parser.js)
 */

const fs = require('fs');
const path = require('path');

// Lazy-loaded parser instance
let Parser = null;
let MDE = null;
let initPromise = null;

/**
 * Initialize the tree-sitter parser (async, call once)
 */
async function init() {
  if (Parser && MDE) return;
  if (initPromise) return initPromise;

  initPromise = (async () => {
    const TreeSitter = require('web-tree-sitter');
    // web-tree-sitter 0.25+ requires Parser.init() before constructing
    const TSParser = TreeSitter.Parser;
    const TSLanguage = TreeSitter.Language;

    await TSParser.init();
    Parser = new TSParser();

    const wasmPath = path.join(__dirname, '../tree-sitter-mde/tree-sitter-mde.wasm');
    if (!fs.existsSync(wasmPath)) {
      throw new Error(
        `Tree-sitter WASM not built. Run: npm run build:ts:wasm\n` +
        `Expected: ${wasmPath}`
      );
    }
    MDE = await TSLanguage.load(wasmPath);
    Parser.setLanguage(MDE);
  })();

  return initPromise;
}

// Operator mapping tables (data-driven instead of hardcoded cases)
const BINARY_OPS = { 'expr_tensor': 'tensor', 'expr_with': 'with', 'expr_plus': 'plus' };
const UNARY_PREFIX_OPS = { 'expr_bang': { prefix: '!', name: 'bang' } };
const LINEAR_IMPL = { name: 'loli', forward: 'forward' };

// AST Node types (same as Ohm parser for compatibility)
const AST = {
  Program: (declarations) => ({
    type: 'Program',
    declarations
  }),

  Comment: (text) => ({
    type: 'Comment',
    text
  }),

  TypeDecl: (name, typeExpr, annotations = []) => ({
    type: 'TypeDecl',
    name,
    typeExpr,
    annotations
  }),

  TypeArrow: (left, right) => ({
    type: 'TypeArrow',
    left,
    right
  }),

  TypeKeyword: () => ({
    type: 'TypeKeyword'
  }),

  ClauseDecl: (name, head, premises, annotations = []) => ({
    type: 'ClauseDecl',
    name,
    head,
    premises,
    annotations
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
  }),

  // Annotation types (for extended Celf / .calc files)
  Annotation: (key, value) => ({
    type: 'Annotation',
    key,
    value
  }),

  StringValue: (value) => ({
    type: 'StringValue',
    value
  }),

  PrecValue: (precedence, associativity) => ({
    type: 'PrecValue',
    precedence,
    associativity  // 'left', 'right', 'none', or null
  }),

  BoolValue: (value) => ({
    type: 'BoolValue',
    value
  }),

  IdentValue: (name) => ({
    type: 'IdentValue',
    name
  })
};

/**
 * Convert tree-sitter CST node to AST
 */
function cstToAst(node, source) {
  if (!node) return null;

  const nodeType = node.type;
  const getText = () => source.slice(node.startIndex, node.endIndex);
  const getNamedChildren = () => {
    const children = [];
    for (let i = 0; i < node.namedChildCount; i++) {
      children.push(node.namedChild(i));
    }
    return children;
  };

  switch (nodeType) {
    case 'source_file': {
      const declarations = [];
      for (let i = 0; i < node.namedChildCount; i++) {
        const child = node.namedChild(i);
        if (child.type === 'declaration') {
          declarations.push(cstToAst(child, source));
        } else if (child.type === 'directive') {
          declarations.push(cstToAst(child, source));
        } else if (child.type === 'comment') {
          const text = source.slice(child.startIndex, child.endIndex);
          declarations.push(AST.Comment(text.replace(/^%\s*/, '').trim()));
        }
      }
      return AST.Program(declarations);
    }

    case 'directive': {
      // Directive: @name arg1 arg2 ...
      const nameNode = node.childForFieldName('name');
      const name = '@' + source.slice(nameNode.startIndex, nameNode.endIndex);

      // Collect args
      const args = [];
      for (let i = 0; i < node.namedChildCount; i++) {
        const child = node.namedChild(i);
        if (child.type === 'directive_arg') {
          args.push(cstToAst(child, source));
        }
      }

      // Return as ClauseDecl with @name convention
      const head = args.length > 0 ? args[0] : null;
      const premises = args.slice(1);
      return AST.ClauseDecl(name, head, premises, []);
    }

    case 'directive_arg': {
      const namedChildren = getNamedChildren();
      if (namedChildren.length === 1) {
        return cstToAst(namedChildren[0], source);
      }
      return AST.TermIdent(getText());
    }

    case 'key_value_pair': {
      const keyNode = node.childForFieldName('key');
      const valueNode = node.childForFieldName('value');
      const key = source.slice(keyNode.startIndex, keyNode.endIndex);
      const value = cstToAst(valueNode, source);
      // Return as an Annotation object so generator can extract key/value
      return AST.Annotation(key, value);
    }

    case 'declaration': {
      const nameNode = node.childForFieldName('name');
      const bodyNode = node.childForFieldName('body');
      const annotationsNode = node.childForFieldName('annotations');
      const name = source.slice(nameNode.startIndex, nameNode.endIndex);
      const body = cstToAst(bodyNode, source);
      const annotations = annotationsNode ? cstToAst(annotationsNode, source) : [];

      // Check if this is a type declaration
      if (isTypeExpr(body.head || body)) {
        return AST.TypeDecl(name, body.head || body, annotations);
      }
      return AST.ClauseDecl(name, body.head, body.premises || [], annotations);
    }

    case 'annotation_block': {
      const annotations = [];
      for (let i = 0; i < node.namedChildCount; i++) {
        const child = node.namedChild(i);
        if (child.type === 'annotation') {
          annotations.push(cstToAst(child, source));
        }
      }
      return annotations;
    }

    case 'annotation': {
      const keyNode = node.childForFieldName('key');
      const valueNode = node.childForFieldName('value');
      const key = source.slice(keyNode.startIndex, keyNode.endIndex);
      const value = valueNode ? cstToAst(valueNode, source) : null;
      return AST.Annotation(key, value);
    }

    case 'annotation_value': {
      // Descend to the actual value type
      const namedChildren = getNamedChildren();
      if (namedChildren.length === 1) {
        const child = namedChildren[0];
        // Handle identifier specially in annotation context
        if (child.type === 'identifier') {
          return AST.IdentValue(source.slice(child.startIndex, child.endIndex));
        }
        return cstToAst(child, source);
      }
      return null;
    }

    case 'string_literal': {
      // Extract content between quotes and unescape
      const text = getText();
      const raw = text.slice(1, -1);  // Remove surrounding quotes
      // Unescape: \\ -> \, \n -> newline, \t -> tab
      const content = raw.replace(/\\(.)/g, (_, c) => {
        if (c === 'n') return '\n';
        if (c === 't') return '\t';
        return c;  // \\ -> \, \x -> x
      });
      return AST.StringValue(content);
    }

    case 'prec_value': {
      const namedChildren = getNamedChildren();
      const numNode = namedChildren.find(c => c.type === 'number');
      const assocNode = namedChildren.find(c => c.type === 'associativity');
      const precedence = parseInt(source.slice(numNode.startIndex, numNode.endIndex), 10);
      const associativity = assocNode ? source.slice(assocNode.startIndex, assocNode.endIndex) : null;
      return AST.PrecValue(precedence, associativity);
    }

    case 'bool_literal': {
      const text = getText();
      return AST.BoolValue(text === 'true');
    }

    case 'number': {
      // Standalone number (shouldn't happen often, prec_value handles this)
      return AST.PrecValue(parseInt(getText(), 10), null);
    }

    case 'decl_body': {
      const exprNode = node.childForFieldName('expr');
      const premisesNode = node.childForFieldName('premises');
      const head = cstToAst(exprNode, source);
      const premises = premisesNode ? cstToAst(premisesNode, source) : [];
      return { head, premises };
    }

    case 'back_chain': {
      const premises = [];
      for (let i = 0; i < node.namedChildCount; i++) {
        const child = node.namedChild(i);
        if (child.type === 'expr') {
          premises.push(cstToAst(child, source));
        }
      }
      return premises;
    }

    case 'expr': {
      const namedChildren = getNamedChildren();
      if (namedChildren.length === 1) {
        return cstToAst(namedChildren[0], source);
      }

      // Check for operators by looking at the text
      const text = getText();
      if (text.includes('->')) {
        const left = cstToAst(namedChildren[0], source);
        const right = cstToAst(namedChildren[1], source);
        return AST.TypeArrow(left, right);
      }
      if (text.includes('-o')) {
        const left = cstToAst(namedChildren[0], source);
        const right = cstToAst(namedChildren[1], source);
        // Check for forward rule: -o { ... }
        const opName = text.includes('{') ? LINEAR_IMPL.forward : LINEAR_IMPL.name;
        return AST.TermApp(AST.TermApp(AST.TermIdent(opName), left), right);
      }

      return cstToAst(namedChildren[0], source);
    }

    // Generic handling of binary and unary operator nodes via mapping tables
    case 'expr_plus':
    case 'expr_with':
    case 'expr_tensor': {
      const opName = BINARY_OPS[nodeType];
      const namedChildren = getNamedChildren();
      if (namedChildren.length === 1) {
        return cstToAst(namedChildren[0], source);
      }
      // Left-associative
      let result = cstToAst(namedChildren[0], source);
      for (let i = 1; i < namedChildren.length; i++) {
        result = AST.TermApp(AST.TermApp(AST.TermIdent(opName), result), cstToAst(namedChildren[i], source));
      }
      return result;
    }

    case 'expr_bang': {
      const unaryOp = UNARY_PREFIX_OPS[nodeType];
      // Check if this node has the prefix operator
      let hasPrefix = false;
      for (let i = 0; i < node.childCount; i++) {
        const child = node.child(i);
        if (!child.isNamed && source.slice(child.startIndex, child.endIndex) === unaryOp.prefix) {
          hasPrefix = true;
          break;
        }
      }
      const namedChildren = getNamedChildren();
      if (!hasPrefix && namedChildren.length === 1) {
        return cstToAst(namedChildren[0], source);
      }
      return AST.TermApp(AST.TermIdent(unaryOp.name), cstToAst(namedChildren[0], source));
    }

    case 'expr_app': {
      const namedChildren = getNamedChildren();
      if (namedChildren.length === 1) {
        return cstToAst(namedChildren[0], source);
      }
      // Left-associative
      let result = cstToAst(namedChildren[0], source);
      for (let i = 1; i < namedChildren.length; i++) {
        result = AST.TermApp(result, cstToAst(namedChildren[i], source));
      }
      return result;
    }

    case 'expr_atom': {
      const namedChildren = getNamedChildren();
      if (namedChildren.length === 1) {
        return cstToAst(namedChildren[0], source);
      }
      // Check for 'type' keyword
      const text = getText();
      if (text === 'type') {
        return AST.TypeKeyword();
      }
      return AST.TermIdent(text);
    }

    case 'identifier': {
      return AST.TermIdent(getText());
    }

    case 'variable': {
      return AST.TermVar(getText());
    }

    default:
      // For unknown nodes, try to descend
      const namedChildren = getNamedChildren();
      if (namedChildren.length === 1) {
        return cstToAst(namedChildren[0], source);
      }
      return null;
  }
}

/**
 * Check if an AST node represents a type expression
 */
function isTypeExpr(node) {
  if (!node) return false;
  if (node.type === 'TypeKeyword') return true;
  if (node.type === 'TypeArrow') return true;
  if (node.type === 'TermIdent' && node.name === 'type') return true;
  return false;
}

/**
 * Parse Celf source code (async)
 * @param {string} source - Celf source code
 * @returns {Promise<Object>} AST or error object
 */
async function parse(source) {
  try {
    await init();

    const tree = Parser.parse(source);

    // Check for errors
    if (tree.rootNode.hasError) {
      const errors = [];
      const findErrors = (node) => {
        if (node.type === 'ERROR' || node.isMissing) {
          errors.push({
            row: node.startPosition.row + 1,
            column: node.startPosition.column,
            text: source.slice(node.startIndex, Math.min(node.endIndex, node.startIndex + 20))
          });
        }
        for (let i = 0; i < node.childCount; i++) {
          findErrors(node.child(i));
        }
      };
      findErrors(tree.rootNode);

      return {
        success: false,
        error: `Parse error at line ${errors[0]?.row || '?'}: ${errors[0]?.text || 'unknown'}`,
        shortMessage: `Parse error at line ${errors[0]?.row || '?'}`,
        errors
      };
    }

    const ast = cstToAst(tree.rootNode, source);
    return {
      success: true,
      ast
    };
  } catch (err) {
    return {
      success: false,
      error: err.message,
      shortMessage: err.message
    };
  }
}

/**
 * Parse a Celf file (async)
 * @param {string} filePath - Path to .mde file
 * @returns {Promise<Object>} AST or error object
 */
async function parseFile(filePath) {
  const source = fs.readFileSync(filePath, 'utf8');
  const result = await parse(source);
  if (!result.success) {
    result.filePath = filePath;
  }
  return result;
}

/**
 * Get raw tree-sitter tree (for debugging/tools)
 * @param {string} source - Celf source code
 * @returns {Promise<Object>} tree-sitter Tree
 */
async function parseRaw(source) {
  await init();
  return Parser.parse(source);
}

/**
 * Synchronous parse (requires init() to be called first)
 * Use for performance-critical code after initialization
 */
function parseSync(source) {
  if (!Parser) {
    throw new Error('Parser not initialized. Call await init() first.');
  }

  const tree = Parser.parse(source);

  if (tree.rootNode.hasError) {
    const errors = [];
    const findErrors = (node) => {
      if (node.type === 'ERROR' || node.isMissing) {
        errors.push({
          row: node.startPosition.row + 1,
          column: node.startPosition.column,
          text: source.slice(node.startIndex, Math.min(node.endIndex, node.startIndex + 20))
        });
      }
      for (let i = 0; i < node.childCount; i++) {
        findErrors(node.child(i));
      }
    };
    findErrors(tree.rootNode);

    return {
      success: false,
      error: `Parse error at line ${errors[0]?.row || '?'}: ${errors[0]?.text || 'unknown'}`,
      shortMessage: `Parse error at line ${errors[0]?.row || '?'}`,
      errors
    };
  }

  return {
    success: true,
    ast: cstToAst(tree.rootNode, source)
  };
}

module.exports = {
  init,
  parse,
  parseFile,
  parseRaw,
  parseSync,
  AST
};
