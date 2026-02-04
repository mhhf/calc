/**
 * MDE → Content-Addressed Hash Converter
 *
 * Single-pass conversion from tree-sitter AST to hashes.
 * No intermediate representation.
 *
 * Complexity: O(n) where n = AST node count
 */

const Store = require('../v2/kernel/store');
const fs = require('fs');
const mdeParser = require('../tree-sitter-mde');

/**
 * Convert tree-sitter expr node to hash
 * @param {TreeSitterNode} node
 * @returns {number} hash
 */
function convertExpr(node) {
  if (!node) return null;

  switch (node.type) {
    case 'expr':
    case 'expr_with':
    case 'expr_tensor':
    case 'expr_bang':
    case 'expr_app':
    case 'expr_atom':
      return convertExprInner(node);

    case 'identifier':
      return Store.intern('atom', [node.text]);

    case 'variable':
      // MDE uppercase variables → metavars (prefix with _ for unification)
      return Store.intern('freevar', ['_' + node.text]);

    default:
      // Handle named children for wrapper nodes
      if (node.namedChildCount === 1) {
        return convertExpr(node.namedChild(0));
      }
      throw new Error(`Unknown node type: ${node.type}`);
  }
}

/**
 * Convert expression inner nodes
 */
function convertExprInner(node) {
  // Filter out comments
  const children = node.namedChildren.filter(c => c.type !== 'comment');

  // Check for 'type' keyword
  if (node.type === 'expr_atom' && node.text === 'type') {
    return Store.intern('type', []);
  }

  // Bang: !A (must check BEFORE single-child unwrap)
  // Each level of expr_bang with text starting with ! adds one bang
  if (node.type === 'expr_bang' && children.length === 1 && node.text.startsWith('!')) {
    // Count the leading ! in this node vs child
    const nodeExcl = node.text.match(/^!+/)?.[0]?.length || 0;
    const childExcl = children[0].text.match(/^!+/)?.[0]?.length || 0;
    if (nodeExcl > childExcl) {
      return Store.intern('bang', [convertExpr(children[0])]);
    }
  }

  // Binary operators: check by parent node type
  if (node.type === 'expr' && children.length === 2) {
    // Arrow: A -> B
    if (node.text.includes('->') && !node.text.includes('-o')) {
      return Store.intern('arrow', [convertExpr(children[0]), convertExpr(children[1])]);
    }
    // Lollipop: A -o B
    if (node.text.includes('-o')) {
      // Forward rule: A -o { B }
      if (node.text.includes('{')) {
        return Store.intern('loli', [convertExpr(children[0]), Store.intern('monad', [convertExpr(children[1])])]);
      }
      return Store.intern('loli', [convertExpr(children[0]), convertExpr(children[1])]);
    }
  }

  // With: A & B
  if (node.type === 'expr_with' && children.length === 2) {
    return Store.intern('with', [convertExpr(children[0]), convertExpr(children[1])]);
  }

  // Tensor: A * B
  if (node.type === 'expr_tensor' && children.length === 2) {
    return Store.intern('tensor', [convertExpr(children[0]), convertExpr(children[1])]);
  }

  // Application: f x (left-associative)
  if (node.type === 'expr_app' && children.length === 2) {
    return Store.intern('app', [convertExpr(children[0]), convertExpr(children[1])]);
  }

  // Single child - unwrap (wrapper nodes, parentheses)
  if (children.length === 1) {
    return convertExpr(children[0]);
  }

  throw new Error(`Cannot convert expr: ${node.type} with ${children.length} children: ${node.text.slice(0, 50)}`);
}

/**
 * Convert premises (backward chaining: <- expr <- expr ...)
 * @param {TreeSitterNode} backChain
 * @returns {number[]} array of hashes
 */
function convertPremises(backChain) {
  if (!backChain) return [];

  const premises = [];
  for (const child of backChain.namedChildren) {
    if (child.type === 'expr') {
      premises.push(convertExpr(child));
    }
  }
  return premises;
}

/**
 * Parse declaration name (handles name/variant style)
 * @param {TreeSitterNode} nameNode
 * @returns {string}
 */
function parseDeclName(nameNode) {
  return nameNode.text;
}

/**
 * Check if expression contains monad (forward rule)
 * @param {number} hash
 * @returns {boolean}
 */
function hasMonad(hash) {
  const node = Store.get(hash);
  if (!node) return false;
  if (node.tag === 'monad') return true;
  for (const c of node.children) {
    if (typeof c === 'number' && hasMonad(c)) return true;
  }
  return false;
}

/**
 * Extract antecedent from lollipop: A -o B → A
 * @param {number} hash
 * @returns {number}
 */
function extractAntecedent(hash) {
  const node = Store.get(hash);
  if (node?.tag === 'loli') return node.children[0];
  return hash;
}

/**
 * Extract consequent from lollipop: A -o B → B
 * @param {number} hash
 * @returns {number}
 */
function extractConsequent(hash) {
  const node = Store.get(hash);
  if (node?.tag === 'loli') return node.children[1];
  return hash;
}

/**
 * Load MDE file
 * @param {string} filePath
 * @returns {Promise<{ types: Map, clauses: Map, forwardRules: Array }>}
 */
async function load(filePath) {
  const source = fs.readFileSync(filePath, 'utf8');
  const tree = await mdeParser.parse(source);

  const types = new Map();
  const clauses = new Map();
  const forwardRules = [];

  for (const child of tree.rootNode.children) {
    if (child.type !== 'declaration') continue;

    const nameNode = child.childForFieldName('name');
    const bodyNode = child.childForFieldName('body');
    if (!nameNode || !bodyNode) continue;

    const name = parseDeclName(nameNode);
    const exprNode = bodyNode.childForFieldName('expr');
    const premisesNode = bodyNode.childForFieldName('premises');

    if (!exprNode) continue;

    const hash = convertExpr(exprNode);
    const premises = convertPremises(premisesNode);

    if (hasMonad(hash)) {
      // Forward rule
      forwardRules.push({
        name,
        hash,
        antecedent: extractAntecedent(hash),
        consequent: extractConsequent(hash)
      });
    } else if (premises.length > 0) {
      // Backward chaining clause
      clauses.set(name, { hash, premises });
    } else {
      // Type or constructor
      types.set(name, hash);
    }
  }

  return { types, clauses, forwardRules };
}

/**
 * Parse a single expression string
 * @param {string} source
 * @returns {Promise<number>} hash
 */
async function parseExpr(source) {
  // Wrap in declaration to parse
  const tree = await mdeParser.parse(`_tmp: ${source}.`);
  const decl = tree.rootNode.child(0);
  if (!decl || decl.type !== 'declaration') {
    throw new Error('Parse error');
  }
  const body = decl.childForFieldName('body');
  const expr = body.childForFieldName('expr');
  return convertExpr(expr);
}

module.exports = {
  load,
  parseExpr,
  convertExpr,
  hasMonad,
  extractAntecedent,
  extractConsequent
};
