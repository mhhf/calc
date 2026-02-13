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
const { expandHexNotation } = require('./hex');

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
      // Normalize binary zero: e → binlit(0n)
      if (node.text === 'e') return Store.intern('binlit', [0n]);
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
  // All items in a tensor are linear (consumed when matched)
  // The * is purely the tensor operator, not an affine marker
  if (node.type === 'expr_tensor' && children.length === 2) {
    return Store.intern('tensor', [convertExpr(children[0]), convertExpr(children[1])]);
  }

  // Application: f x (left-associative)
  if (node.type === 'expr_app' && children.length === 2) {
    const left = convertExpr(children[0]);
    const right = convertExpr(children[1]);

    // Normalize binary constructors: (i/o binlit) → binlit
    const leftNode = Store.get(left);
    if (leftNode?.tag === 'atom' && (leftNode.children[0] === 'i' || leftNode.children[0] === 'o')) {
      const rightNode = Store.get(right);
      if (rightNode?.tag === 'binlit') {
        const val = rightNode.children[0];
        return Store.intern('binlit', [leftNode.children[0] === 'i' ? val * 2n + 1n : val * 2n]);
      }
    }

    return Store.intern('app', [left, right]);
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
 * Load single MDE file into existing collections
 * @param {string} filePath
 * @param {Map} types
 * @param {Map} clauses
 * @param {Array} forwardRules
 */
async function loadFile(filePath, types, clauses, forwardRules, opts = {}) {
  let source = fs.readFileSync(filePath, 'utf8');

  // Expand N_XX hex notation to binary if enabled (default: true)
  if (opts.expandHex !== false) {
    source = expandHexNotation(source);
  }

  const tree = await mdeParser.parse(source);

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
}

/**
 * Load MDE file(s)
 * @param {string|string[]} filePaths - single path or array of paths
 * @returns {Promise<{ types: Map, clauses: Map, forwardRules: Array }>}
 */
async function load(filePaths) {
  const types = new Map();
  const clauses = new Map();
  const forwardRules = [];

  const paths = Array.isArray(filePaths) ? filePaths : [filePaths];
  for (const p of paths) {
    await loadFile(p, types, clauses, forwardRules);
  }

  return { types, clauses, forwardRules };
}

/**
 * Parse a single expression string
 * @param {string} source
 * @returns {Promise<number>} hash
 */
async function parseExpr(source, opts = {}) {
  // Expand N_XX hex notation to binary if enabled (default: true)
  let expandedSource = source;
  if (opts.expandHex !== false) {
    expandedSource = expandHexNotation(source);
  }

  // Wrap in declaration to parse
  const tree = await mdeParser.parse(`_tmp: ${expandedSource}.`);
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
