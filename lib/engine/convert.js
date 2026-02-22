/**
 * MDE → Content-Addressed Hash Converter
 *
 * Single-pass conversion from tree-sitter AST to hashes.
 * No intermediate representation.
 *
 * Complexity: O(n) where n = AST node count
 */

const Store = require('../kernel/store');
const fs = require('fs');
const path = require('path');
const mdeParser = require('../tree-sitter-mde');
const { expandHexNotation } = require('./hex');

// Binder stack for de Bruijn encoding of quantifier variables
const binderStack = [];

/**
 * Resolve #import(path) directives by inlining file contents (recursive)
 * @param {string} source
 * @param {string} basePath - absolute path of the file containing the imports
 * @returns {string}
 */
function resolveImports(source, basePath, imported = new Set()) {
  return source.replace(/#import\(([^)]+)\)/g, (match, relPath) => {
    const resolved = path.resolve(path.dirname(basePath), relPath.trim());
    if (imported.has(resolved)) return '';  // dedup: skip already-imported files
    imported.add(resolved);
    let imported_content = fs.readFileSync(resolved, 'utf8');
    return resolveImports(imported_content, resolved, imported);
  });
}

/**
 * Convert tree-sitter expr node to hash
 * @param {TreeSitterNode} node
 * @returns {number} hash
 */
function convertExpr(node) {
  if (!node) return null;

  switch (node.type) {
    case 'expr':
    case 'expr_plus':
    case 'expr_with':
    case 'expr_tensor':
    case 'expr_bang':
    case 'expr_app':
    case 'expr_atom':
      return convertExprInner(node);

    case 'identifier':
      // Normalize binary zero: e → binlit(0n)
      if (node.text === 'e') return Store.put('binlit', [0n]);
      return Store.put('atom', [node.text]);

    case 'number':
      return Store.put('binlit', [BigInt(node.text)]);

    case 'variable':
      // Check binder stack (innermost first) for bound variables
      for (let i = binderStack.length - 1; i >= 0; i--) {
        if (binderStack[i] === node.text) {
          const depth = binderStack.length - 1 - i;
          return Store.put('bound', [BigInt(depth)]);
        }
      }
      // MDE uppercase variables → metavars (prefix with _ for unification)
      return Store.put('freevar', ['_' + node.text]);

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
    return Store.put('type', []);
  }

  // Bang: !A (must check BEFORE single-child unwrap)
  // Each level of expr_bang with text starting with ! adds one bang
  if (node.type === 'expr_bang' && children.length === 1 && node.text.startsWith('!')) {
    // Count the leading ! in this node vs child
    const nodeExcl = node.text.match(/^!+/)?.[0]?.length || 0;
    const childExcl = children[0].text.match(/^!+/)?.[0]?.length || 0;
    if (nodeExcl > childExcl) {
      return Store.put('bang', [convertExpr(children[0])]);
    }
  }

  // Quantifiers: exists X. body / forall X. body
  if (node.type === 'expr' && children.length === 2) {
    const txt = node.text;
    if (txt.startsWith('exists ') || txt.startsWith('forall ')) {
      const kind = txt.startsWith('exists') ? 'exists' : 'forall';
      const varName = children[0].text; // variable node
      binderStack.push(varName);
      const body = convertExpr(children[1]);
      binderStack.pop();
      return Store.put(kind, [body]);
    }
  }

  // Binary operators: check by parent node type
  if (node.type === 'expr' && children.length === 2) {
    // Arrow: A -> B
    if (node.text.includes('->') && !node.text.includes('-o')) {
      return Store.put('arrow', [convertExpr(children[0]), convertExpr(children[1])]);
    }
    // Lollipop: A -o B
    if (node.text.includes('-o')) {
      // Forward rule: A -o { B }
      if (node.text.includes('{')) {
        return Store.put('loli', [convertExpr(children[0]), Store.put('monad', [convertExpr(children[1])])]);
      }
      return Store.put('loli', [convertExpr(children[0]), convertExpr(children[1])]);
    }
  }

  // Plus: A + B
  if (node.type === 'expr_plus' && children.length === 2) {
    return Store.put('plus', [convertExpr(children[0]), convertExpr(children[1])]);
  }

  // With: A & B
  if (node.type === 'expr_with' && children.length === 2) {
    return Store.put('with', [convertExpr(children[0]), convertExpr(children[1])]);
  }

  // Tensor: A * B
  // All items in a tensor are linear (consumed when matched)
  // The * is purely the tensor operator, not an affine marker
  if (node.type === 'expr_tensor' && children.length === 2) {
    return Store.put('tensor', [convertExpr(children[0]), convertExpr(children[1])]);
  }

  // Application: f x y z (left-associative, flattened)
  // Instead of app(app(app(atom("f"), x), y), z), produce {tag: 'f', children: [x, y, z]}
  if (node.type === 'expr_app' && children.length === 2) {
    // Collect the full application spine: walk left children to find head + all args
    const args = [];
    let cur = node;
    while (cur.type === 'expr_app') {
      const kids = cur.namedChildren.filter(c => c.type !== 'comment');
      if (kids.length !== 2) break;
      args.push(kids[1]); // right child = argument
      cur = kids[0];       // left child = deeper into spine
    }
    args.reverse(); // collected right-to-left, need left-to-right

    // cur is now the head (should be an identifier/atom)
    const headHash = convertExpr(cur);
    const headNode = Store.get(headHash);

    // Convert all arguments
    const argHashes = args.map(a => convertExpr(a));

    // Normalize binary constructors: (i/o binlit) → binlit
    if (headNode?.tag === 'atom' && args.length === 1 &&
        (headNode.children[0] === 'i' || headNode.children[0] === 'o')) {
      const rightNode = Store.get(argHashes[0]);
      if (rightNode?.tag === 'binlit') {
        const val = rightNode.children[0];
        return Store.put('binlit', [headNode.children[0] === 'i' ? val * 2n + 1n : val * 2n]);
      }
    }

    // Flat form: use atom name as tag, args as children
    if (headNode?.tag === 'atom') {
      return Store.put(headNode.children[0], argHashes);
    }

    // Variable head or unknown: keep curried app form
    let result = headHash;
    for (const arg of argHashes) {
      result = Store.put('app', [result, arg]);
    }
    return result;
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
 * @param {Map} queries
 * @param {Object} opts
 */
async function loadFile(filePath, types, clauses, forwardRules, queries, opts = {}) {
  let source = fs.readFileSync(filePath, 'utf8');

  // Resolve #import(path) directives first (before hex expansion,
  // so imported content gets hex-expanded too)
  source = resolveImports(source, filePath);

  // Expand N_XX hex notation to binary if enabled (default: true)
  if (opts.expandHex !== false) {
    source = expandHexNotation(source);
  }

  const tree = await mdeParser.parse(source);

  for (const child of tree.rootNode.children) {
    if (child.type === 'query_directive') {
      const kind = child.childForFieldName('kind')?.text;
      const bodyNode = child.childForFieldName('body');
      if (kind && bodyNode) queries.set(kind, convertExpr(bodyNode));
      continue;
    }
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
 * @returns {Promise<{ types: Map, clauses: Map, forwardRules: Array, queries: Map }>}
 */
async function load(filePaths) {
  const types = new Map();
  const clauses = new Map();
  const forwardRules = [];
  const queries = new Map();

  const paths = Array.isArray(filePaths) ? filePaths : [filePaths];
  for (const p of paths) {
    await loadFile(p, types, clauses, forwardRules, queries);
  }

  return { types, clauses, forwardRules, queries };
}

/**
 * Decompose a tensor expression hash into linear and persistent facts
 * Walks tensor tree, splitting !X into persistent and X into linear
 * @param {number} hash
 * @returns {{ linear: Object, persistent: Object }}
 */
function decomposeQuery(hash) {
  const linear = {}, persistent = {};
  function walk(h) {
    const node = Store.get(h);
    if (node.tag === 'tensor') {
      walk(node.children[0]);
      walk(node.children[1]);
    } else if (node.tag === 'bang') {
      persistent[node.children[0]] = true;
    } else {
      linear[h] = (linear[h] || 0) + 1;
    }
  }
  walk(hash);
  return { linear, persistent };
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
  extractConsequent,
  decomposeQuery
};
