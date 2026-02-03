/**
 * AST Utilities
 *
 * Pure functions for working with v2 ASTs ({ tag, children }).
 * Uses content-addressing via hashAST for efficient equality.
 */

const { hashAST } = require('./sequent');

// Re-export from substitute for convenience
const { copy, eq } = require('./substitute');

/**
 * Get free variable names from AST
 * @param {Object} ast - AST node
 * @returns {string[]} - Unique variable names
 */
function freeVars(ast) {
  const vars = new Set();

  function walk(node) {
    if (!node?.tag) return;
    if (node.tag === 'freevar') {
      vars.add(node.children[0]);
      return;
    }
    for (const child of node.children) {
      if (child?.tag) walk(child);
    }
  }

  walk(ast);
  return [...vars];
}

/**
 * Check if formula is atomic (atom or freevar)
 * @param {Object} ast - AST node
 * @returns {boolean}
 */
function isAtomic(ast) {
  return ast?.tag === 'atom' || ast?.tag === 'freevar';
}

/**
 * Get the principal connective (tag) of formula
 * @param {Object} ast - AST node
 * @returns {string|null}
 */
function connective(ast) {
  return ast?.tag || null;
}

/**
 * Get content-addressed hash
 * @param {Object} ast - AST node
 * @returns {bigint}
 */
function hash(ast) {
  return hashAST(ast);
}

/**
 * Map over AST children (returns new AST if any child changed)
 * @param {Object} ast - AST node
 * @param {Function} fn - Function to apply to each child
 * @returns {Object} - New AST or same if unchanged
 */
function mapChildren(ast, fn) {
  if (!ast?.tag) return ast;
  const newChildren = ast.children.map(fn);
  const changed = newChildren.some((c, i) => c !== ast.children[i]);
  return changed ? { tag: ast.tag, children: newChildren } : ast;
}

/**
 * Fold over AST (depth-first)
 * @param {Object} ast - AST node
 * @param {Function} fn - Function(acc, node) -> acc
 * @param {*} initial - Initial accumulator value
 * @returns {*} - Final accumulator value
 */
function fold(ast, fn, initial) {
  let acc = fn(initial, ast);
  if (ast?.children) {
    for (const child of ast.children) {
      if (child?.tag) acc = fold(child, fn, acc);
    }
  }
  return acc;
}

module.exports = {
  copy,
  eq,
  freeVars,
  isAtomic,
  connective,
  hash,
  mapChildren,
  fold
};
