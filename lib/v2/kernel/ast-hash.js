/**
 * AST Hashing (content-addressed)
 *
 * Separated from sequent.js to avoid circular dependencies with substitute.js
 */

const { hashCombine, hashString } = require('../../hash');

const hashAST = ast => {
  if (!ast?.tag) return hashString(String(ast ?? ''));
  let h = hashString(ast.tag);
  for (const c of ast.children) h = hashCombine(h, hashAST(c));
  return h;
};

module.exports = { hashAST };
