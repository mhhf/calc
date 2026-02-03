/**
 * Substitution: sub(ast, var, val) → ast
 * Pure, immutable.
 */

const { hashAST } = require('./ast-hash');

const eq = (a, b) => a === b || (a?.tag && b?.tag && hashAST(a) === hashAST(b));

const copy = ast => !ast?.tag ? ast : { tag: ast.tag, children: ast.children.map(copy) };

const sub = (ast, v, val) => {
  if (!ast?.tag) return ast;
  if (eq(ast, v)) return copy(val);
  const cs = ast.children.map(c => c?.tag ? sub(c, v, val) : c);
  return cs.some((c, i) => c !== ast.children[i]) ? { tag: ast.tag, children: cs } : ast;
};

const apply = (ast, theta) => theta.reduce((a, [v, val]) => sub(a, v, val), ast);

const occurs = (v, ast) => eq(v, ast) || (ast?.children?.some(c => occurs(v, c)) ?? false);

module.exports = { sub, apply, eq, copy, occurs };
