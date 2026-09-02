/**
 * ILL Connective Table — DERIVED from ill.calc (TODO_0268 item B).
 *
 * Layer: ILL (Intuitionistic Linear Logic)
 *
 * One source of truth: a connective exists iff it is declared in ill.calc
 * with a @category annotation. The former hand-written table here was a
 * mirror of those annotations and had already drifted (forall missing,
 * polarity present/absent differently) — nothing checked the two agreed.
 *
 * Derivation is lazy + memoized: calculus.load side-effect-allocates
 * type-root atoms, so it must not run at import time (Store bit-identity).
 * The memoized table is pure data (names/arities/strings) and survives
 * Store.clear().
 *
 * The engine never queries tag names — it queries structural categories
 * via resolveConn() (formula-utils.js). till derives its table the same
 * way from till.calc (calculus/till/calculus-config.js).
 */

import path from 'path';
import calculus from '../../../lib/calculus/index.js';

const ILL_CALC = path.join(import.meta.dirname, '../ill.calc');

let _table = null;

/** Connective table tag → { category, arity, polarity? }, derived from
 *  ill.calc @category/@polarity annotations. Lazy, memoized. */
function illConnectives() {
  if (_table) return _table;
  const cs = calculus.load(ILL_CALC).constructors;
  const table = {};
  for (const [name, c] of Object.entries(cs)) {
    const ann = c.annotations || {};
    if (c.returnType !== 'formula' || !ann.category) continue;
    table[name] = {
      category: ann.category, arity: c.argTypes.length,
      ...(ann.polarity ? { polarity: ann.polarity } : {}),
    };
  }
  _table = table;
  return table;
}

export { illConnectives };
export default { illConnectives };
