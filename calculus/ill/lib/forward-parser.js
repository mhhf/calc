/**
 * ILL forward-engine expression parser (TODO_0086).
 *
 * Extracted from lib/engine/convert.js's former baked-in fallback: the
 * generic engine no longer knows any calculus's location or surface —
 * every calculus supplies `cc.loader.buildParser` (this is ILL's; till/
 * gill/will build theirs via kit.makeForwardParserBuilder).
 *
 * Formula operators derive from ill.calc constructors, plus engine-
 * specific extras: `concat` (++) is a term-level operator used in EVM
 * programs, not in the calculus. Lazy: built on first use (~20ms, loads
 * the whole ILL calculus); convert.js memoizes per loaderConfig object.
 */

import path from 'path';
import calculusLoader from '../../../lib/calculus/index.js';
import { parserTables, parserFromTables } from '../../../lib/calculus/builders.js';

const ILL_DIR = path.join(import.meta.dirname, '..');

/** Load the ILL backward calculus (ill.calc + ill.rules → buildCalculus). */
function loadILL() {
  return calculusLoader.load(
    path.join(ILL_DIR, 'ill.calc'),
    path.join(ILL_DIR, 'ill.rules')
  );
}

/** Build the .ill-format expression parser for ILL programs. */
function buildForwardParser() {
  const ill = loadILL();
  const tables = parserTables(ill.constructors);
  // Formula-returning constructors only (exclude structural: comma, hyp,
  // seq); loli is re-added by forwardRules with special `-o { }` handling.
  tables.operators = tables.operators
    .filter(o => ill.constructors[o.name]?.returnType === 'formula' && o.name !== 'loli');
  tables.operators.push({ name: 'concat', op: '++', precedence: 55, assoc: 'left' });
  return parserFromTables({
    ...tables,
    binders: { exists: 'exists', forall: 'forall' },
    multiCharFreevars: true,
    numbers: true,
    application: true,
    arrows: true,
    forwardRules: true,
    binaryNormalization: true,
  });
}

export { loadILL, buildForwardParser };
export default { loadILL, buildForwardParser };
