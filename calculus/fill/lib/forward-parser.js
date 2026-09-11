/**
 * fill forward-engine expression parser + sequent loader.
 *
 * fill = ILL + μ/ν fixed points (fill.calc @extends ill). This mirrors ILL's
 * forward-parser (calculus/ill/lib/forward-parser.js): the same operator
 * derivation from the constructor table, plus the μ/ν binders. The backward
 * calculus is the LIST [ill.rules, fill.rules] — ILL's fragment inherited by
 * reference, the four fixpoint unfold rules added.
 */

import path from 'path';
import calculusLoader from '../../../lib/calculus/index.js';
import { parserTables, parserFromTables } from '../../../lib/calculus/builders.js';

const FILL_DIR = path.join(import.meta.dirname, '..');
const ILL_DIR = path.join(import.meta.dirname, '../../ill');

const FILL_CALC = path.join(FILL_DIR, 'fill.calc');
const ILL_RULES = path.join(ILL_DIR, 'ill.rules');
const FILL_RULES = path.join(FILL_DIR, 'fill.rules');

/** Load the fill backward calculus (fill.calc @extends ill + [ill.rules,
 *  fill.rules] → buildCalculus). */
function loadFill() {
  return calculusLoader.load(FILL_CALC, [ILL_RULES, FILL_RULES]);
}

/** Build the .ill-format expression parser for fill programs — ILL's parser
 *  plus the μ/ν binders. */
function buildForwardParser() {
  const fill = loadFill();
  const tables = parserTables(fill.constructors);
  // Formula-returning constructors only (exclude structural: comma, hyp,
  // seq); loli is re-added by forwardRules with special `-o { }` handling.
  tables.operators = tables.operators
    .filter(o => fill.constructors[o.name]?.returnType === 'formula' && o.name !== 'loli');
  tables.operators.push({ name: 'concat', op: '++', precedence: 55, assoc: 'left' });
  return parserFromTables({
    ...tables,
    binders: { exists: 'exists', forall: 'forall', mu: 'mu', nu: 'nu' },
    multiCharFreevars: true,
    numbers: true,
    application: true,
    arrows: true,
    forwardRules: true,
    binaryNormalization: true,
  });
}

export { loadFill, buildForwardParser, FILL_CALC, ILL_RULES, FILL_RULES };
export default { loadFill, buildForwardParser };
