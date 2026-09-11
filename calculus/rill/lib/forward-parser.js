/**
 * rill forward-engine expression parser + sequent loader.
 *
 * rill = fill + the ○ next-time modality (rill.calc @extends fill). This mirrors
 * fill's forward-parser (calculus/fill/lib/forward-parser.js): the same operator
 * derivation from the constructor table, plus ○ (which the @ascii "O _" template
 * auto-derives as a unary prefix operator — ○ is NOT a binder, so the binders
 * map is unchanged from fill's exists/forall/mu/nu). The backward calculus is the
 * LIST [ill.rules, fill.rules, rill.rules] — ILL's fragment and the four μ/ν
 * unfold rules inherited by reference, plus the single ○R rule.
 */

import path from 'path';
import calculusLoader from '../../../lib/calculus/index.js';
import { parserTables, parserFromTables } from '../../../lib/calculus/builders.js';

const RILL_DIR = path.join(import.meta.dirname, '..');
const FILL_DIR = path.join(import.meta.dirname, '../../fill');
const ILL_DIR = path.join(import.meta.dirname, '../../ill');

const RILL_CALC = path.join(RILL_DIR, 'rill.calc');
const ILL_RULES = path.join(ILL_DIR, 'ill.rules');
const FILL_RULES = path.join(FILL_DIR, 'fill.rules');
const RILL_RULES = path.join(RILL_DIR, 'rill.rules');

/** Load the rill backward calculus (rill.calc @extends fill +
 *  [ill.rules, fill.rules, rill.rules] → buildCalculus). */
function loadRill() {
  return calculusLoader.load(RILL_CALC, [ILL_RULES, FILL_RULES, RILL_RULES]);
}

/** Build the .ill-format expression parser for rill programs — fill's parser
 *  plus the ○ prefix operator (auto-derived from the constructor table). */
function buildForwardParser() {
  const rill = loadRill();
  const tables = parserTables(rill.constructors);
  // Formula-returning constructors only (exclude structural: comma, hyp, seq);
  // loli is re-added by forwardRules with special `-o { }` handling.
  tables.operators = tables.operators
    .filter(o => rill.constructors[o.name]?.returnType === 'formula' && o.name !== 'loli');
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

export { loadRill, buildForwardParser, RILL_CALC, ILL_RULES, FILL_RULES, RILL_RULES };
export default { loadRill, buildForwardParser };
