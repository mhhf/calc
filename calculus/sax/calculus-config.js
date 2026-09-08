/**
 * sax Calculus Configuration — single assembly point (TODO_0309).
 *
 * The minimal instance over the SAX family: ILL's propositional
 * connective table (sax.calc) with the semi-axiomatic rule regime
 * (sax.rules) on the single-zone judgment Δ ⊢ C.
 *
 * Deliberately SMALL — the point of the second family is what it does
 * NOT need: no grades, no theories, no FFI, no sorts, no compose layer.
 * Every absent key exercises the engine's documented fallback; anything
 * that BREAKS on absence is a family-interface finding (recorded in
 * TODO_0309).
 *
 * Forward programs (.sax files) use the shared surface: `pred: type.`
 * declarations, `!fact` persistent facts (write-once cells), rules
 * `ante -o { conseq }`. The monad is ILL's trivial-grade shape so the
 * grade-unit thunk is the same binlit-0.
 */

'use strict';

import path from 'path';
import Store from '../../lib/kernel/store.js';
import { grade0 } from '../../lib/engine/grades.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import saxFamily from '../../family/sax/family-config.js';
import { makeCalcTables, makeForwardParserBuilder, makeSequentLoader } from '../kit.js';

const SAX_CALC = path.join(import.meta.dirname, 'sax.calc');
const SAX_RULES = path.join(import.meta.dirname, 'sax.rules');

const { connectives: saxConnectives } = makeCalcTables(SAX_CALC, { fences: {} });

// Trivial grade unit (binlit 0 — same canonical form as ILL's monadUnit,
// so `{A}` / `!p` sugar parses to the same hashes across calculi).
const saxGradeUnit = () => Store.put('binlit', [0]);

const saxBuildParser = makeForwardParserBuilder(SAX_CALC, saxGradeUnit);

const saxCalculusConfig = {
  // ── Structural family: SAX (single linear zone, null hooks) ──
  family: saxFamily,

  // ── L1: Structural ───────────────────────────────────────────
  get connectives() { return saxConnectives(); },
  typeCheck: 'strict',
  gradeUnit: saxGradeUnit,

  // ── L2: Compile ──────────────────────────────────────────────
  compile: {
    getModes: () => null,
    getModeMeta: () => null,
    discriminatorPreds: [],
    cacheEpoch: 'sax',
  },

  // ── Loader (convert.js) ──────────────────────────────────────
  loader: {
    buildParser: saxBuildParser,
    get connTags() { return connTagsFrom(saxConnectives()); },
    grade0,
    timed: false,
  },
};

/** Sequent-level sax calculus: single-zone contextStructure derived from
 *  the family declarations + the semi-axiomatic backward fragment. */
const loadSaxSequent = makeSequentLoader({
  calcFile: SAX_CALC, rulesFile: SAX_RULES,
  gradeUnit: saxGradeUnit, theory: null,
});

export { saxCalculusConfig, saxConnectives, loadSaxSequent };
export default saxCalculusConfig;
