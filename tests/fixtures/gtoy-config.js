/**
 * gtoy calculus config — TODO_0265 Phase 3 integration fixture.
 *
 * A minimal SECOND calculusConfig (graded monad, rational theory) built the
 * way till's will be (Phase 4): its own loader (parser + connTags), its own
 * theories (B6: the FORWARD engine can only cross-tag match ratlit ↔
 * rat(N,D) if setTheories includes ratlitTheory), its own cache epoch, and
 * roles derived from its own connective table (B7).
 */

import path from 'path';
import calculus from '../../lib/calculus/index.js';
import { buildParser } from '../../lib/calculus/builders.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import { setTheories } from '../../lib/kernel/unify.js';
import { defaultTheories } from '../../lib/kernel/eq-theory.js';
import { binlitTheory, installBinlitClassifier } from '../../lib/engine/ill/binlit-theory.js';
import { ratlitTheory, installRatlitTheory } from '../../lib/engine/theories/ratlit-theory.js';
import { grade0 } from '../../lib/engine/grades.js';

const FIXTURE = path.join(import.meta.dirname, 'graded-comp.calc');

const GTOY_CONNECTIVES = {
  tensor: { category: 'multiplicative', arity: 2, polarity: 'positive' },
  loli:   { category: 'multiplicative', arity: 2, polarity: 'negative' },
  bang:   { category: 'exponential',    arity: 2 },
  gmonad: { category: 'monad',          arity: 2, polarity: 'negative' },
};

const gtoyGradeUnit = () => putRat(0n, 1n);

const gtoyConfig = {
  // L0: kernel init — B6: the global unifier must know the rational theory
  // or forward matching silently never fires rat-headed rules.
  init() {
    setTheories([...defaultTheories, binlitTheory, ratlitTheory]);
    installBinlitClassifier();
    installRatlitTheory();
  },

  connectives: GTOY_CONNECTIVES,
  theories: [binlitTheory, ratlitTheory],

  compile: {
    discriminatorPreds: [],
    cacheEpoch: 'gtoy',
  },

  loader: {
    buildParser: () => buildParser(calculus.load(FIXTURE).constructors, {
      gradeUnit: gtoyGradeUnit,
      timedAnnotations: true,
      application: true,
      multiCharFreevars: true,
    }),
    connTags: {
      computation: { tag: 'gmonad', bodyIdx: 1, gradeIdx: 0 },
      implication: 'loli',
      product: 'tensor',
      exponential: 'bang',
      preserved: 'preserved',
    },
    grade0,
    timed: true,
  },

  gradeUnit: gtoyGradeUnit,
};

export { gtoyConfig, gtoyGradeUnit, GTOY_CONNECTIVES };
export default gtoyConfig;
