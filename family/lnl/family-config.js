/**
 * LNL family config — the composable structural-family layer piece (TODO_0086).
 *
 * The Linear/Non-Linear family contributes two things:
 *
 *   1. `lnl.family` (this directory) — the DECLARATIVE source: base types,
 *      the two-zone sequent constructor (`@position_modes`), and the
 *      structural rules (`@structural exchange/contraction/weakening`,
 *      `@position`). `buildCalculus` derives `contextStructure` from these
 *      declarations; a calculus opts in via `@extends lnl` in its .calc.
 *
 *   2. `engine` — the EXECUTABLE bindings: the forward engine's family
 *      protocol implementations (persistent goal proving, dynamic-rule
 *      matching, persistent-trigger drain, existential resolution). The
 *      composition root (`lib/engine/index.js`) reads them off
 *      `cc.family.engine`; a calculus config composes this record by
 *      reference (M2 pattern), same as `cc.backward`/`cc.ffi`.
 *
 * Layer DAG: family/ imports lib/ (allowed), never calculus/. The generic
 * engine holds no default — absent `cc.family`, the engine degrades to
 * state-lookup-only persistent proving and null dynamic-rule slots
 * (the protocol factories' documented fallbacks).
 */

import { proveNaive } from './lib/persistent.js';
import { matchLoli } from './lib/loli.js';
import { drainLolis } from './lib/loli-drain.js';
import { resolveEx } from './lib/existential.js';

const lnlFamily = Object.freeze({
  name: 'lnl',
  engine: Object.freeze({
    proveNaive,
    matchDynamicRule: matchLoli,
    drainDynamicRules: drainLolis,
    resolveEx,
  }),
});

export { lnlFamily };
export default lnlFamily;
