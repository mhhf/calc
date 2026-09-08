/**
 * SAX family config — the second structural family (TODO_0309).
 *
 * The SAX family contributes:
 *
 *   1. `sax.family` (this directory) — the DECLARATIVE source: the
 *      single-zone linear sequent Δ ⊢ C (`@position_modes "linear
 *      linear"`) and its structural rules (exchange only).
 *      `buildCalculus` derives `contextStructure` from these — with
 *      `copySource: null`, the first family without a cartesian zone.
 *
 *   2. `engine` — the forward engine's family protocol slots. All four
 *      are null, and that is a FINDING, not an omission: SAX's
 *      operational reading (write-once cells as persistent facts,
 *      processes as linear facts) needs only the engine's generic
 *      baseline — state-lookup persistent proving, no dynamic rules,
 *      no existential resolution. The four slots are exactly the
 *      LNL-shaped part of the protocol (persistent CLAUSE resolution,
 *      loli continuations, existential witnesses); a family that needs
 *      none of them degrades to the documented fallbacks with zero
 *      special cases.
 *
 * Layer DAG: family/ imports lib/ (allowed), never calculus/.
 */

const saxFamily = Object.freeze({
  name: 'sax',
  engine: Object.freeze({
    proveNaive: null,
    matchDynamicRule: null,
    drainDynamicRules: null,
    resolveEx: null,
  }),
});

export { saxFamily };
export default saxFamily;
