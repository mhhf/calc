// @ts-check
/**
 * Machinery-reserved predicate/constructor names of the decimation
 * surface — the SORT_PREDS pattern (one source of truth, exported so the
 * checker side speaks the same language). These are NOT per-calculus
 * config slots on purpose: 'drawn' is kernel-reserved by the convert
 * fence, and a renameable slot would let a calculus rename around the
 * reservation (audit 2026-09-02).
 *
 * Lives at engine root (RES_0143 L12): the loader's convert fence needs
 * only these NAMES — importing them used to pull all 840 lines of the
 * decimation driver into every load's module graph; and once the driver
 * moved to lib/measure/, the fence could not reach into an outer layer.
 */
const DECIMATE_PREDS = Object.freeze({
  SUPERPOSE: 'superpose',  // the suspended-wave constructor
  DRAWN: 'drawn',          // draw tokens (minted only at the checker boundary)
  BIAS: 'bias',            // the M8 machinery predicate (like SORT_PREDS)
  WITHIN: 'within',        // dynamic datasort conditioning (fence B)
});

// Machinery-reserved RULE names: synthesized by the untrusted prover and
// intercepted by the kernel BEFORE the rule-spec lookup, so a calculus rule of
// the same name would be silently swallowed (its body never verified). The
// loader rejects the collision loudly (TODO_0009 audit 2026-09-11).
//   nu_cycle — the cyclic-proof (coinductive) bud leaf: a back-edge closing to
//              an ancestor companion, certified by the GTC checker (gtc-check.js).
// NOT reserved: 'id'/'id_+'/'id_-' — calculi legitimately DECLARE the identity
// axiom; the kernel coordinates with the declared rule by name, it does not
// forbid it. Only purely-synthesized names (never declarable) belong here.
const RESERVED_RULE_NAMES = Object.freeze(new Set(['nu_cycle']));

export { DECIMATE_PREDS, RESERVED_RULE_NAMES };
export default { DECIMATE_PREDS, RESERVED_RULE_NAMES };
