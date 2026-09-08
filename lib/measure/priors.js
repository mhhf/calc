/**
 * Constructor priors — `name: sort @w Q.` (TODO_0292 D5/M6, will P1).
 *
 * Generic machinery, presence-gated: a program without @w annotations has
 * no priors (absent, not disabled), and no sort name or weight appears in
 * engine JS. Priors are DATA (D5): they enter the logic only through
 * collapse — the decimation driver (P2) and the ∃_ρ existential (P3) —
 * never as facts; the in-logic evidence surface is bias facts (M8).
 * Weights are unnormalized ratios in ℚ≥0 (M6): renormalization over the
 * live domain happens at collapse, an unannotated member weighs 1, and 0
 * is legal (dead unless nothing else remains).
 *
 * This module validates the parsed table against the sort system and
 * computes the Chi–Geman subcriticality advisory (THY_0026 T2): per
 * classifier, m = Σ_c share(c)·arity_rec(c) ≤ 1 ⟺ the branching process
 * of lazy collapse is (sub)critical ⟺ generation terminates almost
 * surely. At rung 1 classifier members are atomic (arity 0, m = 0); the
 * check arms itself the day datasort members with recursive arguments
 * land (P3). Advisory at load (M7) — the decimation driver, not the
 * loader, hard-errors on supercritical priors without a depth bound.
 */

'use strict';

import { _parseSignature } from '../engine/type-check.js';

/**
 * Validate a priors table and compute per-classifier subcriticality.
 * @param {Map<string,[bigint,bigint]>} priorsTable  member → weight [n,d]
 * @param {Object|null} sortSystem  buildSortSystem result (null = sortless)
 * @param {Map<string,number>} definitions  name → signature hash
 * @returns {{errors: string[], advice: Array}}
 */
function checkPriors(priorsTable, sortSystem, definitions) {
  const errors = [];
  const advice = [];
  if (!priorsTable || priorsTable.size === 0) return { errors, advice };
  if (!sortSystem) {
    errors.push(`@w priors need the sorts machinery — import your calculus's sorts prelude (priors annotate classifier members)`);
    return { errors, advice };
  }
  const touched = new Set();
  for (const [name] of priorsTable) {
    const s = sortSystem.leastSortOfName(name);
    if (!s || !sortSystem.isClassifier(s)) {
      errors.push(`'${name}': @w prior on a non-member — priors annotate members of a classifier sort ('${name}: <sort> @w Q.')`);
      continue;
    }
    touched.add(s);
  }

  // Chi–Geman (T2) per touched classifier, over ALL its members (default
  // weight 1). Floats suffice: the check is an advisory threshold, never
  // a semantic input.
  for (const s of touched) {
    let total = 0;
    let msum = 0;
    for (const member of sortSystem.membersOf(s)) {
      const w = priorsTable.get(member) || [1n, 1n];
      const wf = Number(w[0]) / Number(w[1]);
      total += wf;
      const sigHash = definitions.get(member);
      const sig = sigHash !== undefined ? _parseSignature(sigHash) : null;
      const rec = sig
        ? sig.argSorts.filter((a) => a === s || sortSystem.subsort(a, s)).length
        : 0;
      msum += wf * rec;
    }
    const m = total > 0 ? msum / total : 0;
    if (m > 1) {
      advice.push({ kind: 'supercritical-prior', sort: s, m });
    }
  }
  return { errors, advice };
}

export { checkPriors };
export default { checkPriors };
