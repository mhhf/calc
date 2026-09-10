/**
 * Global Trace Condition checker for cyclic μMALL proofs (TODO_0009 rung 3,
 * Inc-3) — a TRUSTED module (TCB), the cyclic-proof twin of the per-step
 * kernel (kernel.js) and the forward-tree checker (forward-check.js).
 *
 * A cyclic pre-proof closes some leaves (BUDS) back to an ancestor sequent
 * (its COMPANION) instead of an axiom. Such a back-edge is only SOUND under a
 * global condition. `checkGTC` verifies that condition for every back-edge; the
 * SEARCH that builds the cyclic proof (focused.js) is untrusted — soundness
 * rests here (the SAX explicit-cut discipline: untrusted search, trusted check).
 *
 * SOUNDNESS THEOREM (intuitionistic single-conclusion ILL μMALL; the focused-
 * discipline simplification of Baelde–Doumane–Saurin, CSL 2016). A back-edge
 * (bud B, companion C) is sound iff BOTH:
 *
 *  (A) CONTEXT CONSERVATION — the consumable (linear) pool of B equals that of C
 *      as a multiset MODULO THEORY (eq-theory canonicalization, never raw hash —
 *      the state-canonicity discipline), and the succedents agree modulo theory.
 *      Persistent (copy-source) formulas are unconstrained. Without this, a
 *      cycle could manufacture or destroy linear resources across the back-edge
 *      (e.g. {A,B} ⊢ νX.F  ⇝  consume A ⇝  {B} ⊢ νX.F  and loop — REJECTED).
 *
 *  (B) GTC PROGRESS — the rule sequence along the cycle (companion → bud) has at
 *      least one PROGRESSING step: a greatest-fixpoint RIGHT unfold (νR) on a
 *      ν-formula, or a least-fixpoint LEFT unfold (μL) on a μ-formula. Progress
 *      is where a coinductive layer is built (νR) or an inductive rank strictly
 *      descends (μL, Dershowitz–Manna). A cycle with no progressing step proves
 *      nothing (a bare structural loop; REJECTED); νL / μR are the WRONG side
 *      and never count (REJECTED).
 *
 * Under Andreoli focusing a back-edge closes against a structurally identical
 * companion, so the formula-thread relation is the identity along the cycle and
 * the GTC collapses to this O(cycle length) check — no Büchi automaton.
 *
 * CONSERVATIVE: it may reject a valid cyclic proof with unusual routing, but
 * never accepts an invalid one — a soundness checker's only permitted bias.
 *
 * The progressing connectives are named by ROLE (roles.lfp = the μ tag,
 * roles.gfp = the ν tag) — no ILL connective-name literal — so the checker is
 * calculus-generic. Imports are kernel-only (store + sequent); the theory
 * canonicalizer is supplied by the caller (a composed fixpoint fold, itself in
 * the TCB), exactly as forward-check.js takes it.
 */

import Store from '../kernel/store.js';
import Seq from '../kernel/sequent.js';

/** Canonicalize each hash and return a numerically-sorted multiset array. */
function canonMultiset(hashes, canon) {
  const out = new Array(hashes.length);
  for (let i = 0; i < hashes.length; i++) out[i] = canon(hashes[i]);
  out.sort((a, b) => a - b);
  return out;
}
function multisetEq(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}

/**
 * @param {Array} backEdges - one record per bud→companion back-edge:
 *   { bud: Seq, companion: Seq, ruleNames: string[], principals: number[] }
 *   ruleNames[i]/principals[i] are the rule applied and its principal-formula
 *   hash at step i of the cycle (companion → bud). bud/companion are Seq objects.
 * @param {Object} opts
 *   roles: calculus.roles — reads roles.lfp (μ tag name) / roles.gfp (ν tag name)
 *   contextStructure: calculus.contextStructure (consumable-zone layout)
 *   canonicalize: the composed theory canonicalizer (hash→hash); null ⇒ identity
 * @returns {{ valid: boolean, errors: string[] }}
 */
function checkGTC(backEdges, { roles, contextStructure, canonicalize } = {}) {
  const errors = [];
  const canon = canonicalize || ((h) => h);
  const cs = contextStructure || Seq.DEFAULT_CONTEXT_STRUCTURE;

  const lfp = roles && roles.lfp;              // μ tag name (least fixed point)
  const gfp = roles && roles.gfp;              // ν tag name (greatest fixed point)
  const lfpTag = lfp ? Store.TAG[lfp] : undefined;
  const gfpTag = gfp ? Store.TAG[gfp] : undefined;
  const muLRule = lfp ? `${lfp}_l` : null;     // μL — the progressing LEFT unfold
  const nuRRule = gfp ? `${gfp}_r` : null;     // νR — the progressing RIGHT unfold

  for (let idx = 0; idx < (backEdges || []).length; idx++) {
    const be = backEdges[idx];
    const where = `back-edge ${idx}`;
    if (!be || !be.bud || !be.companion) {
      errors.push(`${where}: missing bud or companion sequent`);
      continue;
    }

    // (A) context conservation — consumable pool multiset-equal modulo theory,
    // succedents equal modulo theory. Persistent zone is excluded by
    // consumablePool and stays unconstrained.
    const budPool = canonMultiset(Seq.consumablePool(be.bud, cs), canon);
    const compPool = canonMultiset(Seq.consumablePool(be.companion, cs), canon);
    if (!multisetEq(budPool, compPool)) {
      errors.push(`${where}: context conservation violated — consumable pool differs bud vs companion`);
    }
    if (canon(be.bud.succedent) !== canon(be.companion.succedent)) {
      errors.push(`${where}: context conservation violated — succedent differs bud vs companion`);
    }

    // (B) GTC progress — a νR-on-ν or μL-on-μ step somewhere on the cycle.
    // Both the rule name AND the principal's tag must match (defense in depth:
    // a forged record naming nu_r on a non-ν principal does not progress).
    const rules = be.ruleNames || [];
    const prins = be.principals || [];
    let progresses = false;
    for (let i = 0; i < rules.length; i++) {
      const r = rules[i], p = prins[i];
      if ((nuRRule && r === nuRRule && gfpTag !== undefined && Store.tagId(p) === gfpTag) ||
          (muLRule && r === muLRule && lfpTag !== undefined && Store.tagId(p) === lfpTag)) {
        progresses = true;
        break;
      }
    }
    if (!progresses) {
      errors.push(`${where}: no progressing thread — the cycle has no ${nuRRule || 'νR'}-on-ν ` +
        `or ${muLRule || 'μL'}-on-μ unfold step`);
    }
  }

  return { valid: errors.length === 0, errors };
}

export { checkGTC };
export default { checkGTC };
