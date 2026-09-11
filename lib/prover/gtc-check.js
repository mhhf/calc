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
 * The PROGRESS check (B) names the progressing connectives by ROLE (roles.lfp =
 * the μ tag, roles.gfp = the ν tag) and its rule names by convention
 * (`${lfp}_l` / `${gfp}_r`) — no ILL connective-name literal — so the soundness-
 * bearing check is calculus-generic. (The bud MARKER is a fixed synthetic
 * literal 'nu_cycle', shared with focused.js/kernel.js and reserved by the
 * loader; it is a protocol sentinel, not a connective name, and a calculus with
 * a differently-named ν gets conservative rejects, never an unsound accept.)
 * Imports are kernel-only (store + sequent); the theory canonicalizer is
 * supplied by the caller (a composed fixpoint fold, itself in the TCB), exactly
 * as forward-check.js takes it.
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

/**
 * Validate a whole cyclic proof TREE (TODO_0009 Inc-4). Trusted: it
 * reconstructs each back-edge FROM the (otherwise kernel-verified) tree — the
 * search only marks `nu_cycle` bud leaves; the cycle's rule sequence, its
 * companion, and the resource/progress facts are all read back from the tree
 * here, so a buggy or adversarial search cannot smuggle an unsound back-edge
 * past checkGTC.
 *
 * A `nu_cycle` leaf closes its branch by appeal to an ancestor COMPANION sequent
 * (the same sequent, by content-addressed hash). For each such leaf we find the
 * companion on the root→leaf path, take the node chain companion→…→bud-parent as
 * the cycle, read each node's rule and principal, and hand the records to
 * checkGTC. A leaf with no matching companion ancestor is an error.
 *
 * @param {Object} tree - a ProofTree (duck-typed: { conclusion, rule, premises })
 * @param {Object} opts - { roles, contextStructure, canonicalize } (as checkGTC)
 * @returns {{ valid, errors, backEdges }}
 */
function checkCyclicProof(tree, opts = {}) {
  const cs = opts.contextStructure || Seq.DEFAULT_CONTEXT_STRUCTURE;
  const roles = opts.roles || {};
  const lfpTag = roles.lfp ? Store.TAG[roles.lfp] : undefined;
  const gfpTag = roles.gfp ? Store.TAG[roles.gfp] : undefined;
  const errors = [];
  const backEdges = [];

  // The principal formula a node's rule acts on, for GTC purposes: a right rule
  // acts on the succedent; a left rule on the fixpoint formula in its pool.
  const principalOf = (node) => {
    const r = node.rule || '';
    if (r.endsWith('_r') || /_r\d+$/.test(r)) return node.conclusion.succedent;
    const pool = Seq.consumablePool(node.conclusion, cs);
    for (const h of pool) { const t = Store.tagId(h); if (t === lfpTag || t === gfpTag) return h; }
    return pool.length ? pool[0] : 0;
  };

  const walk = (node, path) => {
    if (!node) return;
    if (node.rule === 'nu_cycle') {
      const budHash = Seq.hash(node.conclusion);
      let compIdx = -1;
      for (let i = 0; i < path.length; i++) {
        if (Seq.hash(path[i].conclusion) === budHash) { compIdx = i; break; }
      }
      if (compIdx < 0) { errors.push('nu_cycle bud has no matching companion ancestor'); return; }
      const cycle = path.slice(compIdx);           // companion … bud-parent
      backEdges.push({
        bud: node.conclusion,
        companion: path[compIdx].conclusion,
        ruleNames: cycle.map(n => n.rule),
        principals: cycle.map(principalOf),
      });
      return;
    }
    const next = path.concat(node);
    for (const kid of node.premises || []) walk(kid, next);
  };
  walk(tree, []);

  if (errors.length) return { valid: false, errors, backEdges };
  if (backEdges.length === 0) return { valid: true, errors: [], backEdges };
  const r = checkGTC(backEdges, opts);
  return { valid: r.valid, errors: r.errors, backEdges };
}

export { checkGTC, checkCyclicProof };
export default { checkGTC, checkCyclicProof };
