/**
 * Type Checker for Generic Proof Terms — trusted kernel extension.
 *
 * Implements the de Bruijn criterion: the prover (untrusted, complex) produces
 * terms; the checker (trusted, small) validates them. If checkTerm returns valid,
 * then Gamma; Delta |- t : A is a valid ILL+lax derivation.
 *
 * Architecture:
 *   expand(hash) converts Store hashes → plain { tag, children, hash } trees (once).
 *   buildCheckerMap(calculus) generates one checker function per rule from descriptors.
 *   checkTerm() dispatches by term.rule → checker function (simple map lookup).
 *
 * Key design — remaining-threading:
 *   Each checkTerm call returns { valid, remaining } where remaining is the linear
 *   context AFTER this term consumed its resources. For context-splitting rules
 *   (tensor_r, loli_l), the first subterm's remaining becomes the second's input.
 *   For copyContext rules (with_r), each premise gets the full original delta.
 *   This makes linear resource tracking deterministic — no search needed.
 *
 * Trust boundary: this file + kernel.js + substitute.js (debruijnSubst).
 * Everything else (Store, forward engine, backward prover, FFI) is untrusted.
 *
 * Note on Store: expand() calls Store.isTerm/tag/arity/child, and debruijnSubst
 * operates on Store hashes. The "Store outside trust boundary" principle is
 * pragmatic (JS Store has complex hash-consing internals), not absolute. In a
 * Zig implementation, Store would be a trivial flat arena inside the trust boundary.
 */

const Store = require('../kernel/store');
const { debruijnSubst } = require('../kernel/substitute');

// ─── Expand ─────────────────────────────────────────────────────────

/**
 * Convert a Store hash to a plain object tree.
 * Called once at the boundary; the checker works on the result.
 *
 * @param {number} hash
 * @returns {{ tag: string, children: Object[], hash: number }|null}
 */
function expand(hash) {
  if (!Store.isTerm(hash)) return null;
  const tag = Store.tag(hash);
  const ar = Store.arity(hash);
  const children = [];
  for (let i = 0; i < ar; i++) children.push(expand(Store.child(hash, i)));
  return { tag, children, hash };
}

// ─── Helpers ────────────────────────────────────────────────────────

function ok(remaining) { return { valid: true, remaining }; }
function fail(error) { return { valid: false, error }; }
function unverified(remaining, reason) { return { valid: true, remaining, unverified: reason }; }

function mapDelete(m, key) {
  const n = new Map(m);
  n.delete(key);
  return n;
}

function mapEmpty(m) { return m.size === 0; }

// ─── Core Checker ───────────────────────────────────────────────────

/**
 * Check a generic proof term against a type in dual contexts.
 *
 * @param {Map<number, Object>} gamma  - Cartesian context (freely copyable)
 * @param {Map<number, Object>} delta  - Linear context (use exactly once)
 * @param {Object} term                - GenericTerm
 * @param {Object} type                - Expanded type
 * @param {boolean} lax                - Monotonic lax flag (monad)
 * @param {Object} checkers            - Rule → checker map
 * @returns {{ valid: boolean, remaining?: Map, error?: string, unverified?: string }}
 */
function checkTerm(gamma, delta, term, type, lax, checkers) {
  if (!term || !term.rule) return fail('null or missing term');
  const check = checkers[term.rule];
  if (!check) return fail('unknown rule: ' + term.rule);
  return check(gamma, delta, term, type, lax);
}

// ─── Checker Map Builder ────────────────────────────────────────────

/**
 * Build a checker map from calculus descriptors.
 * One entry per rule (+ spec-key aliases). Generated at load time.
 *
 * @param {Object} calculus
 * @returns {Object} checkers map
 */
function buildCheckerMap(calculus) {
  const checkers = {};

  // ── Special rules ──

  checkers['id'] = checkers['id_+'] = checkers['id_-'] = (gamma, delta, term, type) => {
    const p = term.principal;
    if (p === null) return fail('id: no principal');
    // Linear identity: consume from delta
    if (delta.has(p)) {
      const pType = delta.get(p);
      if (pType.hash !== type.hash) return fail('id: type mismatch');
      return ok(mapDelete(delta, p));
    }
    // Cartesian identity: delta unchanged (no linear consumption)
    if (gamma.has(p)) {
      const pType = gamma.get(p);
      if (pType.hash !== type.hash) return fail('id: type mismatch (cartesian)');
      return ok(delta);
    }
    return fail('id: principal not in context');
  };

  checkers['copy'] = (gamma, delta, term, type, lax) => {
    const p = term.principal;
    if (p === null) return fail('copy: no principal');
    if (!gamma.has(p)) return fail('copy: principal not in gamma');
    const pType = gamma.get(p);
    // Add a linear copy: use pType.hash as the new binding key
    const newDelta = new Map(delta);
    newDelta.set(pType.hash, pType);
    if (term.subterms.length !== 1) return fail('copy: expected 1 subterm');
    return checkTerm(gamma, newDelta, term.subterms[0], type, lax, checkers);
  };

  checkers['ffi'] = (_g, _d, _t, _ty) =>
    unverified(new Map(), 'ffiAxiom');

  checkers['unreachable'] = (_g, _d, _t, _ty) =>
    unverified(new Map(), 'constraintUNSAT');

  // ── Monad rules ──
  //
  // monad_r is the mode switch boundary — the point where backward meets forward.
  // Two behaviors depending on execution profile:
  //   'guided': term.evidence is a complete ILL proof term → recurse (full verification)
  //   'full':   term.evidence is opaque or null → trust bridge's rightFocus check

  checkers['monad_r'] = (gamma, delta, term, type, lax) => {
    if (type.tag !== 'monad') return fail('monad_r: type not monadic');
    // Guided mode: evidence is a full ILL proof term — recurse into it.
    // The lax flag becomes true: once inside the monad, the judgment is |-_lax
    // (Pfenning-Davies 2001). monad_l is only valid under |-_lax.
    if (term.evidence && term.evidence.rule) {
      const innerType = type.children[0];
      return checkTerm(gamma, delta, term.evidence, innerType, true, checkers);
    }
    // Full/opaque mode: bridge verified via rightFocus (residual state matches succedent)
    return ok(delta);
  };

  checkers['monad_l'] = (gamma, delta, term, type, lax) => {
    // Stickiness: monad_l only valid under |-_lax (Pfenning-Davies 2001).
    // The prover enforces this via requiresSuccedentTag:'monad' on the descriptor.
    // The checker independently verifies: once you enter the monad (via monad_r
    // setting lax=true), you stay — monad_l outside lax mode is a proof error.
    if (!lax) return fail('monad_l: not in lax mode (must be inside monad_r)');
    const p = term.principal;
    if (p === null) return fail('monad_l: no principal');
    if (!delta.has(p)) return fail('monad_l: principal not in delta');
    const pType = delta.get(p);
    if (pType.tag !== 'monad') return fail('monad_l: principal not monadic');
    // Remove principal, add inner type as new linear binding
    const inner = pType.children[0];
    const newDelta = mapDelete(delta, p);
    newDelta.set(inner.hash, inner);
    if (term.subterms.length !== 1) return fail('monad_l: expected 1 subterm');
    return checkTerm(gamma, newDelta, term.subterms[0], type, lax, checkers);
  };

  // ── Focused loli_l ──
  //
  // Two variants, dispatched by subterm count:
  //
  // 1-subterm (invertible, backward prover):
  //   Both A and B added to delta. The descriptor-generated checker would handle
  //   this, but we register loli_l explicitly to support both variants.
  //
  // 2-subterm (focused, guided execution):
  //   First subterm proves A (consuming resources from delta).
  //   Second subterm continues with B added to remaining delta.
  //   Sequential context split: remaining from first → input to second.
  //   This is the key innovation enabling guided proof term verification.
  //
  // Why a custom checker instead of the descriptor generator:
  //   The descriptor for loli_l has premises: [{linear:[0,1]}] — single premise
  //   with both A and B as linear bindings. This produces the 1-subterm checker.
  //   The 2-subterm variant can't be expressed in the descriptor language
  //   (it needs sequential context split between two premises on the same principal).
  checkers['loli_l'] = (gamma, delta, term, type, lax) => {
    const p = term.principal;
    if (p === null) return fail('loli_l: no principal');
    if (!delta.has(p)) return fail('loli_l: principal not in delta');
    const pType = delta.get(p);
    if (pType.tag !== 'loli') return fail('loli_l: tag mismatch');
    const workDelta = mapDelete(delta, p);
    const A = pType.children[0]; // antecedent type
    const B = pType.children[1]; // consequent type

    if (term.subterms.length === 2) {
      // Focused: first subterm proves A, second continues with B
      const r1 = checkTerm(gamma, workDelta, term.subterms[0], A, lax, checkers);
      if (!r1.valid) return r1;
      const newDelta = new Map(r1.remaining);
      newDelta.set(B.hash, B);
      return checkTerm(gamma, newDelta, term.subterms[1], type, lax, checkers);
    }

    // Invertible (1-subterm): add both A and B to delta
    if (term.subterms.length !== 1) return fail('loli_l: expected 1 or 2 subterms');
    const premDelta = new Map(workDelta);
    premDelta.set(A.hash, A);
    premDelta.set(B.hash, B);
    return checkTerm(gamma, premDelta, term.subterms[0], type, lax, checkers);
  };

  // ── Descriptor-generated rules ──

  for (const [name, rule] of Object.entries(calculus.rules)) {
    if (!rule.descriptor) continue;
    const d = rule.descriptor;
    const specKey = (d.connective && d.side) ? `${d.connective}_${d.side}` : name;

    // Skip rules we've already handled specially
    if (checkers[name]) continue;

    const checker = buildRuleChecker(d, checkers);
    checkers[name] = checker;
    if (specKey !== name && !checkers[specKey]) {
      checkers[specKey] = checker;
    }

    // Also register suffixed variants (with_l1, with_l2, oplus_r1, etc.)
    const match = name.match(/^(.+_[lr])(\d+)$/);
    if (match) {
      const base = match[1];
      if (!checkers[base]) checkers[base] = checker;
    }
  }

  return checkers;
}

/**
 * Generate a checker function from a descriptor.
 */
function buildRuleChecker(d, checkers) {
  return (gamma, delta, term, type, lax) => {
    let workingDelta = delta;
    let decomposed;

    // Left rules: consume principal, decompose its children
    if (d.side === 'l') {
      const p = term.principal;
      if (p === null) return fail('left rule: no principal');
      if (!workingDelta.has(p)) return fail('left rule: principal not in delta');
      const pType = workingDelta.get(p);
      if (pType.tag !== d.connective) return fail('left rule: tag mismatch');
      workingDelta = mapDelete(workingDelta, p);
      decomposed = pType.children;
    }

    // Right rules: type must match connective
    if (d.side === 'r') {
      if (type.tag !== d.connective) return fail('right rule: type tag mismatch');
      decomposed = type.children;
    }

    // Quantifier binding: open body with witness/eigenvariable.
    // Uses Store-level debruijnSubst (bridge to Store approach — pragmatic, tested,
    // avoids duplicating de Bruijn arithmetic on expanded ASTs).
    // Handles all four quantifier rules uniformly:
    //   exists_r(witness, u): decomposed[0] = A[witness/X], premise checks u : A[witness/X]
    //   forall_l(z, witness, u): decomposed[0] = A[witness/X], adds to delta
    //   exists_l(z, evar, u): decomposed[0] = A[evar/X], adds to delta
    //   forall_r(evar, u): decomposed[0] = A[evar/X], premise checks u : A[evar/X]
    // After substitution, the normal premise loop handles linear/succedent assignments.
    if (d.binding && decomposed && decomposed.length > 0) {
      const bodyHash = decomposed[0].hash;
      const replacement = d.binding === 'metavar' ? term.witness : term.eigenvariable;
      if (replacement == null) return fail(d.connective + ': missing ' + d.binding);
      decomposed = [expand(debruijnSubst(bodyHash, 0n, replacement))];
    }

    // Zero-premise rules (one_r, zero_l, etc.)
    if (d.premises.length === 0) {
      if (d.emptyLinear && !mapEmpty(workingDelta))
        return fail('zero-premise: non-empty delta');
      // discardsContext: zero-premise left rules WITHOUT emptyLinear (e.g., zero_l).
      // From falsehood (0) anything follows — all linear resources abandoned.
      // This is the type-theoretic "ex falso quodlibet" / abort.
      // Named const matches rule-interpreter.js:92 where discardsContext is computed.
      const discardsContext = d.side === 'l' && !d.emptyLinear;
      const remaining = discardsContext ? new Map() : workingDelta;
      return ok(remaining);
    }

    // Save delta before premises for copyContext rules
    const savedDelta = workingDelta;

    // Check each premise / subterm
    for (let i = 0; i < d.premises.length; i++) {
      const p = d.premises[i];
      const subterm = term.subterms[i];
      if (!subterm) return fail(`missing subterm ${i}`);

      // Build delta for this premise
      let premDelta;
      if (d.copyContext) {
        // with_r: each premise gets full original delta (context copied)
        premDelta = new Map(savedDelta);
      } else {
        // Context split or sequential: use working delta
        premDelta = workingDelta;
      }

      // Add linear bindings from decomposed children
      if (p.linear && decomposed) {
        premDelta = new Map(premDelta);
        for (const idx of p.linear) {
          if (idx < decomposed.length && decomposed[idx]) {
            premDelta.set(decomposed[idx].hash, decomposed[idx]);
          }
        }
      }

      // Add cartesian bindings (e.g., absorption: !A moves inner to gamma)
      let premGamma = gamma;
      if (p.cartesian && decomposed) {
        premGamma = new Map(gamma);
        for (const idx of p.cartesian) {
          if (idx < decomposed.length && decomposed[idx]) {
            premGamma.set(decomposed[idx].hash, decomposed[idx]);
          }
        }
      }

      // Empty linear requirement (promotion, one_r)
      if (d.emptyLinear && !mapEmpty(premDelta))
        return fail('premise requires empty delta');

      // Determine succedent type for this premise
      const premType = (p.succedent != null && decomposed && decomposed[p.succedent])
        ? decomposed[p.succedent]
        : type;

      const result = checkTerm(premGamma, premDelta, subterm, premType, lax, checkers);
      if (!result.valid) return result;

      // Update working delta with remaining (for sequential context split)
      workingDelta = result.remaining;
    }

    return ok(workingDelta);
  };
}

// ─── Public API ─────────────────────────────────────────────────────

/**
 * Create a term checker for a calculus.
 *
 * @param {Object} calculus
 * @returns {{ check: Function, expand: Function }}
 */
function createChecker(calculus) {
  const checkers = buildCheckerMap(calculus);

  /**
   * Check a proof term against a sequent.
   *
   * @param {Object} term       - GenericTerm (from extractTerm or buildMonadicTerm)
   * @param {Object} sequent    - The sequent (with contexts and succedent as Store hashes)
   * @returns {{ valid: boolean, error?: string, unverified?: string }}
   */
  function check(term, sequent) {
    const Seq = require('../kernel/sequent');
    const gamma = new Map();
    const delta = new Map();
    for (const h of Seq.getContext(sequent, 'cartesian'))
      gamma.set(h, expand(h));
    for (const h of Seq.getContext(sequent, 'linear'))
      delta.set(h, expand(h));
    const type = expand(sequent.succedent);
    if (!type) return fail('cannot expand succedent');

    const result = checkTerm(gamma, delta, term, type, false, checkers);
    if (!result.valid) return result;

    // Verify all linear resources consumed (unless unverified)
    if (!result.unverified && result.remaining && result.remaining.size > 0)
      return fail('leftover linear resources');

    return { valid: true, unverified: result.unverified || undefined };
  }

  return { check, expand };
}

module.exports = { createChecker, expand, buildCheckerMap };
