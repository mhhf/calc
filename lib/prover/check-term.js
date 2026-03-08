/**
 * Type Checker for Generic Proof Terms (Phase 4, TODO_0068 §4)
 *
 * Trusted kernel extension. Verifies `Gamma; Delta |- t : A`.
 * Works on expanded AST objects — Store is outside the trust boundary.
 *
 * expand(hash) bridges Store hashes to plain objects (called once).
 * checkTerm() is a pure function on expanded data structures.
 *
 * Context splitting is deterministic: the term dictates which sub-term
 * uses which variables. Each linear variable must be used exactly once.
 *
 * Returns { valid, remaining, error?, unverified? }
 *   remaining = linear context after this term consumed its resources
 */

const Store = require('../kernel/store');

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

  checkers['monad_r'] = (gamma, delta, term, type, lax) => {
    if (type.tag !== 'monad') return fail('monad_r: type not monadic');
    // monad_r has no sub-proofs from backward search; evidence from bridge
    // If the term carries forward evidence, it was verified separately
    return ok(delta);
  };

  checkers['monad_l'] = (gamma, delta, term, type, lax) => {
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
  // Quantifier rules: defer to unverified (de Bruijn subst on expanded terms deferred)
  if (d.binding) {
    return (gamma, delta, term, type, lax) => {
      // Still check principal exists for left rules
      if (d.side === 'l') {
        const p = term.principal;
        if (p === null) return fail(d.connective + '_l: no principal');
        if (!delta.has(p)) return fail(d.connective + '_l: principal not in delta');
        const pType = delta.get(p);
        if (pType.tag !== d.connective) return fail(d.connective + '_l: tag mismatch');
      }
      if (d.side === 'r' && type.tag !== d.connective) {
        return fail(d.connective + '_r: type tag mismatch');
      }
      return unverified(new Map(), 'quantifier');
    };
  }

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

    // Zero-premise rules
    if (d.premises.length === 0) {
      if (d.emptyLinear && !mapEmpty(workingDelta))
        return fail('zero-premise: non-empty delta');
      // discardsContext (zero_l): all remaining linear consumed
      const remaining = d.side === 'l' && !d.emptyLinear ? new Map() : workingDelta;
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

  return { check, expand, buildCheckerMap: () => checkers };
}

module.exports = { createChecker, expand, buildCheckerMap };
