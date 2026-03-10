/**
 * Guided Proof Term Builder — forward trace → complete ILL proof term.
 *
 * Core insight: the forward engine IS the backward prover, minus search.
 * Every forward step is an ILL derivation — this module makes it explicit:
 *
 *   1. copy(ruleHash)           — from persistent gamma (the .ill program rule)
 *   2. loli_l(groundLoli,       — consume antecedent, produce monadic result
 *        antecedentProof,       — tensor_r tree of id(consumed) + promotion(evidence)
 *        monad_l(result,        — unwrap monadic body
 *          consequentDecomp     — tensor_l/bang_l chain binding produced facts
 *            (continuation)))   — next step or terminal rfTerm
 *
 * Pure function: trace entries + rfTerm → GenericTerm. No search, no state mutation.
 * All ILL constructors used here (copy, loli_l, tensor_r, id, promotion, monad_l,
 * tensor_l, bang_l, one_l, one_r) are already in check-term.js — no new
 * constructors needed.
 *
 * Focused loli_l (2 subterms): the key type-checking innovation. The invertible
 * 1-premise loli_l (from descriptor) adds both antecedent and consequent to delta,
 * which doesn't work for forward steps (antecedent resources must be consumed
 * separately). The focused 2-premise variant splits the context: first subterm
 * consumes antecedent, second subterm gets remaining delta + consequent.
 * check-term.js handles both variants via subterm count dispatch.
 *
 * Loli matches (linear -o facts, not program rules): same structure minus
 * the copy wrapper. Detected via absence of rule.hash — synthetic rules
 * from matchLoli have no hash since they aren't persistent clauses in gamma.
 */

const Store = require('../kernel/store');
const { applyIndexed: subApplyIdx } = require('../kernel/substitute');

/**
 * Build a complete ILL proof term from an enriched forward trace.
 *
 * Folds right-to-left: the last step wraps rfTerm, each earlier step
 * wraps the accumulated continuation. This produces nested let-bindings
 * matching CLF's monadic expression grammar:
 *   let {p₁} = r₁(...) in let {p₂} = r₂(...) in ... rfTerm
 *
 * @param {Array} trace - Enriched trace entries from forward.run with evidence:
 *   { rule, theta, slots, persistentEvidence, loliHash? }
 * @param {Object} rfTerm - Terminal rightFocusTerm (succedent decomposition)
 * @returns {Object} GenericTerm — complete ILL proof term
 */
function buildGuidedTerm(trace, rfTerm) {
  let term = rfTerm;
  for (let i = trace.length - 1; i >= 0; i--) {
    term = buildStepTerm(trace[i], term);
  }
  return term;
}

/**
 * Build the proof term for a single forward step.
 *
 * The forward engine tells us WHAT happened (which rule fired, what was consumed).
 * This function reconstructs HOW it's justified in ILL by walking the rule's
 * formula structure in Store.
 *
 * Compiled rules (from .ill files, persistent clauses in gamma):
 *   copy(ruleHash, loli_l(antProof, monad_l(consqDecomp, continuation)))
 *
 * Loli matches (linear -o facts in state, not persistent):
 *   loli_l(antProof, monad_l(consqDecomp, continuation))
 *   No copy wrapper because the loli is consumed from delta, not copied from gamma.
 */
function buildStepTerm(step, continuation) {
  const { rule, theta, slots, persistentEvidence } = step;
  const isLoli = !rule.hash; // Synthetic loli rules have no hash

  // The Store formula of the rule is the source of truth for antecedent/consequent
  // structure. getLoliFromRule peels bang/forall wrappers to find the loli node.
  const loliHash = isLoli ? step.loliHash : getLoliFromRule(rule.hash);
  if (!loliHash) {
    // Fallback: opaque step (shouldn't happen with well-formed traces)
    return { rule: rule.name || 'unknown', principal: null, subterms: [continuation] };
  }

  const antecedentPattern = Store.child(loliHash, 0);

  // Build antecedent proof: tensor_r tree of id(consumed) + promotion(evidence)
  const antecedentProof = buildAntecedentProof(
    antecedentPattern, theta, slots, persistentEvidence || []
  );

  // Build consequent decomposition from compiled linear facts.
  // Cannot use the original formula body because existentially-bound variables
  // (de Bruijn `bound(N)`) are not substituted by subApplyIdx. The compiled rule
  // resolves exists variables during matching, so compiled patterns have `freevar`
  // slots that subApplyIdx handles correctly.
  const groundLinear = (rule.consequent.linear || []).map(p => subApplyIdx(p, theta, slots));
  const groundMonadBody = buildRightTensor(groundLinear);
  const groundMonadic = Store.put('monad', [groundMonadBody]);

  let inner;
  if (isLoli) {
    // Loli matches: the loli body may contain freevars (e.g., sha3's _Bytes)
    // that the loli match resolves. The Store structure of the loli retains
    // these freevars, so monad_l/tensor_l decomposition gives different hashes
    // than what the forward engine produces (via subApplyIdx on compiled linear).
    // Encode as an opaque loli_match step: the witness generator directly adjusts
    // delta using the ground facts rather than following Store.child decomposition.
    const groundAntecedent = subApplyIdx(antecedentPattern, theta, slots);
    inner = {
      rule: 'loli_match',
      principal: step.loliHash,
      groundAntecedent,
      groundFacts: groundLinear,
      subterms: [antecedentProof, continuation]
    };
  } else {
    // Compiled rules: construct ground loli from antecedent + synthetic monad.
    const groundAntecedent = subApplyIdx(antecedentPattern, theta, slots);
    const groundLoli = Store.put('loli', [groundAntecedent, groundMonadic]);

    let inner2 = buildConsequentDecompFromFacts(groundLinear, continuation);
    inner2 = { rule: 'monad_l', principal: groundMonadic, subterms: [inner2] };
    inner2 = { rule: 'loli_l', principal: groundLoli, subterms: [antecedentProof, inner2] };

    // Wrap in copy (contraction from persistent gamma).
    // Principal is the ground loli (not rule.hash) — the ZK witness generator
    // tracks copy.principal in the live delta, and loli_l removes it.
    inner = { rule: 'copy', principal: groundLoli, subterms: [inner2] };
  }

  return inner;
}

// ─── Formula Walking ─────────────────────────────────────────────────

/**
 * Peel bang/forall wrappers from a rule formula to get the loli node.
 *
 * Program rules in .ill files are stored as: !∀X₁.∀X₂...∀Xₙ.(A ⊸ {B})
 * The outermost bang makes them persistent (in gamma). Universals bind
 * metavars instantiated at match time. The loli is the actual rule body.
 *
 * Most rules are bare loli after compilation (bang/forall peeled by compile.js),
 * but rule.hash preserves the original formula structure. Bounded loop for safety.
 */
function getLoliFromRule(hash) {
  let h = hash;
  for (let i = 0; i < 20; i++) { // bounded loop for safety
    const t = Store.tag(h);
    if (t === 'loli') return h;
    if (t === 'bang' || t === 'forall') { h = Store.child(h, 0); continue; }
    return null; // unexpected structure
  }
  return null;
}

// ─── Antecedent Proof (Right Rules) ──────────────────────────────────

/**
 * Build the antecedent proof (right rules) by walking the formula's tensor spine.
 *
 * The antecedent of A ⊸ {B} is A, which is a tensor tree of linear facts
 * and persistent (!-wrapped) goals. Each node maps to a right rule:
 *   tensor → tensor_r(left, right)   — multiplicative conjunction introduction
 *   bang   → promotion(evidenceTerm) — the persistent goal was proved somehow
 *   one    → one_r()                 — unit, no resources consumed
 *   atom   → id(groundHash)          — identity: consume this fact from delta
 *
 * The evidence parameter carries per-persistent-goal proof records from
 * provePersistentGoals, used to fill the promotion() subterms.
 */
function buildAntecedentProof(patternHash, theta, slots, evidence) {
  const tag = Store.tag(patternHash);

  if (tag === 'tensor') {
    const left = buildAntecedentProof(Store.child(patternHash, 0), theta, slots, evidence);
    const right = buildAntecedentProof(Store.child(patternHash, 1), theta, slots, evidence);
    return { rule: 'tensor_r', principal: null, subterms: [left, right] };
  }

  if (tag === 'bang') {
    const inner = Store.child(patternHash, 0);
    const groundInner = subApplyIdx(inner, theta, slots);
    const ev = findEvidence(groundInner, evidence);
    return {
      rule: 'promotion', principal: null,
      subterms: [evidenceToTerm(ev)]
    };
  }

  if (tag === 'one') {
    return { rule: 'one_r', principal: null, subterms: [] };
  }

  // Linear atom/predicate — consumed from delta via identity
  const groundHash = subApplyIdx(patternHash, theta, slots);
  return { rule: 'id', principal: groundHash, subterms: [] };
}

/** Find evidence entry matching a ground persistent goal */
function findEvidence(groundGoal, evidence) {
  for (let i = 0; i < evidence.length; i++) {
    if (evidence[i].goal === groundGoal) return evidence[i];
  }
  return evidence.length > 0 ? evidence[0] : null;
}

/**
 * Convert a persistent evidence record to a proof term.
 *
 * Three resolution methods, matching provePersistentGoals' three levels:
 *   'state' → id(fact) — the fact already exists in persistent state
 *   'ffi'   → ffi()    — computed by FFI (checker returns unverified:'ffiAxiom')
 *   'clause' → id(goal) — proved by backward clause resolution
 *     NOTE: Full clause proof tree extraction from prove.js is deferred.
 *     Currently uses id(goal) fallback. ~30 LOC when prove.js gets proofTree mode.
 */
function evidenceToTerm(ev) {
  if (!ev) return { rule: 'id', principal: null, subterms: [] };

  if (ev.method === 'state') {
    return { rule: 'id', principal: ev.fact, subterms: [] };
  }
  if (ev.method === 'ffi') {
    return { rule: 'ffi', principal: null, subterms: [] };
  }
  if (ev.method === 'clause') {
    return { rule: 'id', principal: ev.goal, subterms: [] };
  }
  return { rule: 'id', principal: ev.goal || null, subterms: [] };
}

// ─── Compiled-Array Consequent Decomposition ──────────────────────────

/**
 * Build a right-associated tensor tree from ground fact hashes.
 * [f1, f2, f3] → tensor(f1, tensor(f2, f3))
 * [f1] → f1
 * [] → one
 */
function buildRightTensor(hashes) {
  if (hashes.length === 0) return Store.put('one', []);
  if (hashes.length === 1) return hashes[0];
  let acc = hashes[hashes.length - 1];
  for (let i = hashes.length - 2; i >= 0; i--) {
    acc = Store.put('tensor', [hashes[i], acc]);
  }
  return acc;
}

/**
 * Build consequent decomposition from ground linear facts (compiled array).
 *
 * Generates a right-associated tensor_l chain matching the tensor tree
 * built by buildRightTensor. Each tensor_l peels off the leftmost fact,
 * leaving it in delta for subsequent steps to consume.
 */
function buildConsequentDecompFromFacts(groundFacts, continuation) {
  if (groundFacts.length <= 1) return continuation;
  // Right-associated: tensor_l(f0 * rest, tensor_l(f1 * rest', ...))
  // Each tensor_l principal is the tensor of remaining facts from this point
  let inner = continuation;
  for (let i = groundFacts.length - 2; i >= 0; i--) {
    const remaining = groundFacts.slice(i);
    const tensorHash = buildRightTensor(remaining);
    inner = { rule: 'tensor_l', principal: tensorHash, subterms: [inner] };
  }
  return inner;
}

module.exports = { buildGuidedTerm, getLoliFromRule };
