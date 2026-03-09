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
  const monadicPattern = Store.child(loliHash, 1);

  // Build antecedent proof: tensor_r tree of id(consumed) + promotion(evidence)
  const antecedentProof = buildAntecedentProof(
    antecedentPattern, theta, slots, persistentEvidence || []
  );

  // Build consequent decomposition: monad_l → tensor_l/absorption chain → continuation
  const monadBody = Store.child(monadicPattern, 0);
  const groundMonadic = isLoli ? monadicPattern : subApplyIdx(monadicPattern, theta, slots);

  let inner = buildConsequentDecomp(monadBody, theta, slots, continuation);
  inner = { rule: 'monad_l', principal: groundMonadic, subterms: [inner] };

  // Focused loli_l (2-subterm variant): first proves antecedent, second continues
  // with consequent. check-term.js dispatches on subterm count (2 = focused, 1 = invertible).
  // Sequential context split: remaining delta from antecedent flows to consequent.
  const groundLoli = isLoli ? loliHash : subApplyIdx(loliHash, theta, slots);
  inner = { rule: 'loli_l', principal: groundLoli, subterms: [antecedentProof, inner] };

  // Compiled rules: wrap in copy (contraction from persistent gamma).
  // This is the structural rule that duplicates a persistent clause for use.
  // Loli matches skip this — the loli fact is linear, consumed directly.
  if (rule.hash) {
    inner = { rule: 'copy', principal: rule.hash, subterms: [inner] };
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

// ─── Consequent Decomposition (Left Rules) ───────────────────────────

/**
 * Build the consequent decomposition (left rules) for a forward step's output.
 *
 * After monad_l unwraps the monadic body and adds it to delta, we need to
 * decompose the compound type into individual facts that subsequent steps
 * can consume. This mirrors what the backward prover does in inversion phase:
 *
 *   tensor → tensor_l(groundTensor, recurse(left, recurse(right, continuation)))
 *   bang   → bang_l(groundBang, continuation) — absorb !P, inner goes to gamma
 *   one    → one_l(groundOne, continuation) — discard unit
 *   atom   → continuation (leaf fact already in delta, no decomposition needed)
 *
 * The recursion follows tensor_l descriptor structure: left child first,
 * then right child, threading the continuation through.
 */
function buildConsequentDecomp(bodyPattern, theta, slots, continuation) {
  const tag = Store.tag(bodyPattern);

  if (tag === 'tensor') {
    const groundBody = subApplyIdx(bodyPattern, theta, slots);
    // tensor_l decomposes: both children added to delta.
    // Recurse into left first (matching tensor_l descriptor: linear:[0,1])
    // then right, threading the continuation.
    const leftDecomp = buildConsequentDecomp(Store.child(bodyPattern, 0), theta, slots,
      buildConsequentDecomp(Store.child(bodyPattern, 1), theta, slots, continuation));
    return {
      rule: 'tensor_l',
      principal: groundBody,
      subterms: [leftDecomp]
    };
  }

  if (tag === 'bang') {
    // absorption: !P → P in delta + gamma
    const groundBang = subApplyIdx(bodyPattern, theta, slots);
    return {
      rule: 'bang_l',
      principal: groundBang,
      subterms: [continuation]
    };
  }

  if (tag === 'one') {
    const groundOne = subApplyIdx(bodyPattern, theta, slots);
    return {
      rule: 'one_l',
      principal: groundOne,
      subterms: [continuation]
    };
  }

  // Leaf (atom/predicate): already in delta, no decomposition needed
  return continuation;
}

module.exports = { buildGuidedTerm, getLoliFromRule };
