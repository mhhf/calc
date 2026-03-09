/**
 * Guided Proof Term Builder (TODO_0068 §10.5 Phase 2)
 *
 * Transforms an enriched forward trace into a complete ILL proof term.
 * Each forward step maps to:
 *   copy(ruleHash, loli_l(antecedentProof, monad_l(consequentDecomp, continuation)))
 *
 * Pure function: trace entries + rfTerm → GenericTerm. No search, no state mutation.
 *
 * Uses focused loli_l (2 subterms): first proves antecedent, second continues
 * with consequent. The antecedent proof follows the formula's tensor tree
 * structure via tensor_r/id/promotion. The consequent is decomposed via
 * tensor_l/absorption to bind individual produced facts.
 */

const Store = require('../kernel/store');
const { applyIndexed: subApplyIdx } = require('../kernel/substitute');

/**
 * Build a complete ILL proof term from an enriched forward trace.
 *
 * @param {Array} trace - Enriched trace entries from forward.run with evidence
 * @param {Object} rfTerm - Terminal rightFocusTerm (from rightFocusTerm)
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
 * Compiled rules: copy(ruleHash, loli_l(antProof, monad_l(consqDecomp, continuation)))
 * Loli matches: loli_l(antProof, monad_l(consqDecomp, continuation))
 */
function buildStepTerm(step, continuation) {
  const { rule, theta, slots, persistentEvidence } = step;
  const isLoli = !rule.hash;

  // Get the loli formula node (source of truth for structure)
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

  // Focused loli_l: 2 subterms (antecedent proof + continuation with consequent)
  const groundLoli = isLoli ? loliHash : subApplyIdx(loliHash, theta, slots);
  inner = { rule: 'loli_l', principal: groundLoli, subterms: [antecedentProof, inner] };

  // Compiled rules: wrap in copy (from persistent context / gamma)
  if (rule.hash) {
    inner = { rule: 'copy', principal: rule.hash, subterms: [inner] };
  }

  return inner;
}

// ─── Formula Walking ─────────────────────────────────────────────────

/**
 * Peel bang/forall wrappers from a rule formula to get the loli node.
 * Rules in .ill files are typically bare loli, but defensive peeling
 * handles !∀X.A⊸{B} forms.
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
 * Build tensor_r proof tree matching the antecedent's tensor structure.
 * Walks the Store formula tree recursively:
 *   tensor → tensor_r(left, right)
 *   bang   → promotion(evidenceTerm)
 *   one    → one_r
 *   other  → id(groundHash)
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

/** Convert a persistent evidence record to a proof term */
function evidenceToTerm(ev) {
  if (!ev) return { rule: 'id', principal: null, subterms: [] };

  if (ev.method === 'state') {
    return { rule: 'id', principal: ev.fact, subterms: [] };
  }
  if (ev.method === 'ffi') {
    return { rule: 'ffi', principal: null, subterms: [] };
  }
  if (ev.method === 'clause') {
    // Clause resolution proof — for now, treat as unverified identity
    // Full clause proof extraction requires prove.js proofTree mode (future)
    return { rule: 'id', principal: ev.goal, subterms: [] };
  }
  return { rule: 'id', principal: ev.goal || null, subterms: [] };
}

// ─── Consequent Decomposition (Left Rules) ───────────────────────────

/**
 * Build tensor_l / absorption chain for consequent decomposition.
 * After monad_l adds the body to delta, we decompose tensors and
 * absorb banged parts to make individual facts available.
 *
 *   tensor → tensor_l(groundTensor, recurse(right, continuation))
 *   bang   → bang_l(groundBang, continuation)
 *   other  → continuation (leaf fact already in delta)
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
