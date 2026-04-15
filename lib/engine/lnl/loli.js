/**
 * Dynamic rule matching for linear implications (loli facts).
 *
 * Layer: LNL (Linear-Non-Linear)
 *
 * Loli facts (A ⊸ {B}) are state-resident dynamic rules produced by
 * forward rule consequents. Firing one consumes the loli + trigger from
 * linear state and produces the body.
 *
 * The generic layer (strategy.js) owns iteration over dynamic rules;
 * this module owns match semantics: trigger decomposition, linear matching,
 * persistent proving, monad unwrap, and choice expansion.
 *
 * Resolved connectives (role → tag) are received via matchOpts.connectives,
 * set by forward.js/explore.js at run start. No ILL-specific imports.
 */

const Store = require('../../kernel/store');
const { predHead } = require('../../kernel/ast');
const { matchIndexed, undoSave, undoRestore, undoDiscard } = require('../../kernel/unify');
const { applyIndexed } = require('../../kernel/substitute');
const { flattenAnte, expandConsqChoices, collectMetavars } = require('../compile');

/**
 * Try to fire a loli(trigger, {body}) fact from linear state.
 *
 * @param {number} h - Loli fact hash
 * @param {Object} state - FactSet-based State object
 * @param {Object} calc - Calculus context (connectives, clauses, etc.)
 * @param {Object} matchOpts - Match options with provePersistent callback and connectives
 * @returns {Object|null} Match result compatible with applyMatch, or null
 */
function matchLoli(h, state, calc, matchOpts) {
  const trigger = Store.child(h, 0);
  const body = Store.child(h, 1);
  const rc = matchOpts?.connectives;
  const bodyInner = rc?.computation && Store.tag(body) === rc.computation
    ? Store.child(body, 0) : body;

  // Flatten trigger into linear + persistent components
  const { linear: linearTriggers, persistent: persistentTriggers } = flattenAnte(trigger, rc);

  // Build metavar slots for trigger + body
  const allVars = new Set();
  collectMetavars(trigger, allVars);
  collectMetavars(bodyInner, allVars);
  const slots = {};
  let slotIdx = 0;
  for (const v of allVars) slots[v] = slotIdx++;
  const theta = new Array(slotIdx);

  const topUndo = undoSave();
  const consumed = { [h]: 1 };

  // Phase 1: Match linear trigger patterns against state.linear
  for (let ti = 0; ti < linearTriggers.length; ti++) {
    const pattern = linearTriggers[ti];
    const pred = predHead(pattern);
    const trigTagId = pred ? Store.TAG[pred] : -1;
    let found = false;

    const candidates = trigTagId >= 0
      ? state.linear.group(trigTagId)
      : state.groupForPred(pred);

    for (let ci = 0; ci < candidates.length; ci++) {
      const fact = candidates[ci];
      if (fact === h) continue;
      const factTag = trigTagId >= 0 ? trigTagId : Store.tagId(fact);
      const factCount = state.linear.count(factTag, fact);
      if (factCount <= 0) continue;
      if (consumed[fact] && factCount - (consumed[fact] || 0) <= 0) continue;
      if (predHead(fact) !== pred) continue;

      const saved = undoSave();
      if (matchIndexed(pattern, fact, theta, slots)) {
        undoDiscard(saved);
        consumed[fact] = (consumed[fact] || 0) + 1;
        found = true;
        break;
      }
      undoRestore(theta, saved);
    }
    if (!found) {
      undoRestore(theta, topUndo);
      return null;
    }
  }

  // Phase 2: Prove persistent trigger patterns
  const wantEvidence = matchOpts && matchOpts.evidence;
  const evidenceOut = wantEvidence ? [] : null;
  if (persistentTriggers.length > 0) {
    // provePersistent comes from matchOpts (set by orchestrator via buildMatchOpts).
    // Lazy fallback for direct callers that bypass orchestrator.
    const proveFn = (matchOpts && matchOpts.provePersistent)
      || require('../opt/ffi').proveWithFFI;
    const proved = proveFn(
      persistentTriggers, 0, theta, slots, state, calc, evidenceOut, matchOpts
    );
    if (proved < persistentTriggers.length) {
      undoRestore(theta, topUndo);
      return null;
    }
  }

  // Instantiate body with matched bindings
  const instantiated = applyIndexed(bodyInner, theta, slots);
  undoDiscard(topUndo);

  // Expand choices in body (handles additive choice in loli body)
  const produced = flattenAnte(instantiated, rc);
  const consequentAlts = expandConsqChoices(produced, rc);
  const name = 'loli:' + (predHead(trigger) || 'trigger');

  const result = {
    rule: {
      name,
      consequent: produced,
      consequentAlts,
      preserved: null,
      compiledConseqLinear: null,
      compiledConseqPersistent: null,
    },
    theta: wantEvidence ? theta.slice(0, slotIdx) : [],
    slots: wantEvidence ? slots : {},
    consumed,
    optimized: false,
  };
  if (wantEvidence) {
    result.persistentEvidence = evidenceOut;
    result.loliHash = h;
  }
  return result;
}

module.exports = { matchLoli };
