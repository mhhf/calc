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
 */

const Store = require('../../kernel/store');
const { getPredicateHead } = require('../../kernel/ast');
const { matchIndexed, undoSave, undoRestore, undoDiscard } = require('../../kernel/unify');
const { applyIndexed } = require('../../kernel/substitute');
const { flattenTensor, expandConsequentChoices, collectMetavars } = require('../compile');

/**
 * Try to fire a loli(trigger, {body}) fact from linear state.
 *
 * @param {number} h - Loli fact hash
 * @param {Object} state - FactSet-based State object
 * @param {Object} calc - Calculus context (roles, clauses, etc.)
 * @param {Object} matchOpts - Match options with provePersistent callback
 * @returns {Object|null} Match result compatible with applyMatch, or null
 */
function matchLoli(h, state, calc, matchOpts) {
  const trigger = Store.child(h, 0);
  const body = Store.child(h, 1);
  const compTag = calc?.roles?.computation || 'monad';
  const bodyInner = Store.tag(body) === compTag ? Store.child(body, 0) : body;

  // Flatten trigger into linear + persistent components
  const { linear: linearTriggers, persistent: persistentTriggers } = flattenTensor(trigger);

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
    const pred = getPredicateHead(pattern);
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
      if (getPredicateHead(fact) !== pred) continue;

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
    const proveFn = (matchOpts && matchOpts.provePersistent)
      || require('../opt/ffi').provePersistentWithFFI;
    const proved = proveFn(
      persistentTriggers, 0, theta, slots, state, calc, evidenceOut
    );
    if (proved < persistentTriggers.length) {
      undoRestore(theta, topUndo);
      return null;
    }
  }

  // Instantiate body with matched bindings
  const instantiated = applyIndexed(bodyInner, theta, slots);
  undoDiscard(topUndo);

  // Expand choices in body (handles oplus/with in loli body)
  const produced = flattenTensor(instantiated);
  const consequentAlts = expandConsequentChoices(produced);
  const name = 'loli:' + (getPredicateHead(trigger) || 'trigger');

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
