/**
 * backchain-tree — wrap the backchainer to produce a proof-tree/v1 tree.
 *
 * The backchainer already has pluggable `buildClauseTerm` / `buildTypeTerm` /
 * `buildFFITerm` callbacks. Here we register builders that emit a tiny
 * intermediate record (rule, goal hash, premise records), then post-walk
 * the result to serialize formulas + compute content ids. Everything the
 * viewer needs, nothing it doesn't.
 *
 * This is the Phase C.1 entry point for `{proof ill backchain}` blocks —
 * used when the embedded source asks for a persistent/propositional goal
 * (e.g. `!plus (i e) (i e) R` after an `#import programs/bin.ill`). It
 * bypasses the focused prover entirely: the answer IS the SLD derivation.
 *
 * Goal framing: a backchain proof derives a proposition. We model each
 * node as `{ contexts: {}, succedent: <goal> }` — no linear / persistent
 * context on display, because the derivation is purely term-structured.
 */

'use strict';

const backward = require('../engine/backchain');
const serialize = require('./serialize-tree');

function buildClauseTerm(_groundPrems, premTerms, groundHead, clauseName) {
  return {
    rule: clauseName || 'clause',
    goal: groundHead,
    premises: premTerms || [],
  };
}

function buildTypeTerm(groundGoal, typeName) {
  return {
    rule: typeName || 'type',
    goal: groundGoal,
    premises: [],
  };
}

function buildFFITerm(goalHash) {
  return {
    rule: 'ffi',
    goal: goalHash,
    premises: [],
  };
}

function termToNode(term, ctx) {
  const premises = (term.premises || []).map((p) => termToNode(p, ctx));
  const goalRef = serialize.serializeFormula(term.goal, ctx);
  const sequent = { contexts: Object.create(null), succedent: goalRef };
  const premiseIds = premises.map((p) => p.id);
  const id = serialize.computeNodeId(term.rule, sequent, premiseIds);
  return { id, sequent, rule: term.rule, premises, proven: true };
}

/**
 * Run the backchainer on `atom` and return a serialized proof-tree/v1
 * object, or `{ success: false }` if no derivation was found.
 *
 * `opts` is forwarded to `backward.backchain` — callers pass the ILL
 * calc's `backwardOpts` here for theories / normalize / FFI. Our
 * builders are appended last so they override anything the caller
 * registered (the point of this module is the tree, not whatever
 * proof-term shape the underlying calculus uses for verification).
 *
 * @param {number} atom - Goal hash (a predicate term, not wrapped in `!`)
 * @param {Map} clauses
 * @param {Map} definitions
 * @param {Object} [opts]
 * @param {string} [opts.calculus='ill']
 * @param {string} [opts.profile='backchain']
 * @returns {{ success: boolean, tree?: object }}
 */
function backchainWithTree(atom, clauses, definitions, opts = {}) {
  const runOpts = {
    ...opts,
    buildTerm: true,
    buildClauseTerm,
    buildTypeTerm,
    buildFFITerm,
  };
  const result = backward.backchain(atom, clauses, definitions, runOpts);
  if (!result || !result.success || !result.term) {
    return { success: false };
  }

  const ctx = serialize._newContext({
    calculus: opts.calculus || 'ill',
    profile: opts.profile || 'backchain',
  });
  const root = termToNode(result.term, ctx);
  const tree = {
    format: serialize.FORMAT_VERSION,
    calculus: ctx.calculus,
    profile: ctx.profile,
    formulas: ctx.formulas,
    root,
  };
  return { success: true, tree };
}

module.exports = { backchainWithTree };
