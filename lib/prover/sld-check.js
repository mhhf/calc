/**
 * SLD certificate checker (TODO_0295) — deterministic verification of a
 * backchain derivation against the program's declared clause set.
 *
 * A certificate is the backchainer's term tree (buildTerm mode):
 *   { rule: clauseName|defName, goal: groundHash, premises: [node] }
 * emitted CLAUSE-ONLY (useFFI: false — the FFI principle: FFI is the
 * uncertified fast path; certificates take the semantics path).
 *
 * The check is matching, never search: resolve the NAMED clause, slot-
 * match its head pattern against the recorded ground goal, thread the
 * bindings through the premise patterns matched against the child goals,
 * recurse. Matching uses the kernel's theory-aware matcher (matchIdx +
 * the Store-registered equational theories — already in the TCB as the
 * calculus's conversion layer), so i/o/e clause patterns match canonical
 * binlit goals. 'ffi' leaves are REJECTED — an uncertified shortcut has
 * no place in a certificate.
 *
 * Generic: no calculus imports; clauses/definitions are the caller's
 * declarative data (Map name → {hash, premises} / Map name → hash).
 */

'use strict';

import Store from '../kernel/store.js';
import { matchIndexed as matchIdx, undoSave, undoDiscard } from '../kernel/unify.js';
import { collectMetavars } from '../engine/pattern-utils.js';

function slotsFor(head, premises) {
  const mv = new Set();
  collectMetavars(head, mv);
  for (const p of premises || []) collectMetavars(p, mv);
  const slots = {};
  let i = 0;
  for (const m of mv) slots[m] = i++;
  return { slots, count: i };
}

/** Theory-aware ground equality: match with no free slots. */
function groundEq(a, b) {
  if (a === b) return true;
  const save = undoSave();
  const r = !!matchIdx(a, b, [], {});
  undoDiscard(save);
  return r;
}

/**
 * Check one certificate tree. Returns {} on success, { error } on the
 * first defect (path-annotated).
 *
 * Undo discipline: matchIdx logs every fresh slot binding on unify's
 * module-global undo stack. Bindings must PERSIST across the head match
 * and the premise matches of one node (that is the theta threading), so
 * the node saves once on entry and discards its whole span on every
 * exit — theta is node-local garbage, so undoDiscard (pointer reset, no
 * theta writeback) is exact. Without this the stack leaks per binding
 * and overflows at capacity (audit 2026-08-29, TODO_0296 P0).
 */
function checkSLD(node, clauses, definitions, path = 'root') {
  if (!node || typeof node.goal !== 'number') {
    return { error: `${path}: malformed certificate node` };
  }
  if (node.rule === 'ffi') {
    return { error: `${path}: uncertified ffi leaf (emit with useFFI: false)` };
  }

  const cl = clauses && clauses.get(node.rule);
  if (cl) {
    const prems = cl.premises || [];
    const kids = node.premises || [];
    if (kids.length !== prems.length) {
      return { error: `${path}: clause '${node.rule}' has ${prems.length} premise(s), certificate has ${kids.length}` };
    }
    const { slots, count } = slotsFor(cl.hash, prems);
    const theta = new Array(count).fill(undefined);
    const save = undoSave();
    if (!matchIdx(cl.hash, node.goal, theta, slots)) {
      undoDiscard(save);
      return { error: `${path}: goal is not an instance of clause '${node.rule}'` };
    }
    for (let i = 0; i < prems.length; i++) {
      if (typeof kids[i]?.goal !== 'number' ||
          !matchIdx(prems[i], kids[i].goal, theta, slots)) {
        undoDiscard(save);
        return { error: `${path}: premise ${i} of '${node.rule}' does not match its subderivation` };
      }
    }
    undoDiscard(save);
    for (let i = 0; i < kids.length; i++) {
      const r = checkSLD(kids[i], clauses, definitions, `${path}.${i}`);
      if (r.error) return r;
    }
    return {};
  }

  const dh = definitions && definitions.get(node.rule);
  if (dh !== undefined) {
    if ((node.premises || []).length !== 0) {
      return { error: `${path}: definition '${node.rule}' is a fact — no premises` };
    }
    const { slots, count } = slotsFor(dh, []);
    const theta = new Array(count).fill(undefined);
    const save = undoSave();
    const ok = matchIdx(dh, node.goal, theta, slots);
    undoDiscard(save);
    if (!ok) {
      return { error: `${path}: goal is not an instance of definition '${node.rule}'` };
    }
    return {};
  }

  return { error: `${path}: unknown clause or definition '${node.rule}'` };
}

/**
 * Check a certificate FOR a specific goal: the root must derive exactly
 * that goal (theory-aware equality), then the tree must check.
 */
function checkGoalCert(cert, goal, clauses, definitions) {
  if (!cert) return { error: 'missing certificate' };
  if (!groundEq(cert.goal, goal)) {
    return { error: 'certificate derives a different goal' };
  }
  return checkSLD(cert, clauses, definitions);
}

export { checkSLD, checkGoalCert, groundEq };
export default { checkSLD, checkGoalCert, groundEq };
