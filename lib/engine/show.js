/**
 * Pretty-print content-addressed hashes for debugging.
 *
 * Usage:
 *   const { show } = require('./show');
 *   console.log(show(hash));              // "pc(0x3b)"
 *   console.log(showState(state));        // grouped by predicate
 */

import Store from '../kernel/store.js';
import { grade0 } from './grades.js';
import { predHead } from '../kernel/ast.js';

/**
 * Default render configuration — the ILL instance (TODO_0265 Phase 2b).
 * A calculus with different connective tags / grade atoms passes its own
 * record (from calculusConfig) as the `render` parameter; the default keeps
 * `show(h)` working standalone as a debug tool.
 */
const DEFAULT_RENDER = {
  implication: 'loli', exponential: 'bang', product: 'tensor',
  unit: 'one', additiveZero: 'zero', grade0,
};

/**
 * Default leaf policy — the EVM/ILL instance. `terminals` maps atom names to
 * classifications; `runningPred` marks a live control point. till supplies
 * its own via calculusConfig.domain (Phase 4).
 */
const DEFAULT_LEAF_POLICY = {
  terminals: { stop: 'STOP', revert: 'REVERT', invalid: 'INVALID' },
  runningPred: 'pc',
};

/** Default showInteresting exclusions — the EVM instance. */
const DEFAULT_SHOW_EXCLUDE = ['bytecode', 'calldata'];

/**
 * Pretty-print a single content-addressed hash.
 * @param {number} h
 * @param {Map<string, (string|null)[]>} [argNamesTable] - optional arg names for display
 * @param {Object} [render] - connective render config (default: ILL)
 * @returns {string}
 */
/** Stamp/grade positions read as decimals (`wood@3`, not `wood@0x3`). */
function _showStamp(h, argNamesTable, render) {
  const n = Store.get(h);
  if (n && n.tag === 'binlit') return n.children[0].toString();
  return show(h, argNamesTable, render);
}

function show(h, argNamesTable, render = DEFAULT_RENDER) {
  const n = Store.get(h);
  if (!n) return String(h);
  if (n.tag === 'atom') return n.children[0];
  if (n.tag === 'binlit') return '0x' + n.children[0].toString(16);
  // Timed forms (TODO_0265 Phase 3) — exact rationals, never a float
  if (n.tag === 'ratlit') return n.children[0].toString() + '/' + n.children[1].toString();
  if (n.tag === 'at') return show(n.children[0], argNamesTable, render) + '@' + _showStamp(n.children[1], argNamesTable, render);
  if (n.tag === 'after' || n.tag === 'before') {
    return n.tag + ' ' + _showStamp(n.children[0], argNamesTable, render);
  }
  if (n.tag === 'readPreserved') return 'read ' + show(n.children[0], argNamesTable, render);
  if (n.tag === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (!elems) return 'arrlit(?)';
    if (elems.length <= 5) return '[' + Array.from(elems).map(e => show(e, argNamesTable, render)).join(', ') + ']';
    return '[' + Array.from(elems.subarray(0, 5)).map(e => show(e, argNamesTable, render)).join(', ') + ', ...' + elems.length + ']';
  }
  if (n.tag === 'acons') return '[' + show(n.children[0], argNamesTable, render) + ' | ' + show(n.children[1], argNamesTable, render) + ']';
  if (n.tag === 'concat') return show(n.children[0], argNamesTable, render) + ' ++ ' + show(n.children[1], argNamesTable, render);
  if (n.tag === 'freevar') return n.children[0];
  if (n.tag === 'metavar') return '?' + n.children[0];
  if (n.tag === render.implication) return render.implication + '(' + show(n.children[0], argNamesTable, render) + ', ...)';
  if (n.tag === render.exponential) {
    const grade = n.children[0];
    const inner = n.children[1];
    const prefix = grade === render.grade0() ? '!_0 ' : '!';
    return prefix + show(inner, argNamesTable, render);
  }
  if (n.tag === render.product) return show(n.children[0], argNamesTable, render) + ' * ' + show(n.children[1], argNamesTable, render);
  if (n.tag === render.unit) return '1';
  if (n.tag === render.additiveZero) return '0';
  // Predicate with named args
  if (argNamesTable) {
    const names = argNamesTable.get(n.tag);
    if (names) {
      return n.tag + '(' + n.children.map((c, i) => {
        const val = typeof c === 'number' ? show(c, argNamesTable, render) : String(c);
        return names[i] ? names[i] + ': ' + val : val;
      }).join(', ') + ')';
    }
  }
  return n.tag + '(' + n.children.map(c =>
    typeof c === 'number' ? show(c, argNamesTable, render) : String(c)
  ).join(', ') + ')';
}

/**
 * Classify a explore leaf state.
 * Polymorphic: accepts FactSet-based State or plain { linear: {hash:count} } objects.
 * @param {Object} state
 * @param {Object} [policy] - { terminals: {atomName: label}, runningPred }
 *   (default: the EVM/ILL instance — stop/revert/invalid, pc)
 * @returns {string} a terminal label, 'RUNNING', 'STUCK', or 'NO_STATE'
 */
function classifyLeaf(state, policy = DEFAULT_LEAF_POLICY) {
  if (!state) return 'NO_STATE';
  const terminals = policy.terminals || {};
  const runningPred = policy.runningPred || null;
  if (state.linear && state.linear.group) {
    // FactSet path: direct group access
    const atomGroup = state.linear.group(Store.TAG.atom);
    for (let i = 0; i < atomGroup.length; i++) {
      const label = terminals[Store.child(atomGroup[i], 0)];
      if (label) return label;
    }
    const runTagId = runningPred !== null ? Store.TAG[runningPred] : undefined;
    if (runTagId !== undefined && state.linear.groupLen(runTagId) > 0) return 'RUNNING';
    return 'STUCK';
  }
  // Plain object fallback (hand-built test trees)
  for (const h of Object.keys(state.linear)) {
    const label = terminals[predHead(Number(h))];
    if (label) return label;
  }
  if (runningPred !== null) {
    for (const h of Object.keys(state.linear)) {
      if (predHead(Number(h)) === runningPred) return 'RUNNING';
    }
  }
  return 'STUCK';
}

/**
 * Show interesting facts from a leaf state (pc, stop, revert, loli).
 * Polymorphic: accepts FactSet-based State or plain { linear: {hash:count} } objects.
 * @param {Object} state
 * @param {Object} [opts]
 * @param {string[]} [opts.exclude] - predicates to exclude
 *   (default: the EVM instance — ['bytecode','calldata'])
 * @returns {string[]}
 */
function showInteresting(state, opts = {}) {
  const exclude = new Set(opts.exclude || DEFAULT_SHOW_EXCLUDE);
  const result = [];
  if (state.linear && state.linear.forEach) {
    // FactSet path
    state.linear.forEach(h => {
      const pred = predHead(h);
      if (exclude.has(pred)) return;
      result.push(show(h));
    });
  } else {
    // Plain object fallback
    for (const h of Object.keys(state.linear)) {
      const hn = Number(h);
      const pred = predHead(hn);
      if (exclude.has(pred)) continue;
      result.push(show(hn));
    }
  }
  return result;
}

export { show, classifyLeaf, showInteresting, DEFAULT_RENDER, DEFAULT_LEAF_POLICY, DEFAULT_SHOW_EXCLUDE };
export default { show, classifyLeaf, showInteresting, DEFAULT_RENDER, DEFAULT_LEAF_POLICY, DEFAULT_SHOW_EXCLUDE };
