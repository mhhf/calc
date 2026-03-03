/**
 * Pretty-print content-addressed hashes for debugging.
 *
 * Usage:
 *   const { show } = require('./show');
 *   console.log(show(hash));              // "pc(0x3b)"
 *   console.log(showState(state));        // grouped by predicate
 */

const Store = require('../kernel/store');
const { getPredicateHead } = require('../kernel/ast');

/**
 * Pretty-print a single content-addressed hash.
 * @param {number} h
 * @returns {string}
 */
function show(h) {
  const n = Store.get(h);
  if (!n) return String(h);
  if (n.tag === 'atom') return n.children[0];
  if (n.tag === 'binlit') return '0x' + n.children[0].toString(16);
  if (n.tag === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (!elems) return 'arrlit(?)';
    if (elems.length <= 5) return '[' + Array.from(elems).map(show).join(', ') + ']';
    return '[' + Array.from(elems.subarray(0, 5)).map(show).join(', ') + ', ...' + elems.length + ']';
  }
  if (n.tag === 'freevar') return n.children[0];
  if (n.tag === 'loli') return 'loli(' + show(n.children[0]) + ', ...)';
  if (n.tag === 'bang') return '!' + show(n.children[0]);
  if (n.tag === 'tensor') return show(n.children[0]) + ' * ' + show(n.children[1]);
  if (n.tag === 'one') return '1';
  if (n.tag === 'zero') return '0';
  return n.tag + '(' + n.children.map(c =>
    typeof c === 'number' ? show(c) : String(c)
  ).join(', ') + ')';
}

/**
 * Classify a symexec leaf state.
 * Polymorphic: accepts FactSet-based State or plain { linear: {hash:count} } objects.
 * @param {Object} state
 * @returns {'STOP'|'REVERT'|'INVALID'|'RUNNING'|'STUCK'|'NO_STATE'}
 */
function classifyLeaf(state) {
  if (!state) return 'NO_STATE';
  if (state.linear && state.linear.group) {
    // FactSet path: direct group access
    const atomGroup = state.linear.group(Store.TAG.atom);
    for (let i = 0; i < atomGroup.length; i++) {
      const name = Store.child(atomGroup[i], 0);
      if (name === 'stop') return 'STOP';
      if (name === 'revert') return 'REVERT';
      if (name === 'invalid') return 'INVALID';
    }
    const pcTagId = Store.TAG['pc'];
    if (pcTagId !== undefined && state.linear.groupLen(pcTagId) > 0) return 'RUNNING';
    return 'STUCK';
  }
  // Plain object fallback (hand-built test trees)
  for (const h of Object.keys(state.linear)) {
    const pred = getPredicateHead(Number(h));
    if (pred === 'stop') return 'STOP';
    if (pred === 'revert') return 'REVERT';
    if (pred === 'invalid') return 'INVALID';
  }
  for (const h of Object.keys(state.linear)) {
    if (getPredicateHead(Number(h)) === 'pc') return 'RUNNING';
  }
  return 'STUCK';
}

/**
 * Show interesting facts from a leaf state (pc, stop, revert, loli).
 * Polymorphic: accepts FactSet-based State or plain { linear: {hash:count} } objects.
 * @param {Object} state
 * @param {Object} [opts]
 * @param {string[]} [opts.exclude] - predicates to exclude (default: ['bytecode','calldata'])
 * @returns {string[]}
 */
function showInteresting(state, opts = {}) {
  const exclude = new Set(opts.exclude || ['bytecode', 'calldata']);
  const result = [];
  if (state.linear && state.linear.forEach) {
    // FactSet path
    state.linear.forEach(h => {
      const pred = getPredicateHead(h);
      if (exclude.has(pred)) return;
      result.push(show(h));
    });
  } else {
    // Plain object fallback
    for (const h of Object.keys(state.linear)) {
      const hn = Number(h);
      const pred = getPredicateHead(hn);
      if (exclude.has(pred)) continue;
      result.push(show(hn));
    }
  }
  return result;
}

module.exports = { show, classifyLeaf, showInteresting };
