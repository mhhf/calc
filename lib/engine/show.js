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
  if (n.tag === 'freevar') return n.children[0];
  if (n.tag === 'loli') return 'loli(' + show(n.children[0]) + ', ...)';
  if (n.tag === 'bang') return '!' + show(n.children[0]);
  if (n.tag === 'tensor') return show(n.children[0]) + ' * ' + show(n.children[1]);
  if (n.tag === 'one') return '1';
  return n.tag + '(' + n.children.map(c =>
    typeof c === 'number' ? show(c) : String(c)
  ).join(', ') + ')';
}

/**
 * Classify a symexec leaf state.
 * @param {{ linear: Object, persistent: Object }} state
 * @returns {'STOP'|'REVERT'|'INVALID'|'RUNNING'|'STUCK'}
 */
function classifyLeaf(state) {
  if (!state) return 'NO_STATE';
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
 * Show interesting facts from a leaf state (pc, stop, revert, loli, unblock).
 * @param {{ linear: Object }} state
 * @param {Object} [opts]
 * @param {string[]} [opts.exclude] - predicates to exclude (default: ['code','calldata'])
 * @returns {string[]}
 */
function showInteresting(state, opts = {}) {
  const exclude = new Set(opts.exclude || ['code', 'calldata']);
  const result = [];
  for (const h of Object.keys(state.linear)) {
    const hn = Number(h);
    const pred = getPredicateHead(hn);
    if (exclude.has(pred)) continue;
    result.push(show(hn));
  }
  return result;
}

module.exports = { show, classifyLeaf, showInteresting };
