/**
 * Disc-tree optimization layer — re-exports from disc-tree.js.
 *
 * When profile.discTree is true, the disc-tree layer is included in
 * the strategy stack for O(pattern_depth) rule lookup. When false,
 * only predicate filtering (linear scan) is used.
 */

const { makeDiscTreeLayer } = require('../disc-tree');

module.exports = { makeDiscTreeLayer };
