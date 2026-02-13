/**
 * AST Hashing (content-addressed)
 *
 * With the new content-addressed architecture, terms ARE their hashes.
 * This module provides backwards compatibility and the hashAST function
 * which is now just the identity function.
 */

/**
 * Get the hash of a term.
 * Since terms are now represented as hashes, this is the identity function.
 *
 * @param {number} h - Term hash
 * @returns {number} Same hash
 */
const hashAST = h => h;

module.exports = { hashAST };
