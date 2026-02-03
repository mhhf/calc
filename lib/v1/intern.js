/**
 * Intern - Convert between Node AST and content-addressed Terms
 *
 * internNode: Node -> Term (hash in global store)
 * externNode: Term -> Node (reconstruct AST)
 *
 * Uses the global store singleton - no need to pass store around.
 */

const { Term } = require('./term');
const { profiler } = require('./profiler');
const { getStore } = require('./store');

/**
 * Intern a Node AST into the global store, returning a Term
 *
 * @param {Node|string} node - Node to intern
 * @returns {Term} - Content-addressed term
 */
function internNode(node) {
  profiler.count('intern.node');
  const store = getStore();

  // Handle string values (atom names, variable names)
  if (typeof node === 'string') {
    return Term.fromString(store, node);
  }

  // Handle Node objects
  const constructorId = node.id;
  const childHashes = node.vals.map(child => internNode(child).hash);

  return Term.struct(store, constructorId, childHashes);
}

/**
 * Extern a Term back to a Node AST
 *
 * @param {Term|bigint} termOrHash - Term or hash to extern
 * @param {Function} NodeClass - Node constructor
 * @returns {Node|string} - Reconstructed AST
 */
function externNode(termOrHash, NodeClass) {
  profiler.count('extern.node');
  const store = getStore();

  const term = termOrHash instanceof Term
    ? termOrHash
    : Term.fromHash(store, termOrHash);

  // Handle string values
  if (term.isString()) {
    return term.getString();
  }

  // Handle bigint values (shouldn't normally appear in formula ASTs)
  if (term.isBigInt()) {
    return term.getBigInt().toString();
  }

  // Handle structural nodes
  if (term.isStruct()) {
    const constructorId = term.constructorId();
    const vals = term.children().map(child => externNode(child, NodeClass));
    return new NodeClass(constructorId, vals);
  }

  throw new Error(`Cannot extern unknown term type: ${term.hash}`);
}

/**
 * Intern a sequent-like tree structure
 * Returns hashes for context and succedent
 */
function internSequent(sequentNode) {
  profiler.count('intern.sequent');

  // A sequent node typically has structure:
  // vals[0] = antecedent (left side)
  // vals[1] = succedent (right side)

  const term = internNode(sequentNode);
  return {
    hash: term.hash,
    term: term,
  };
}

/**
 * Check if two nodes are equal via content addressing
 */
function nodesEqual(node1, node2) {
  const t1 = internNode(node1);
  const t2 = internNode(node2);
  return t1.equals(t2);
}

/**
 * Get all subterms of a node (for subformula property)
 */
function getSubterms(node) {
  const term = internNode(node);
  const subterms = new Set();

  term.fold((acc, t) => {
    acc.add(t.hash);
    return acc;
  }, subterms);

  return subterms;
}

/**
 * Count nodes in a term (for complexity analysis)
 */
function countNodes(node) {
  const term = internNode(node);
  return term.fold((acc, _) => acc + 1, 0);
}

module.exports = {
  internNode,
  externNode,
  internSequent,
  nodesEqual,
  getSubterms,
  countNodes,
};
