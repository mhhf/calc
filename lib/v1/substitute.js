const Calc = require("./calc.js");
const { profiler } = require("./profiler.js");
const { internNode } = require("./intern.js");

/**
 * Check if two nodes are equal using O(1) content-addressed comparison
 */
function nodesMatch(node, key) {
  // Same reference = equal
  if (node === key) {
    profiler.count('substitute.eq.ref');
    return true;
  }

  // Both must be objects (not strings)
  if (typeof node !== 'object' || typeof key !== 'object') {
    return false;
  }

  // Different constructors = not equal
  if (node.id !== key.id) {
    return false;
  }

  // Use content-addressed hash (O(1) equality)
  profiler.count('substitute.eq.hash');
  const h0 = internNode(node).hash;
  const h1 = internNode(key).hash;
  return h0 === h1;
}

/**
 * Substitute key with val in node
 *
 * @param {Node|string} node - Node to perform substitution on
 * @param {Node} key - Variable/term to replace
 * @param {Node} val - Replacement value
 * @returns {Node|string} - Node with substitution applied (mutates original)
 */
const sub = function (node, key, val) {
  profiler.count('substitute.call');

  if(typeof node === "string") return node;
  let type = Calc.db.rules[node.id];

  // ignore bounded variables
  if (
    type.ruleName === "Formula_Forall"
    && node.vals[0].vals[0] == key.vals[0]
  ) {
    return node;
  }

  // Check if this node matches the key (what we're replacing)
  if (nodesMatch(node, key)) {
    profiler.count('substitute.match');
    return val.copy();
  }

  // Recursively substitute in children
  node.vals = node.vals
  .map(v => {
    if(typeof v !== "object") return v;
    return sub(v, key, val);
  })
  return node;
}


module.exports = sub;
