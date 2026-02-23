/**
 * Execution Tree Utilities
 *
 * Display and analysis functions for execution trees from symexec.explore().
 * Separated from symexec.js for clean module boundaries.
 */

function isTerminal(tree) {
  return tree.type === 'leaf' || tree.type === 'bound' || tree.type === 'cycle';
}

function countLeaves(tree) {
  if (isTerminal(tree)) return 1;
  return tree.children.reduce((sum, c) => sum + countLeaves(c.child), 0);
}

function getAllLeaves(tree) {
  if (isTerminal(tree)) return [tree];
  return tree.children.flatMap(c => getAllLeaves(c.child));
}

function maxDepth(tree, d = 0) {
  if (isTerminal(tree)) return d;
  return Math.max(...tree.children.map(c => maxDepth(c.child, d + 1)));
}

function countNodes(tree) {
  if (isTerminal(tree)) return 1;
  return 1 + tree.children.reduce((sum, c) => sum + countNodes(c.child), 0);
}

/**
 * Convert execution tree to DOT (Graphviz) format.
 *
 * @param {Object} tree - Execution tree from explore()
 * @param {Object} [opts]
 * @param {function} [opts.render] - (state) => string label for nodes
 * @returns {string} DOT source
 */
function toDot(tree, opts = {}) {
  const render = opts.render || (() => '');
  const lines = ['digraph exec {'];
  let nextId = 0;

  const colors = { leaf: 'green', bound: 'yellow', cycle: 'red', branch: 'white' };

  function visit(node) {
    const id = nextId++;
    const color = colors[node.type] || 'white';
    const label = node.state ? render(node.state).replace(/"/g, '\\"') : '';
    lines.push(`  n${id} [label="${node.type}${label ? '\\n' + label : ''}" style=filled fillcolor=${color}];`);

    if (node.type === 'branch') {
      for (const c of node.children) {
        const childId = visit(c.child);
        const edgeLabel = c.choice !== undefined
          ? `${c.rule}[${c.choice}]`
          : c.rule;
        lines.push(`  n${id} -> n${childId} [label="${edgeLabel}"];`);
      }
    }
    return id;
  }

  visit(tree);
  lines.push('}');
  return lines.join('\n');
}

module.exports = {
  isTerminal,
  countLeaves,
  getAllLeaves,
  maxDepth,
  countNodes,
  toDot
};
