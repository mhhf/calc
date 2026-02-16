#!/usr/bin/env node
/**
 * Symexec tree inspector — run symbolic execution and display leaf analysis.
 *
 * Usage:
 *   node tools/symexec-inspect.js [options] <files...>
 *
 * Options:
 *   --query <name>    Query directive name (default: symex)
 *   --depth <n>       Max exploration depth (default: 200)
 *   --leaf <n>        Show full state for leaf N
 *   --exclude <preds> Comma-separated predicates to hide (default: code,calldata)
 *   --all             Show all leaf states (not just summary)
 *
 * Examples:
 *   node tools/symexec-inspect.js calculus/ill/programs/{bin,evm,multisig}.ill
 *   node tools/symexec-inspect.js --leaf 2 calculus/ill/programs/{bin,evm,multisig}.ill
 *   node tools/symexec-inspect.js --all --exclude code,calldata,storage calculus/ill/programs/{bin,evm,multisig}.ill
 */

const path = require('path');

const args = process.argv.slice(2);
const opts = { query: 'symex', depth: 200, leaf: null, exclude: 'code,calldata', all: false };
const files = [];

for (let i = 0; i < args.length; i++) {
  if (args[i] === '--query') { opts.query = args[++i]; continue; }
  if (args[i] === '--depth') { opts.depth = parseInt(args[++i]); continue; }
  if (args[i] === '--leaf') { opts.leaf = parseInt(args[++i]); continue; }
  if (args[i] === '--exclude') { opts.exclude = args[++i]; continue; }
  if (args[i] === '--all') { opts.all = true; continue; }
  files.push(path.resolve(args[i]));
}

if (files.length === 0) {
  console.error('Usage: node tools/symexec-inspect.js [options] <files...>');
  process.exit(1);
}

(async () => {
  const mde = require('../lib/engine');
  const symexec = require('../lib/engine/symexec');
  const { show, classifyLeaf, showInteresting } = require('../lib/engine/show');

  const calc = await mde.load(files);
  const query = calc.queries.get(opts.query);
  if (!query) {
    console.error(`Query '${opts.query}' not found. Available: ${[...calc.queries.keys()].join(', ')}`);
    process.exit(1);
  }

  const state = mde.decomposeQuery(query);
  const calcCtx = { clauses: calc.clauses, types: calc.types };

  const t0 = performance.now();
  const tree = symexec.explore(state, calc.forwardRules, { maxDepth: opts.depth, calc: calcCtx });
  const elapsed = performance.now() - t0;

  const leaves = symexec.getAllLeaves(tree);
  const nodes = symexec.countNodes(tree);
  const depth = symexec.maxDepth(tree);

  console.log(`Nodes: ${nodes}  Leaves: ${leaves.length}  Depth: ${depth}  Time: ${elapsed.toFixed(1)}ms`);
  console.log();

  const excludeSet = opts.exclude.split(',').filter(Boolean);

  for (let i = 0; i < leaves.length; i++) {
    const leaf = leaves[i];
    const status = classifyLeaf(leaf.state);
    const marker = status === 'STOP' ? '\x1b[32m' : status === 'REVERT' ? '\x1b[33m' :
      status === 'RUNNING' ? '\x1b[36m' : '\x1b[31m';

    if (opts.leaf !== null && opts.leaf !== i) continue;

    if (opts.all || opts.leaf === i) {
      console.log(`${marker}Leaf ${i} [${leaf.type}]: ${status}\x1b[0m`);
      if (leaf.state) {
        const facts = showInteresting(leaf.state, { exclude: excludeSet });
        for (const f of facts) console.log(`  ${f}`);
      }
      console.log();
    } else {
      const interesting = leaf.state
        ? showInteresting(leaf.state, { exclude: [...excludeSet, 'storage', 'balance', 'mstore'] })
            .filter(f => /^(stop|revert|invalid|pc|loli|unblock)/.test(f))
        : [];
      console.log(`${marker}Leaf ${i} [${leaf.type}]: ${status}\x1b[0m — ${interesting.join(', ')}`);
    }
  }
})();
