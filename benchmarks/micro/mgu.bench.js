/**
 * MGU (Most General Unifier) Micro-benchmarks
 */

const { BenchmarkRunner } = require('../lib/runner');

// Setup
const calc = require('../../ll.json');
const calcParser = require('../../lib/parser.js');
const mgu = require('../../lib/mgu.js');

const parser = calcParser(calc).parser;

// Parse formula and extract first term for unification
function parseTerm(str) {
  const fullSeq = `-- : ${str} |- -- : A`;
  const node = parser.parse(fullSeq);
  // Get the antecedent formula: node.vals[0].vals[1]
  // node is Sequent, vals[0] is Structure_Term_Formula, vals[1] is the formula
  return node.vals[0].vals[1];
}

// Create unification problems
const terms = {
  atom_same: [parseTerm('P'), parseTerm('P')],
  atom_diff: [parseTerm('P'), parseTerm('Q')],
  tensor_simple: [parseTerm('A * B'), parseTerm('A * B')],
  tensor_var: [parseTerm('A * B'), parseTerm('F?X * F?Y')],
  nested_tensor: [parseTerm('(A * B) * C'), parseTerm('(A * B) * C')],
  loli_simple: [parseTerm('A -o B'), parseTerm('A -o B')],
  loli_var: [parseTerm('A -o B'), parseTerm('F?X -o F?Y')],
  complex: [parseTerm('(A * B) -o (C & D)'), parseTerm('(F?X * F?Y) -o (F?Z & F?W)')],
};

function runMguBenchmarks(runner) {
  // Successful unifications
  runner.run('mgu.atom_same', () => {
    mgu([[terms.atom_same[0].copy(), terms.atom_same[1].copy()]]);
  });

  runner.run('mgu.tensor_simple', () => {
    mgu([[terms.tensor_simple[0].copy(), terms.tensor_simple[1].copy()]]);
  });

  runner.run('mgu.tensor_var', () => {
    mgu([[terms.tensor_var[0].copy(), terms.tensor_var[1].copy()]]);
  });

  runner.run('mgu.nested_tensor', () => {
    mgu([[terms.nested_tensor[0].copy(), terms.nested_tensor[1].copy()]]);
  });

  runner.run('mgu.loli_simple', () => {
    mgu([[terms.loli_simple[0].copy(), terms.loli_simple[1].copy()]]);
  });

  runner.run('mgu.loli_var', () => {
    mgu([[terms.loli_var[0].copy(), terms.loli_var[1].copy()]]);
  });

  runner.run('mgu.complex', () => {
    mgu([[terms.complex[0].copy(), terms.complex[1].copy()]]);
  });

  // Failed unification
  runner.run('mgu.fail_atom', () => {
    mgu([[terms.atom_diff[0].copy(), terms.atom_diff[1].copy()]]);
  });
}

module.exports = { runMguBenchmarks };

// CLI entry point
if (require.main === module) {
  const runner = new BenchmarkRunner({ iterations: 1000, warmup: 100 });
  console.log('Running MGU micro-benchmarks...\n');
  runMguBenchmarks(runner);
  console.log(runner.report());
}
