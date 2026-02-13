/**
 * v2 Proof Search Benchmarks
 *
 * Uses the refactored v2 prover with focused proof search
 */

const { BenchmarkRunner } = require('../lib/runner');

// v2 imports
const calcV2 = require('../../lib/calculus');
const proverV2 = require('../../lib/prover');
const SeqV2 = require('../../lib/kernel/sequent');

// Cached calculus and prover (initialized lazily)
let _calc = null;
let _prover = null;

async function getProver() {
  if (!_prover) {
    _calc = await calcV2.loadILL();
    _prover = proverV2.create(_calc);
  }
  return { calc: _calc, prover: _prover };
}

/**
 * v2 fixtures - same proofs as v1, but in v2 format
 * Format: [linearFormulas[], succedent]
 */
const fixtures = {
  simple: {
    identity: [['A'], 'A'],
    identity_var: [['X'], 'X'],  // Same as identity for v2
    modus_ponens: [['P', 'P -o Q'], 'Q'],
  },

  medium: {
    tensor_id: [['P * Q'], 'P * Q'],
    tensor_comm: [['P * Q'], 'Q * P'],
    tensor_assoc: [['(A * B) * C'], 'A * (B * C)'],
    with_elim_l: [['A & B'], 'A'],
    with_elim_r: [['A & B'], 'B'],
    with_intro: [['A'], 'A & A'],
    currying: [['(A * B) -o C'], 'A -o (B -o C)'],
    uncurrying: [['A -o (B -o C)'], '(A * B) -o C'],
  },

  complex: {
    distribution: [['P -o (R & Q)'], '(P -o Q) & (P -o R)'],
    tensor_with: [['(A & B) * (C & D)'], '(A * C) & (B * D)'],
    deep_loli: [['A -o (B -o (C -o D))'], '((A * B) * C) -o D'],
    nested_with: [['(A & B) & (C & D)'], 'A & D'],
  },

  stress: {
    many_tensor: [['A * B * C * D'], 'D * C * B * A'],
    deep_tensor: [['((((A * B) * C) * D) * E)'], 'A * (B * (C * (D * E)))'],
    many_with: [['A & B & C & D'], 'A & D'],
  },
};

fixtures.all = { ...fixtures.simple, ...fixtures.medium, ...fixtures.complex, ...fixtures.stress };

/**
 * Prove a formula with v2 prover
 */
async function proveV2(linearFormulas, succedent) {
  const { calc, prover } = await getProver();

  const linearAST = linearFormulas.map(f => calc.parse(f));
  const succAST = calc.parse(succedent);
  const seq = SeqV2.fromArrays(linearAST, [], succAST);

  return prover.prove(seq);
}

/**
 * Run v2 proof benchmarks
 */
async function runV2ProofBenchmarks(runner, category = 'all') {
  const formulas = category === 'all' ? fixtures.all : fixtures[category];

  if (!formulas) {
    console.error(`Unknown category: ${category}`);
    return;
  }

  // Ensure prover is initialized before benchmarks
  await getProver();

  for (const [name, [linear, succ]] of Object.entries(formulas)) {
    // Sync wrapper for runner.run
    runner.run(`v2.proof.${name}`, () => {
      // Note: This is synchronous because we pre-initialize the prover
      const { calc, prover } = { calc: _calc, prover: _prover };
      const linearAST = linear.map(f => calc.parse(f));
      const succAST = calc.parse(succ);
      const seq = SeqV2.fromArrays(linearAST, [], succAST);
      const result = prover.prove(seq);

      if (!result.success) {
        throw new Error(`Failed to prove: ${name}`);
      }
    });
  }
}

/**
 * Run v2 benchmarks with profiling (counting operations)
 */
async function runV2WithProfiling(category = 'all') {
  const formulas = category === 'all' ? fixtures.all : fixtures[category];

  if (!formulas) {
    console.error(`Unknown category: ${category}`);
    return {};
  }

  await getProver();
  const results = {};

  for (const [name, [linear, succ]] of Object.entries(formulas)) {
    const { calc, prover } = { calc: _calc, prover: _prover };
    const linearAST = linear.map(f => calc.parse(f));
    const succAST = calc.parse(succ);
    const seq = SeqV2.fromArrays(linearAST, [], succAST);

    const result = prover.prove(seq);

    if (!result.success) {
      console.error(`Failed to prove: ${name}`);
      continue;
    }

    // Count proof tree statistics
    const pt = result.proofTree;
    results[name] = {
      treeSize: pt.size(),
      treeDepth: pt.depth(),
      success: true,
    };
  }

  return results;
}

module.exports = {
  runV2ProofBenchmarks,
  runV2WithProfiling,
  proveV2,
  fixtures,
  getProver,
};

// CLI entry point
if (require.main === module) {
  const category = process.argv[2] || 'all';

  (async () => {
    const runner = new BenchmarkRunner({ iterations: 20, warmup: 5 });

    console.log(`Running v2 proof benchmarks (category: ${category})...\n`);
    await runV2ProofBenchmarks(runner, category);
    console.log(runner.report());

    console.log('\n--- Proof Tree Stats ---\n');
    const stats = await runV2WithProfiling(category);
    for (const [name, s] of Object.entries(stats)) {
      console.log(`${name}: size=${s.treeSize}, depth=${s.treeDepth}`);
    }
  })();
}
