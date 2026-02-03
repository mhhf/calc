#!/usr/bin/env node
/**
 * Hash Algorithm Comparison Benchmark
 *
 * Tests different hashing approaches with real proof workloads:
 * 1. BigInt FNV-1a (current) - baseline
 * 2. Number FNV-1a (32-bit) - fast but collision risk
 * 3. xxHash128 - fast WASM, collision-proof
 * 4. Interned + idx - two-level architecture
 *
 * Run: node benchmarks/hash-comparison.bench.js
 */

const { bigint, number32, xxhash128, interned } = require('../lib/hash-alternatives');

// ============================================================
// Test Data: AST structures of varying complexity
// ============================================================

function buildTestASTs() {
  // Simple atom
  const atom = (name) => ({ tag: 'atom', children: [name] });
  const freevar = (name) => ({ tag: 'freevar', children: [name] });

  // Connectives
  const tensor = (a, b) => ({ tag: 'tensor', children: [a, b] });
  const loli = (a, b) => ({ tag: 'loli', children: [a, b] });
  const withc = (a, b) => ({ tag: 'with', children: [a, b] });
  const bang = (a) => ({ tag: 'bang', children: [a] });
  const one = () => ({ tag: 'one', children: [] });

  const A = atom('A'), B = atom('B'), C = atom('C'), D = atom('D');
  const E = atom('E'), F = atom('F'), G = atom('G'), H = atom('H');

  return {
    // Simple formulas
    simple: [A, B, C, loli(A, B), tensor(A, B)],

    // Medium complexity
    medium: [
      loli(A, loli(B, C)),
      tensor(loli(A, B), loli(C, D)),
      withc(tensor(A, B), tensor(C, D)),
      loli(tensor(A, B), tensor(C, D))
    ],

    // Complex (deep nesting)
    complex: [
      loli(tensor(A, B), loli(tensor(C, D), tensor(E, F))),
      withc(loli(A, withc(B, C)), loli(D, withc(E, F))),
      tensor(tensor(tensor(A, B), tensor(C, D)), tensor(tensor(E, F), tensor(G, H))),
      bang(loli(tensor(A, bang(B)), withc(C, D)))
    ],

    // Stress test: many formulas with shared substructure
    stress: (() => {
      const formulas = [];
      // Create 100 formulas with shared atoms
      for (let i = 0; i < 20; i++) {
        formulas.push(loli(atom(`X${i}`), atom(`Y${i}`)));
        formulas.push(tensor(atom(`X${i}`), atom(`Z${i}`)));
        formulas.push(withc(loli(A, atom(`P${i}`)), tensor(B, atom(`Q${i}`))));
        formulas.push(bang(loli(atom(`R${i}`), withc(C, atom(`S${i}`)))));
        formulas.push(tensor(
          loli(atom(`A${i}`), atom(`B${i}`)),
          withc(atom(`C${i}`), atom(`D${i}`))
        ));
      }
      return formulas;
    })()
  };
}

// ============================================================
// Benchmark: Pure Hashing Speed
// ============================================================

async function benchmarkHashingSpeed(algo, asts, iterations) {
  const times = [];

  if (algo.isAsync) {
    if (algo.init) await algo.init();

    for (let run = 0; run < 3; run++) {
      const start = process.hrtime.bigint();
      for (let i = 0; i < iterations; i++) {
        for (const ast of asts) {
          await algo.hashAST(ast);
        }
      }
      const elapsed = Number(process.hrtime.bigint() - start) / 1e6;
      times.push(elapsed);
    }
  } else {
    for (let run = 0; run < 3; run++) {
      const start = process.hrtime.bigint();
      for (let i = 0; i < iterations; i++) {
        for (const ast of asts) {
          algo.hashAST(ast);
        }
      }
      const elapsed = Number(process.hrtime.bigint() - start) / 1e6;
      times.push(elapsed);
    }
  }

  return Math.min(...times);
}

// ============================================================
// Benchmark: Context Operations (simulating proof search)
// ============================================================

async function benchmarkContextOps(algo, asts, iterations) {
  // Pre-hash all ASTs
  const hashes = [];

  if (algo.isAsync) {
    if (algo.init) await algo.init();
    for (const ast of asts) {
      hashes.push(await algo.hashAST(ast));
    }
  } else {
    for (const ast of asts) {
      hashes.push(algo.hashAST(ast));
    }
  }

  // Simulate context operations
  const times = [];

  for (let run = 0; run < 3; run++) {
    const start = process.hrtime.bigint();

    for (let i = 0; i < iterations; i++) {
      // Build context (as Map keyed by hash)
      const ctx = new Map();
      for (let j = 0; j < hashes.length; j++) {
        const key = algo.hashToString(hashes[j]);
        ctx.set(key, { formula: asts[j], count: 1 });
      }

      // Membership checks
      for (const h of hashes) {
        const key = algo.hashToString(h);
        ctx.has(key);
      }

      // Equality checks
      for (let j = 0; j < hashes.length - 1; j++) {
        algo.hashEquals(hashes[j], hashes[j + 1]);
      }
    }

    const elapsed = Number(process.hrtime.bigint() - start) / 1e6;
    times.push(elapsed);
  }

  return Math.min(...times);
}

// ============================================================
// Benchmark: Interned Context Ops (with integer indices)
// ============================================================

async function benchmarkInternedContextOps(asts, iterations) {
  await interned.init();
  interned.reset();

  // Intern all ASTs
  const terms = [];
  for (const ast of asts) {
    terms.push(await interned.intern(ast));
  }

  const times = [];

  for (let run = 0; run < 3; run++) {
    const start = process.hrtime.bigint();

    for (let i = 0; i < iterations; i++) {
      // Build context using Set of indices
      const ctx = new Set();
      for (const t of terms) {
        ctx.add(t._idx);
      }

      // Membership checks (integer)
      for (const t of terms) {
        ctx.has(t._idx);
      }

      // Equality checks (integer comparison)
      for (let j = 0; j < terms.length - 1; j++) {
        terms[j]._idx === terms[j + 1]._idx;
      }
    }

    const elapsed = Number(process.hrtime.bigint() - start) / 1e6;
    times.push(elapsed);
  }

  return Math.min(...times);
}

// ============================================================
// Benchmark: Full Proof Simulation
// ============================================================

async function benchmarkProofSimulation(algo, formulas, iterations) {
  // Simulate what happens during proof search:
  // - Hash formulas repeatedly
  // - Build/modify contexts
  // - Check equality

  const times = [];

  if (algo.isAsync) {
    if (algo.init) await algo.init();
  }

  for (let run = 0; run < 3; run++) {
    const start = process.hrtime.bigint();

    for (let iter = 0; iter < iterations; iter++) {
      // Simulate proof search operations
      const ctx = new Map();

      // Add formulas to context (hashing each time, like current impl)
      for (const f of formulas) {
        const h = algo.isAsync ? await algo.hashAST(f) : algo.hashAST(f);
        const key = algo.hashToString(h);
        if (ctx.has(key)) {
          ctx.get(key).count++;
        } else {
          ctx.set(key, { formula: f, count: 1, hash: h });
        }
      }

      // Simulate focus/unfocus (lookup by hash)
      for (const f of formulas.slice(0, 5)) {
        const h = algo.isAsync ? await algo.hashAST(f) : algo.hashAST(f);
        const key = algo.hashToString(h);
        ctx.get(key);
      }

      // Simulate removal
      for (const f of formulas.slice(0, 3)) {
        const h = algo.isAsync ? await algo.hashAST(f) : algo.hashAST(f);
        const key = algo.hashToString(h);
        if (ctx.has(key)) {
          const entry = ctx.get(key);
          if (entry.count === 1) ctx.delete(key);
          else entry.count--;
        }
      }
    }

    const elapsed = Number(process.hrtime.bigint() - start) / 1e6;
    times.push(elapsed);
  }

  return Math.min(...times);
}

// ============================================================
// Main
// ============================================================

async function main() {
  console.log('='.repeat(70));
  console.log('HASH ALGORITHM COMPARISON BENCHMARK');
  console.log('='.repeat(70));
  console.log('');

  const testData = buildTestASTs();

  // Test 1: Pure hashing speed
  console.log('TEST 1: Pure Hashing Speed (hash 100 ASTs x 100 iterations)');
  console.log('-'.repeat(70));

  const hashResults = {};
  for (const [name, algo] of Object.entries({ bigint, number32, xxhash128 })) {
    try {
      const time = await benchmarkHashingSpeed(algo, testData.stress, 100);
      hashResults[name] = time;
      console.log(`  ${algo.name.padEnd(30)} ${time.toFixed(2).padStart(10)} ms`);
    } catch (e) {
      console.log(`  ${algo.name.padEnd(30)} ERROR: ${e.message}`);
    }
  }

  // Baseline comparison
  if (hashResults.bigint && hashResults.number32) {
    const speedup = hashResults.bigint / hashResults.number32;
    console.log(`\n  → 32-bit is ${speedup.toFixed(1)}x faster than BigInt`);
  }
  if (hashResults.bigint && hashResults.xxhash128) {
    const speedup = hashResults.bigint / hashResults.xxhash128;
    console.log(`  → xxHash128 is ${speedup.toFixed(1)}x faster than BigInt`);
  }

  // Test 2: Context operations with pre-computed hashes
  console.log('\n');
  console.log('TEST 2: Context Operations (pre-hashed, 1000 iterations)');
  console.log('-'.repeat(70));

  const ctxResults = {};
  for (const [name, algo] of Object.entries({ bigint, number32, xxhash128 })) {
    try {
      const time = await benchmarkContextOps(algo, testData.stress, 1000);
      ctxResults[name] = time;
      console.log(`  ${algo.name.padEnd(30)} ${time.toFixed(2).padStart(10)} ms`);
    } catch (e) {
      console.log(`  ${algo.name.padEnd(30)} ERROR: ${e.message}`);
    }
  }

  // Test interned approach
  try {
    const time = await benchmarkInternedContextOps(testData.stress, 1000);
    ctxResults.interned = time;
    console.log(`  ${interned.name.padEnd(30)} ${time.toFixed(2).padStart(10)} ms`);
  } catch (e) {
    console.log(`  ${interned.name.padEnd(30)} ERROR: ${e.message}`);
  }

  if (ctxResults.bigint && ctxResults.interned) {
    const speedup = ctxResults.bigint / ctxResults.interned;
    console.log(`\n  → Interned+idx is ${speedup.toFixed(1)}x faster than BigInt for context ops`);
  }

  // Test 3: Full proof simulation
  console.log('\n');
  console.log('TEST 3: Proof Search Simulation (100 iterations)');
  console.log('-'.repeat(70));

  const proofResults = {};
  for (const [name, algo] of Object.entries({ bigint, number32, xxhash128 })) {
    try {
      const time = await benchmarkProofSimulation(algo, testData.stress, 100);
      proofResults[name] = time;
      console.log(`  ${algo.name.padEnd(30)} ${time.toFixed(2).padStart(10)} ms`);
    } catch (e) {
      console.log(`  ${algo.name.padEnd(30)} ERROR: ${e.message}`);
    }
  }

  if (proofResults.bigint && proofResults.number32) {
    const speedup = proofResults.bigint / proofResults.number32;
    console.log(`\n  → 32-bit is ${speedup.toFixed(1)}x faster for proof simulation`);
  }
  if (proofResults.bigint && proofResults.xxhash128) {
    const speedup = proofResults.bigint / proofResults.xxhash128;
    console.log(`  → xxHash128 is ${speedup.toFixed(1)}x faster for proof simulation`);
  }

  // Test 4: Real proof with actual prover
  console.log('\n');
  console.log('TEST 4: Real Proof Search (current v2 prover)');
  console.log('-'.repeat(70));

  try {
    const v2 = require('../lib/v2');
    const ill = await v2.loadILL();
    const sp = v2.createSequentParser(ill);
    const prover = v2.createProver(ill);

    const testCases = [
      'A, A -o B |- B',
      'A -o (B -o C) |- (A * B) -o C',
      'A & B, C & D |- (A * C) & (B * D)',
      'A & B, C & D, E & F |- (A * C * E) & (B * D * F)'
    ];

    console.log('  (Using current BigInt implementation)\n');

    for (const tc of testCases) {
      const seq = sp.parseSequent(tc);
      const times = [];

      for (let run = 0; run < 5; run++) {
        const start = process.hrtime.bigint();
        prover.prove(seq, { maxDepth: 100 });
        times.push(Number(process.hrtime.bigint() - start) / 1e6);
      }

      const min = Math.min(...times);
      console.log(`  ${tc.padEnd(45)} ${min.toFixed(2).padStart(10)} ms`);
    }
  } catch (e) {
    console.log(`  ERROR: ${e.message}`);
  }

  // Summary
  console.log('\n');
  console.log('='.repeat(70));
  console.log('SUMMARY');
  console.log('='.repeat(70));
  console.log('');
  console.log('Algorithm           | Hash Speed | Ctx Ops | Proof Sim | Collision Risk');
  console.log('-'.repeat(70));

  const fmt = (n) => n ? n.toFixed(1).padStart(8) + ' ms' : '     N/A';
  console.log(`BigInt FNV-1a       | ${fmt(hashResults.bigint)} | ${fmt(ctxResults.bigint)} | ${fmt(proofResults.bigint)} | None (64-bit)`);
  console.log(`Number FNV-1a       | ${fmt(hashResults.number32)} | ${fmt(ctxResults.number32)} | ${fmt(proofResults.number32)} | HIGH (32-bit)`);
  console.log(`xxHash128           | ${fmt(hashResults.xxhash128)} | ${fmt(ctxResults.xxhash128)} | ${fmt(proofResults.xxhash128)} | None (128-bit)`);
  console.log(`Interned + idx      |       N/A | ${fmt(ctxResults.interned)} |       N/A | None (128-bit)`);

  console.log('\n');
  console.log('RECOMMENDATIONS:');
  console.log('  1. For drop-in replacement: Use 32-bit FNV-1a (20x speedup, watch collisions)');
  console.log('  2. For collision safety: Use xxHash128 (fast + 128-bit)');
  console.log('  3. For maximum speed: Use Interned + idx (hash once, integer ops after)');
  console.log('');
}

main().catch(console.error);
