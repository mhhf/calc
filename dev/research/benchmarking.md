# CALC Operations Analysis and Benchmarking Strategy

Research document analyzing primitive operations, their complexity, usage frequency, and benchmarking strategy.

---

## Executive Summary

This document catalogs all primitive operations in CALC, analyzes their computational complexity, traces their usage during proof search, and proposes a benchmarking framework to measure real-world performance.

**Key Finding:** The proof search hot path is dominated by:
1. **Unification (mgu)** — O(n²) due to repeated toString() comparisons
2. **Substitution** — O(n) per call, called O(m) times per unification
3. **Context operations** — O(n) per hash computation
4. **Deep copying** — O(n) everywhere, no structural sharing

---

## Part 1: Primitive Operations Catalog

### 1.1 Node Operations (lib/node.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **Create** | `new Node(id, vals)` | O(1) | Allocate node with rule ID and children |
| **Copy** | `node.copy()` | O(n) | Deep recursive copy of entire subtree |
| **Equality** | (implicit via toString) | O(n) | No direct equality — uses string comparison |
| **toString** | `node.toString(style)` | O(n) | Serialize to ASCII/LaTeX/Isabelle format |
| **isVar** | `node.isVar()` | O(1) | Check if node is a variable |
| **isTermType** | `node.isTermType()` | O(1) | Check if Structure_Term_Formula |

**Code location:** `lib/node.js:1-150`

**Key issue:** No identity/hash — equality requires full tree traversal via toString().

### 1.2 Sequent Operations (lib/sequent.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **fromTree** | `Sequent.fromTree(ast)` | O(n) | Parse AST into sequent structure |
| **copy** | `Sequent.copy(seq)` | O(n) | Deep copy entire sequent |
| **toString** | `seq.toString(style)` | O(n) | Serialize sequent |
| **add_to_linear_ctx** | (internal) | O(n) | Add formula to context, hash via sha3(toString) |
| **add_to_antecedent_bulk** | `Sequent.add_to_antecedent_bulk()` | O(m·n) | Add multiple formulas |
| **remove_from_antecedent** | `Sequent.remove_from_antecedent()` | O(m) | Remove formulas from context |
| **remove_structural_variables** | `Sequent.remove_structural_variables()` | O(m) | Clean up structural vars |
| **substitute** | `seq.substitute(theta)` | O(n·k) | Apply substitution list |
| **getFreeVariables** | `Sequent.getFreeVariables()` | O(n) | Collect all free variables |
| **getAtoms** | `Sequent.getAtoms()` | O(n) | Collect atomic propositions |
| **renameUnique** | `Sequent.renameUnique()` | O(n) | Alpha-rename to fresh variables |
| **renameUniqueArray** | `Sequent.renameUniqueArray()` | O(m·n) | Rename array of sequents |
| **constructCompareOptions** | `Sequent.constructCompareOptions()` | O(m!) | Generate permutations for multiset matching |

**Code locations:**
- `lib/sequent.js:255` — sha3(ast.toString()) for context keys
- `lib/sequent.js:420` — fromTree with linear_ctx construction
- `lib/sequent.js:180` — copy operation

**Critical hotspot:** `sha3(ast.toString())` — called on every context insertion.

### 1.3 Unification Operations (lib/mgu.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **mgu** | `mgu(pairs)` | O(n²) | Most General Unifier computation |
| **propagate** | (internal) | O(n·k) | Propagate substitution through pairs |
| **occurs** | (internal) | O(n) | Occurs check |

**Code location:** `lib/mgu.js:1-120`

```javascript
// Line 23: O(n) equality check
let isEq = t0.toString() === t1.toString();

// Line 45-46: O(n) substitutions applied to all remaining pairs
G = G.map(([l, r]) => ([subs(l, t0, t1), subs(r, t0, t1)]))
```

**Complexity breakdown:**
- Per iteration: O(n) equality + O(m·n) substitutions
- Total iterations: O(k) where k = number of variables
- Overall: O(k²·n) in worst case

### 1.4 Substitution Operations (lib/substitute.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **substitute** | `substitute(node, var, term)` | O(n) | Replace variable with term |
| **subs** | `subs(node, var, term)` | O(n) | Alias for substitute |

**Code location:** `lib/substitute.js:1-60`

```javascript
// Line 23: Recursive traversal with copy
return new Node(val.id, val.vals.map(v => {
  return typeof(v) === "object" ? substitute(v, x_, w) : v;
}))
```

**Key issue:** Creates new nodes on every call — no structural sharing.

### 1.5 Comparison Operations (lib/compare.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **compare** | `compare(a, b, theta)` | O(n) | Structural comparison with unification |

**Code location:** `lib/compare.js:1-80`

Returns substitution (theta) for matching, or false if no match.

### 1.6 Proof Tree Operations (lib/pt.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **Create** | `new PT({conclusion, premisses})` | O(1) | Create proof tree node |
| **toTree** | `pt.toTree()` | O(m) | Convert to display tree |
| **toString** | `pt.toString(style)` | O(m·n) | Render proof tree |

**Code location:** `lib/pt.js:1-160`

### 1.7 Proof Search Operations (lib/proofstate.js, lib/prover.js)

| Operation | Function | Current Complexity | Description |
|-----------|----------|-------------------|-------------|
| **auto** | `Proofstate.auto(pt, opts)` | Exponential | Full proof search |
| **getInvertibleRule** | (prover) | O(m) | Find invertible rule |
| **chooseFocus** | (prover) | O(m) | Choose formula to focus on |
| **applyRule** | (prover) | O(n) | Apply inference rule |
| **tryIdentityPositive** | (prover) | O(m·n) | Try Id+ rule |
| **tryIdentityNegative** | (prover) | O(n) | Try Id- rule |
| **continueProof** | (prover) | Recursive | Continue on premises |

**Code locations:**
- `lib/proofstate.js:1-400` — Main proof search loop
- `lib/prover.js:1-530` — Focused prover implementation

---

## Part 2: Call Graph Analysis

### 2.1 Proof Search Call Tree

```
Proofstate.auto(pt)
├── Sequent.getFreeVariables(seq)          [O(n)]
├── prover.getInvertibleRule(pt)           [O(m)]
│   ├── getPolarity(formula)               [O(1)]
│   └── isAtomic(formula)                  [O(1)]
├── prover.chooseFocus(pt)                 [O(m)]
├── prover.applyRule(pt, ruleName, ...)    [O(n)]
│   ├── mgu([[conclusionConnective, ...]])  [O(n²)]
│   │   ├── toString() comparisons          [O(n) × k]
│   │   └── substitute() calls              [O(n) × k]
│   ├── Sequent.substitute(theta)           [O(n·k)]
│   └── new PT({conclusion: seq})           [O(1)]
├── prover.tryIdentityPositive(pt)         [O(m·n)]
│   ├── mgu([[ctxFormula, formula]])        [O(n²)]
│   ├── substitute(succedent, k, v)         [O(n) × k]
│   └── Sequent.remove_from_antecedent()   [O(m)]
├── prover.continueProof(pt, ...)          [Recursive]
│   ├── seq.substitute(theta)               [O(n·k)]
│   ├── Sequent.add_to_antecedent_bulk()   [O(m·n)]
│   │   └── sha3(ast.toString())           [O(n) × m]
│   ├── Sequent.remove_structural_variables() [O(m)]
│   └── Proofstate.auto(premise)           [Recursive]
└── Rule application overhead
    ├── Ruleset.getRule(name)               [O(n) — renameUnique]
    └── seq.copy() for each premise         [O(n)]
```

### 2.2 Hotspot Identification

Based on call graph analysis, the **critical path** operations are:

| Rank | Operation | Frequency | Per-call Cost | Cumulative Impact |
|------|-----------|-----------|---------------|-------------------|
| 1 | `mgu()` | Every rule application | O(n²) | **CRITICAL** |
| 2 | `toString()` | Every mgu, every context op | O(n) | **CRITICAL** |
| 3 | `substitute()` | k times per mgu | O(n) | **HIGH** |
| 4 | `sha3(toString())` | Every context add | O(n) | **HIGH** |
| 5 | `copy()` | Every rule, every premise | O(n) | **MEDIUM** |
| 6 | `renameUnique()` | Every rule fetch | O(n) | **MEDIUM** |

---

## Part 3: Complexity Summary

### 3.1 Current vs Target Complexity

| Operation | Current | With Interning | Improvement |
|-----------|---------|----------------|-------------|
| Node equality | O(n) | O(1) | n× faster |
| Node copy | O(n) | O(1)* | n× faster |
| Context lookup | O(n) | O(1) | n× faster |
| Substitution | O(n) | O(n)** | Same (but shared) |
| MGU | O(n²) | O(n) | n× faster |
| Proof search | O(b^d · n²) | O(b^d · n) | n× faster |

\* With structural sharing, "copy" becomes reference copy
\** Substitution creates new interned nodes but shares subtrees

### 3.2 Estimated Frequency (per proof search)

For a proof of depth d with branching factor b:
- Rule applications: O(b^d)
- MGU calls: O(b^d)
- Substitutions: O(k · b^d) where k = avg variables per rule
- Context operations: O(m · b^d) where m = avg context size
- Copy operations: O(b · b^d) = O(b^(d+1))

**Example: Proving `(A * B) -o C |- A -o (B -o C)` (currying)**
- Depth: ~6 (Loli_R, Loli_R, Tensor_L, Loli_L, Id, Id)
- Branching: ~1.5 (some rules have choices)
- Estimated operations: ~20 rule applications, ~40 MGU calls, ~100 substitutions

---

## Part 4: Benchmarking Strategy

### 4.1 Tools Comparison

| Tool | Resolution | Pros | Cons | Recommendation |
|------|------------|------|------|----------------|
| **Benchmark.js** | ms | Statistical analysis, mature | Overhead, complex | **Integration tests** |
| **perf_hooks** | μs | Native, low overhead | Manual statistics | **Micro-benchmarks** |
| **process.hrtime** | ns | Nanosecond precision | Awkward API | Timing primitives |
| **console.time** | ms | Simple | Low precision | Debugging only |

### 4.2 V8/JIT Considerations

Critical pitfalls to avoid:

1. **Warmup:** Run code 10-100 times before measuring (JIT compilation)
2. **Isolation:** Fresh Node process per benchmark suite
3. **Monomorphism:** Keep object shapes consistent
4. **Dead code elimination:** Ensure results are used
5. **GC interference:** Force GC between runs with `--expose-gc`

```javascript
// Proper warmup pattern
for (let i = 0; i < 100; i++) {
  runBenchmark(); // Warmup — not measured
}

if (global.gc) global.gc(); // Force GC

const times = [];
for (let i = 0; i < 1000; i++) {
  const start = performance.now();
  runBenchmark();
  times.push(performance.now() - start);
}
```

### 4.3 Benchmark Categories

#### Category 1: Micro-benchmarks (Operation Level)

Test individual operations in isolation:

```javascript
// Node operations
benchmark('node.copy() - depth 5', () => deepNode.copy());
benchmark('node.toString() - depth 5', () => deepNode.toString());
benchmark('node equality via toString', () => nodeA.toString() === nodeB.toString());

// Sequent operations
benchmark('sha3(ast.toString())', () => sha3(formula.toString()));
benchmark('Sequent.copy()', () => Sequent.copy(seq));
benchmark('Sequent.add_to_linear_ctx()', () => addToCtx(seq, formula));

// Unification
benchmark('mgu - simple', () => mgu([[simpleA, simpleB]]));
benchmark('mgu - complex', () => mgu([[complexA, complexB]]));

// Substitution
benchmark('substitute - depth 3', () => substitute(node3, varX, termY));
benchmark('substitute - depth 10', () => substitute(node10, varX, termY));
```

#### Category 2: Component Benchmarks

Test operation groups:

```javascript
benchmark('rule application cycle', () => {
  const rule = getRule('Tensor_R');
  const theta = mgu([[rule[0].succedent, seq.succedent]]);
  const premise = rule[1].substitute(theta);
  return premise;
});

benchmark('context manipulation', () => {
  const seq = Sequent.copy(baseSeq);
  Sequent.add_to_antecedent_bulk(seq, formulas);
  Sequent.remove_from_antecedent(seq, toRemove);
  return seq;
});
```

#### Category 3: Proof Search Benchmarks

Full proof search with varying complexity:

```javascript
const proofBenchmarks = [
  // Trivial
  { name: 'identity', formula: '-- : A |- -- : A' },

  // Simple
  { name: 'modus-ponens', formula: '-- : P, -- : P -o Q |- -- : Q' },
  { name: 'tensor-comm', formula: '-- : P * Q |- -- : Q * P' },

  // Medium
  { name: 'currying', formula: '-- : (A * B) -o C |- -- : A -o (B -o C)' },
  { name: 'distribution', formula: '-- : P -o (R & Q) |- -- : (P -o Q) & (P -o R)' },

  // Complex
  { name: 'nested-tensor', formula: '-- : ((A * B) * C) * D |- -- : A * (B * (C * D))' },
  { name: 'deep-loli', formula: '-- : A -o (B -o (C -o (D -o E))) |- -- : A * B * C * D -o E' },

  // Stress test
  { name: 'with-explosion', formula: '-- : (A & B) * (C & D) * (E & F) |- -- : A * C * E' },
];

for (const { name, formula } of proofBenchmarks) {
  benchmark(`proof: ${name}`, () => proveFormula(formula));
}
```

### 4.4 Metrics to Collect

For each benchmark:

1. **Time:** Mean, median, std dev, min, max
2. **Operations:** Count of key operations (mgu calls, substitutions, etc.)
3. **Memory:** Heap used before/after, allocations
4. **Cache:** (If implementing interning) Hit/miss ratio

```javascript
class BenchmarkResult {
  constructor() {
    this.times = [];
    this.ops = { mgu: 0, substitute: 0, copy: 0, hash: 0 };
    this.memory = { before: 0, after: 0 };
  }

  stats() {
    const sorted = [...this.times].sort((a, b) => a - b);
    return {
      mean: this.times.reduce((a, b) => a + b) / this.times.length,
      median: sorted[Math.floor(sorted.length / 2)],
      stdDev: this.stdDev(),
      min: sorted[0],
      max: sorted[sorted.length - 1],
      p95: sorted[Math.floor(sorted.length * 0.95)],
      ops: this.ops,
      memory: this.memory.after - this.memory.before,
    };
  }
}
```

### 4.5 Instrumentation Strategy

Add counters without significant overhead:

```javascript
// Global counters (disabled in production)
const counters = {
  mgu: 0,
  substitute: 0,
  copy: 0,
  hash: 0,
  toString: 0,
};

// Conditional instrumentation
const INSTRUMENT = process.env.CALC_INSTRUMENT === '1';

function mgu(pairs) {
  if (INSTRUMENT) counters.mgu++;
  // ... existing code
}

// Reset between benchmarks
function resetCounters() {
  for (const key of Object.keys(counters)) {
    counters[key] = 0;
  }
}
```

---

## Part 5: Proposed Benchmark Suite

### 5.1 Directory Structure

```
benchmarks/
├── micro/
│   ├── node.bench.js       # Node operations
│   ├── sequent.bench.js    # Sequent operations
│   ├── mgu.bench.js        # Unification
│   └── substitute.bench.js # Substitution
├── component/
│   ├── rule-apply.bench.js # Rule application cycle
│   └── context.bench.js    # Context manipulation
├── proof/
│   ├── simple.bench.js     # Simple proofs
│   ├── medium.bench.js     # Medium complexity
│   └── stress.bench.js     # Stress tests
├── fixtures/
│   ├── nodes.js            # Pre-built node fixtures
│   ├── sequents.js         # Pre-built sequent fixtures
│   └── formulas.js         # Test formula strings
├── lib/
│   ├── runner.js           # Benchmark runner
│   ├── reporter.js         # Results formatting
│   └── instrument.js       # Instrumentation helpers
├── results/
│   └── .gitkeep            # Store benchmark results
└── run.js                  # Main entry point
```

### 5.2 Benchmark Runner Implementation

```javascript
// benchmarks/lib/runner.js
const { performance } = require('perf_hooks');

class BenchmarkRunner {
  constructor(options = {}) {
    this.warmupIterations = options.warmup || 100;
    this.measureIterations = options.iterations || 1000;
    this.gcBetweenRuns = options.gc && global.gc;
  }

  async run(name, fn) {
    // Warmup
    for (let i = 0; i < this.warmupIterations; i++) {
      fn();
    }

    // Force GC
    if (this.gcBetweenRuns) global.gc();

    // Measure
    const times = [];
    const memBefore = process.memoryUsage().heapUsed;

    for (let i = 0; i < this.measureIterations; i++) {
      const start = performance.now();
      fn();
      times.push(performance.now() - start);
    }

    const memAfter = process.memoryUsage().heapUsed;

    return {
      name,
      times,
      memory: memAfter - memBefore,
      stats: this.computeStats(times),
    };
  }

  computeStats(times) {
    const sorted = [...times].sort((a, b) => a - b);
    const sum = times.reduce((a, b) => a + b, 0);
    const mean = sum / times.length;
    const variance = times.reduce((a, t) => a + (t - mean) ** 2, 0) / times.length;

    return {
      mean: mean.toFixed(4),
      median: sorted[Math.floor(sorted.length / 2)].toFixed(4),
      stdDev: Math.sqrt(variance).toFixed(4),
      min: sorted[0].toFixed(4),
      max: sorted[sorted.length - 1].toFixed(4),
      p95: sorted[Math.floor(sorted.length * 0.95)].toFixed(4),
      opsPerSec: Math.floor(1000 / mean),
    };
  }
}

module.exports = { BenchmarkRunner };
```

### 5.3 Example Micro-benchmark

```javascript
// benchmarks/micro/mgu.bench.js
const { BenchmarkRunner } = require('../lib/runner');
const mgu = require('../../lib/mgu');
const { simpleNode, complexNode, deepNode } = require('../fixtures/nodes');

async function main() {
  const runner = new BenchmarkRunner({ warmup: 100, iterations: 10000 });

  const results = [];

  // Simple unification (matching atoms)
  results.push(await runner.run('mgu: identical atoms', () => {
    mgu([[simpleNode.a, simpleNode.a]]);
  }));

  // Unification with variables
  results.push(await runner.run('mgu: var → term', () => {
    mgu([[simpleNode.varX, simpleNode.termP]]);
  }));

  // Complex unification (nested structures)
  results.push(await runner.run('mgu: nested structures (depth 3)', () => {
    mgu([[complexNode.tensor3, complexNode.tensor3Pattern]]);
  }));

  // Deep unification
  results.push(await runner.run('mgu: deep structures (depth 10)', () => {
    mgu([[deepNode.loli10, deepNode.loli10Pattern]]);
  }));

  // Failed unification
  results.push(await runner.run('mgu: fail (different constructors)', () => {
    mgu([[simpleNode.a, simpleNode.b]]);
  }));

  // Report
  console.table(results.map(r => ({
    name: r.name,
    mean: r.stats.mean + ' ms',
    median: r.stats.median + ' ms',
    stdDev: r.stats.stdDev + ' ms',
    opsPerSec: r.stats.opsPerSec,
  })));
}

main().catch(console.error);
```

### 5.4 Proof Search Benchmark

```javascript
// benchmarks/proof/simple.bench.js
const { BenchmarkRunner } = require('../lib/runner');
const { proveFormula, setupProver } = require('../lib/prover-helper');

const formulas = [
  { name: 'identity', formula: '-- : A |- -- : A' },
  { name: 'modus-ponens', formula: '-- : P, -- : P -o Q |- -- : Q' },
  { name: 'tensor-comm', formula: '-- : P * Q |- -- : Q * P' },
  { name: 'with-elim-L', formula: '-- : A & B |- -- : A' },
  { name: 'with-elim-R', formula: '-- : A & B |- -- : B' },
  { name: 'with-intro', formula: '-- : A |- -- : A & A' },
];

async function main() {
  setupProver(); // Initialize calculus

  const runner = new BenchmarkRunner({ warmup: 50, iterations: 500 });
  const results = [];

  for (const { name, formula } of formulas) {
    results.push(await runner.run(`proof: ${name}`, () => {
      proveFormula(formula);
    }));
  }

  console.table(results.map(r => ({
    name: r.name,
    mean: r.stats.mean + ' ms',
    median: r.stats.median + ' ms',
    opsPerSec: r.stats.opsPerSec,
  })));
}

main().catch(console.error);
```

### 5.5 npm Scripts

```json
{
  "scripts": {
    "bench": "node --expose-gc benchmarks/run.js",
    "bench:micro": "node --expose-gc benchmarks/run.js --category=micro",
    "bench:proof": "node --expose-gc benchmarks/run.js --category=proof",
    "bench:compare": "node benchmarks/compare.js",
    "bench:profile": "node --prof benchmarks/run.js && node --prof-process isolate-*.log"
  }
}
```

---

## Part 6: Baseline Measurements (To Be Collected)

Before any optimization, collect baseline measurements:

### 6.1 Operation-Level Baseline

| Operation | Size | Target Baseline |
|-----------|------|-----------------|
| node.copy() | depth 5 | ? μs |
| node.copy() | depth 10 | ? μs |
| node.toString() | depth 5 | ? μs |
| sha3(toString()) | depth 5 | ? μs |
| mgu (simple) | 2 nodes | ? μs |
| mgu (complex) | depth 5 | ? μs |
| substitute | depth 5 | ? μs |
| Sequent.copy | avg | ? μs |

### 6.2 Proof-Level Baseline

| Proof | Formula | Target Baseline |
|-------|---------|-----------------|
| identity | `A |- A` | ? ms |
| modus-ponens | `P, P -o Q |- Q` | ? ms |
| tensor-comm | `P * Q |- Q * P` | ? ms |
| currying | `(A*B)-oC |- A-o(B-oC)` | ? ms |
| distribution | `P-o(R&Q) |- (P-oQ)&(P-oR)` | ? ms |

---

## Part 7: Optimization Impact Projections

### 7.1 Expected Speedups from Interning

Based on complexity analysis:

| Optimization | Operations Affected | Expected Speedup |
|--------------|--------------------|--------------------|
| O(1) equality | mgu, context ops | 10-100× for large formulas |
| Structural sharing | copy, substitute | 2-10× memory, 2-5× time |
| Cached toString | rendering | 10× for repeated renders |
| Lazy hashing | context ops | 5-20× for proof search |

### 7.2 Measurement Methodology

For each optimization:

1. **Before:** Run full benchmark suite, record results
2. **After:** Run identical suite on optimized code
3. **Compare:**
   - Calculate speedup ratio: `before_time / after_time`
   - Calculate memory reduction: `(before_mem - after_mem) / before_mem`
   - Verify correctness: All proofs still succeed

---

## Part 8: Implementation Roadmap

### Phase 1: Establish Baseline (1-2 days)
- [ ] Create benchmark fixtures
- [ ] Implement micro-benchmarks
- [ ] Implement proof benchmarks
- [ ] Collect baseline measurements
- [ ] Document results

### Phase 2: Add Instrumentation (1 day)
- [ ] Add operation counters
- [ ] Profile real proof search
- [ ] Identify actual hotspots
- [ ] Validate complexity analysis

### Phase 3: Iterate on Optimizations
For each optimization:
- [ ] Implement change
- [ ] Run benchmark suite
- [ ] Compare to baseline
- [ ] Document speedup

---

## Part 9: Garbage Collection Deep Dive

### 9.1 V8 Garbage Collection Architecture

V8 uses a **generational garbage collector** with two main spaces:

**Young Generation (Scavenger):**
- **Nursery:** Initial allocation space
- **Intermediate:** Survives one GC → promoted here
- **Semi-space copying:** Fast, parallel scavenging
- Triggers: ~1-8MB allocation since last minor GC

**Old Generation (Mark-Sweep-Compact):**
- Long-lived objects promoted from young gen
- Mark phase: Traverse object graph, mark live objects
- Sweep phase: Reclaim unmarked memory
- Compact: Defragment (optional, incremental)

**Key Insight:** Most objects die young. Proof search creates many short-lived objects (Node copies, Sequent copies, intermediate strings) that are collected cheaply in the young generation. BUT: frequent minor GCs cause pause jitter.

### 9.2 Allocation Sites in CALC Proof Search

**Traced step-by-step for proving `(A * B) -o C |- A -o (B -o C)`:**

```
1. PARSING (One-time)
   ├── Parser creates AST nodes                 → O(n) Node allocations
   └── Sequent.fromTree()
       ├── new Sequent({...})                   → 1 Sequent allocation
       ├── sha3(toString()) per formula         → O(m) string allocations
       └── linear_ctx object creation           → 1 object per formula

2. PROOF SEARCH (Per rule application)
   │
   ├── Proofstate.auto()
   │   ├── getFreeVariables()
   │   │   ├── Res.getFreeVariables() recursive → O(n) array allocations
   │   │   └── concat(), reduceRight()          → O(k) intermediate arrays
   │   │
   │   ├── getInvertableRule() / chooseFocus()
   │   │   └── Object.keys(), find()            → O(m) array allocations
   │   │
   │   └── actions = filter.map(() => ...)      → O(b) closure allocations
   │
   ├── RULE APPLICATION (Proofstate.apply)
   │   │
   │   ├── getRule(ruleName)
   │   │   └── Sequent.renameUniqueArray()
   │   │       ├── Sequent.copy() for each      → O(r) Sequent copies
   │   │       ├── Node.copy() recursive        → O(r·n) Node allocations
   │   │       └── theta array                  → O(k) pair allocations
   │   │
   │   ├── mgu([[rule.succedent, pt.succedent]])
   │   │   ├── toString() comparisons           → O(n) string per node
   │   │   ├── propagate()
   │   │   │   └── subs(v_.copy(), k, v)        → O(k·n) Node copies
   │   │   └── G.map(([l,r]) => [subs..])       → O(|G|·n) Node copies
   │   │
   │   ├── persistent_ctx copy per premise
   │   │   └── r.copy() for each                → O(p·m) Node copies
   │   │
   │   ├── pt.premisses = rule.slice(1).map()
   │   │   ├── seq.substitute(theta)            → O(r·k·n) substitutions
   │   │   └── new PT({conclusion: seq})        → O(r) PT allocations
   │   │
   │   └── copyMS(linear_ctx, rmIds)            → O(m) object copies
   │
   ├── PREMISE RECURSION (continueProof)
   │   ├── copyMS(pt.delta_in) if With_R        → O(m) per premise
   │   ├── ptp.conclusion.substitute(theta)     → O(k·n) new nodes
   │   ├── add_to_antecedent_bulk()
   │   │   └── sha3(toString()) per formula     → O(m·n) strings
   │   └── Proofstate.auto(ptp, o) RECURSE      → depth d recursion
   │
   └── BACKTRACKING (on failure)
       └── ALL allocations from failed branch → GARBAGE
           ├── PT nodes
           ├── Sequent copies
           ├── Node copies from substitutions
           └── Intermediate strings

3. IDENTITY RULES (tryIdPos / tryIdNeg)
   ├── mgu() calls                              → same as above
   ├── substitute() per theta entry             → O(k·n) copies
   └── linear_ctx_ object                       → O(1) allocation
```

### 9.3 GC Pressure Quantification

**Per rule application:**
| Allocation Type | Count | Size | Lifetime |
|-----------------|-------|------|----------|
| Node copies | O(k·n) | ~100 bytes each | Short (mgu) |
| Sequent copies | O(r) | ~500 bytes each | Short → Long |
| Strings (toString) | O(n) | ~50-200 bytes | Very short |
| Arrays (intermediate) | O(m) | ~8 bytes × length | Very short |
| PT nodes | O(r) | ~200 bytes each | Long (if success) |

**For a proof of depth d with branching b:**
- Total allocations: O(b^d × k × n)
- Failed branches contribute **100% garbage**
- Successful path: O(d × r) objects survive

**Backtracking Worst Case:**
- With additive choice (&), may try multiple branches
- Each failed branch: all allocations → young gen GC
- Example: `(A & B) * (C & D) * (E & F) |- ...` = 2³ = 8 possible paths

### 9.4 GC Overhead Measurement

**To measure GC overhead:**

```javascript
// Run with: node --expose-gc --trace-gc script.js

const startHeap = process.memoryUsage().heapUsed;
const startTime = performance.now();

// Run proof search
proveFormula(formula);

const endTime = performance.now();
const endHeap = process.memoryUsage().heapUsed;

// Force GC and measure
global.gc();
const afterGcHeap = process.memoryUsage().heapUsed;

console.log({
  proofTime: endTime - startTime,
  heapGrowth: endHeap - startHeap,
  garbage: endHeap - afterGcHeap,  // Objects created but now dead
  retained: afterGcHeap - startHeap,
});
```

**Expected pattern for proof with backtracking:**
- Many minor GCs during search (young gen)
- Large "garbage" after proof completes
- Small "retained" (just the proof tree)

---

## Part 10: Proof Search Complexity Analysis

### 10.1 Forward vs Backward Chaining

**Backward Chaining (Goal-directed):**
- Start from goal, work backward to axioms
- Pattern: "To prove G, find rule with conclusion matching G, prove premises"
- CALC: `Proofstate.auto` with `o.bwd` rules

```
Goal: P -o Q |- P -o Q

Loli_R: ?X |- -- : F?A -o F?B
        ---------------------------
        ?X, -- : F?A |- -- : F?B

Apply Loli_R backward:
  - Match goal succedent with rule conclusion
  - Generate premise: P, P -o Q |- Q
  - Recurse on premise

Complexity: O(|rules| × mgu_cost) per step
            O(b^d × |rules| × n²) total
where b = branching, d = depth, n = formula size
```

**Forward Chaining (Saturation):**
- Start from axioms, apply rules until goal reached
- Pattern: "Apply all applicable rules, add conclusions, repeat"
- CALC: `runner.js` `saturate()` function

```
Facts: P, P -o Q

Loli_L: ?X, -- : F?A -o F?B |- -- : F?C
        ?X, -- : F?B |- -- : F?C
        ---------------------------
        (premise 2)

Apply Loli_L forward:
  - Match P -o Q with F?A -o F?B
  - Match P with F?A (produces F?A = P, F?B = Q)
  - Add Q to facts

Complexity: O(|facts|² × |rules| × mgu_cost) per iteration
            Can be exponential in worst case (fact explosion)
```

**CALC uses FOCUSED proof search:**
- Hybrid: alternates inversion (forward-like) and focusing (backward-like)
- Inversion phase: eagerly apply invertible rules (deterministic)
- Focus phase: choose non-invertible rule (non-deterministic, backtrack)

### 10.2 Focused Proof Search Complexity

**Phases in CALC's focused prover:**

```
1. INVERSION PHASE (deterministic, no backtracking)
   - Apply invertible rules (negative on right, positive on left)
   - Each rule reduces formula complexity
   - Terminates when no invertible rules apply

   Complexity: O(n) rule applications
               O(n × mgu_cost) = O(n³) per inversion chain

2. FOCUS PHASE (non-deterministic, may backtrack)
   - Choose formula to focus on (multiple choices)
   - Apply focusing rule(s)
   - May need to backtrack if proof fails

   Complexity: O(m) choices where m = |linear_ctx| + 1
               Each choice: O(n³) for rule application
               Backtracking: multiply by choice tree size

3. IDENTITY RULES (atoms)
   - Match atom in context with succedent
   - O(m × mgu_cost) = O(m × n²)
```

**Total Complexity:**

```
T(sequent) = {
  If invertible rule applies:
    O(n²) + T(simpler_sequent)  -- mgu + recurse

  If focus needed:
    Σᵢ [ O(n²) + Σⱼ T(premiseⱼ) ]  -- for each choice i
    (backtrack on failure, take first success)

  If atomic:
    O(m × n²)  -- identity matching
}

Worst case: O(b^d × n²) where
  b = average branching factor (focus choices + rule alternatives)
  d = proof depth
  n = formula size

For linear logic specifically:
  - Invertible rules: O(n) depth (formula shrinks)
  - Focusing: O(m) choices per focus point
  - Proof depth: O(n) for balanced formulas

  → O(m^n × n²) worst case (exponential in formula size)
```

### 10.3 Step-by-Step Trace: Currying Proof

**Goal:** `(A * B) -o C |- A -o (B -o C)`

```
STEP 1: Inversion on (A -o (B -o C)) - RIGHT (Loli_R invertible)
  Sequent: (A * B) -o C |- A -o (B -o C)
  Rule: Loli_R
  Action:
    - mgu([[rule.succ, goal.succ]])  → θ = {F?A → A, F?B → B -o C}
    - Create premise: A, (A*B)-oC |- B -o C
  Allocations:
    - Sequent.copy() for premise
    - Node.copy() for each context formula
    - New PT node
  GC pressure: ~5-10 Node allocations

STEP 2: Inversion on (B -o C) - RIGHT (Loli_R invertible)
  Sequent: A, (A * B) -o C |- B -o C
  Rule: Loli_R
  Action:
    - mgu → θ = {F?A → B, F?B → C}
    - Create premise: B, A, (A*B)-oC |- C
  Allocations: ~5-10 Node allocations

STEP 3: No invertible rule, enter FOCUS phase
  Sequent: B, A, (A * B) -o C |- C
  Choices:
    - Focus on C (right, positive) → try Id+
    - Focus on (A*B)-oC (left, negative)

  CHOICE 1: Focus right on C
    tryIdPos: mgu C with each context formula
    - mgu(C, B) → fails
    - mgu(C, A) → fails
    - mgu(C, (A*B)-oC) → fails (different constructors)
    → FAIL, backtrack
    Allocations: ~3 mgu attempts, strings for toString
    GC: All allocations → garbage

  CHOICE 2: Focus left on (A*B)-oC
    Apply Loli_L:
    - Premise 1: B, A |- A * B  (must provide argument)
    - Premise 2: B, A, C |- C   (use result)
    Allocations: 2 new PT nodes, 2 Sequent copies

STEP 4: Prove premise B, A |- A * B
  Inversion: Tensor_R (positive on right, but context split!)
  Focus phase needed.

  FOCUS on A * B (right):
    Apply Tensor_R:
    - Premise 1: B, A |- A  (some subset)
    - Premise 2: B, A |- B  (rest)

    BUT: Must partition context! Multiple choices:
    - {A} |- A and {B} |- B  ✓
    - {B} |- A and {A} |- B  ✗
    - {A,B} |- A and {} |- B  ✗
    - etc.

    This requires SPLIT ENUMERATION (implicit in CALC via delta tracking)

STEP 5: Prove B, A, C |- C
  Focus on C (right):
    tryIdPos: mgu(C, C) → θ = []  ✓
    Identity succeeds!

TOTAL ALLOCATIONS:
  - ~6 rule applications
  - ~10-15 mgu calls
  - ~50-100 Node objects (many short-lived)
  - ~20-30 intermediate strings
  - ~6 PT nodes (final proof tree)

GC EVENTS:
  - 1 failed focus choice → minor GC trigger
  - Young gen scavenging during proof
```

### 10.4 Backtracking Patterns

**When backtracking occurs:**

1. **Focus choice fails:** Try alternative focus points
2. **Rule alternative fails:** E.g., With_L vs With_L2
3. **Resource mismatch:** Linear context not properly split
4. **Identity fails:** No matching formula in context

**GC impact of backtracking:**

```javascript
// Pseudocode showing allocation/GC pattern

function auto(pt) {
  const actions = computeChoices(pt);  // Allocates closures

  for (const action of actions) {
    // ALLOCATION POINT: Each action creates copies
    const result = action();  // May allocate O(n) objects

    if (result.success) {
      // SUCCESS: Objects become part of proof tree
      // Survive to old generation eventually
      return result;
    }
    // FAILURE: All objects from action() → GARBAGE
    // Will be collected in next minor GC
  }
}
```

**Observation:** Backtracking is the primary source of short-lived garbage. Reducing backtracking OR reusing objects would significantly reduce GC pressure.

---

## Part 11: GC Optimization Strategies

### 11.1 Object Pooling

**Concept:** Pre-allocate objects, reuse instead of allocating new.

```javascript
class NodePool {
  constructor(initialSize = 1000) {
    this.pool = Array(initialSize).fill(null).map(() => new Node(-1, []));
    this.freeList = [...this.pool];
  }

  acquire(id, vals) {
    if (this.freeList.length === 0) {
      // Pool exhausted, allocate more
      const newNode = new Node(id, vals);
      this.pool.push(newNode);
      return newNode;
    }
    const node = this.freeList.pop();
    node.id = id;
    node.vals = vals;
    return node;
  }

  release(node) {
    // Clear references to allow child GC
    node.vals = [];
    this.freeList.push(node);
  }
}
```

**Challenges for CALC:**
- Nodes are trees → need recursive release
- Hard to know when node is truly unused
- Interning solves this better (shared ownership)

### 11.2 Arena Allocation (Zig-Portable Pattern)

**Concept:** Allocate in bulk, free in bulk. Perfect for proof search!

```javascript
// JavaScript simulation of arena pattern
class ProofArena {
  constructor() {
    this.nodes = [];
    this.sequents = [];
    this.strings = [];
  }

  allocNode(id, vals) {
    const node = new Node(id, vals);
    this.nodes.push(node);
    return node;
  }

  allocSequent(params) {
    const seq = new Sequent(params);
    this.sequents.push(seq);
    return seq;
  }

  reset() {
    // For a failed proof branch, just drop references
    this.nodes = [];
    this.sequents = [];
    this.strings = [];
    // All objects become garbage, collected in batch
  }
}

// Usage in proof search
function autoWithArena(pt, arena = new ProofArena()) {
  // All allocations go through arena
  const result = tryProof(pt, arena);

  if (!result.success) {
    arena.reset();  // Bulk "free" on failure
    return null;
  }

  return result;  // Arena objects survive
}
```

**Benefits:**
- Bulk deallocation matches backtracking pattern
- Reduces GC fragmentation
- Maps directly to Zig's `ArenaAllocator`

### 11.3 Interning (Best for CALC)

**Concept:** Deduplicate, share structure, enable O(1) equality.

```javascript
class InternedNode {
  constructor(id, ruleId, children) {
    this.id = id;           // Unique integer ID
    this.ruleId = ruleId;   // Rule type
    this.children = children; // Array of child IDs (integers)
  }
}

class NodeInterner {
  constructor() {
    this.nextId = 0;
    this.table = new Map();  // key → id
    this.nodes = [];         // id → InternedNode
  }

  intern(ruleId, children) {
    const key = `${ruleId}:${children.join(',')}`;

    if (this.table.has(key)) {
      return this.table.get(key);  // Reuse existing
    }

    const id = this.nextId++;
    const node = new InternedNode(id, ruleId, children);
    this.table.set(key, id);
    this.nodes[id] = node;
    return id;
  }

  get(id) {
    return this.nodes[id];
  }
}
```

**GC benefits of interning:**
- Structural sharing → fewer allocations
- Identical subtrees share memory
- No "copies" needed → O(1) instead of O(n)
- Objects live in old generation (long-lived)

### 11.4 Reducing toString() Allocations

**Current:** `sha3(ast.toString())` creates new string every time.

**Optimization: Cached toString + lazy computation**

```javascript
class CachedNode {
  constructor(id, vals) {
    this.id = id;
    this.vals = vals;
    this._stringCache = null;
    this._hashCache = null;
  }

  toString() {
    if (this._stringCache === null) {
      this._stringCache = this._computeString();
    }
    return this._stringCache;
  }

  get hash() {
    if (this._hashCache === null) {
      this._hashCache = sha3(this.toString());
    }
    return this._hashCache;
  }
}
```

**With interning, even better:**
- ID IS the identity → no hashing needed
- toString only for display, not comparison

---

## Part 12: Zig-Portable Architecture Design

### 12.1 Design Goals

1. **Shared data structures:** Same logical structure in JS and Zig
2. **Explicit memory management:** No hidden allocations
3. **Arena-friendly:** Bulk allocation/deallocation
4. **Interning-compatible:** Integer IDs, array storage

### 12.2 Core Data Structures

**Node (both JS and Zig):**

```javascript
// JavaScript version
class Node {
  constructor(ruleId, children) {
    this.ruleId = ruleId;      // u32 in Zig
    this.children = children;  // Array of node IDs (u32[])
  }
}
```

```zig
// Zig version
const Node = struct {
    rule_id: u32,
    children: []u32,  // Slice of child IDs
};
```

**Interner:**

```javascript
// JavaScript
class Interner {
  constructor() {
    this.nodes = [];           // id → Node
    this.table = new Map();    // key → id
  }
}
```

```zig
// Zig
const Interner = struct {
    nodes: std.ArrayList(Node),
    table: std.StringHashMap(u32),
    arena: std.heap.ArenaAllocator,

    pub fn intern(self: *Interner, rule_id: u32, children: []const u32) u32 {
        // ... implementation
    }
};
```

**Sequent:**

```javascript
// JavaScript
class Sequent {
  constructor() {
    this.linear_ctx = {};      // Map<string, {num, nodeId}>
    this.persistent_ctx = {};  // Map<string, nodeId>
    this.succedent = 0;        // node ID (u32)
  }
}
```

```zig
// Zig
const Sequent = struct {
    linear_ctx: std.AutoHashMap(u32, CtxEntry),
    persistent_ctx: std.AutoHashMap(u32, u32),
    succedent: u32,
};

const CtxEntry = struct {
    num: u32,
    node_id: u32,
};
```

### 12.3 Memory Management Strategy

**JavaScript (current):**
- V8 GC handles everything
- No explicit memory management
- GC pressure from short-lived objects

**JavaScript (optimized):**
- Interning reduces allocations dramatically
- Arena pattern for proof search branches
- Object pooling for hot paths

**Zig (future port):**
- Arena allocator for proof search
- Reset arena on backtrack (O(1) bulk free)
- Interner with arena backing

```zig
// Zig proof search with arena
pub fn prove(allocator: std.mem.Allocator, goal: Sequent) !?ProofTree {
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();  // Free everything when done

    const arena_alloc = arena.allocator();
    var interner = Interner.init(arena_alloc);

    return try autoSearch(&interner, goal, arena_alloc);
}

fn autoSearch(interner: *Interner, seq: Sequent, alloc: std.mem.Allocator) !?ProofTree {
    // All allocations use arena
    // On backtrack: allocations abandoned, freed at end
    // On success: proof tree returned, arena freed after extraction
}
```

### 12.4 Migration Path

**Phase 1: JS with Interning**
- Implement `NodeInterner` in JavaScript
- Refactor `Node`, `Sequent` to use integer IDs
- Measure speedup

**Phase 2: JS with Arena Pattern**
- Implement `ProofArena` class
- Pass arena through proof search
- Reset on backtrack

**Phase 3: Zig Core**
- Port `Interner`, `Sequent`, `mgu` to Zig
- Use `ArenaAllocator` natively
- Call from JS via WASM or FFI

**Phase 4: Hybrid System**
- JS for UI, parsing, interactive use
- Zig for heavy proof search
- Communication via integer IDs (serialization-free)

### 12.5 Expected Performance

| Metric | Current JS | Optimized JS | Zig |
|--------|-----------|--------------|-----|
| Allocation rate | High | Low | Minimal |
| GC pauses | Frequent | Rare | None |
| Memory usage | High (copies) | Low (sharing) | Minimal |
| Equality check | O(n) | O(1) | O(1) |
| Backtrack cost | High (GC) | Medium (arena reset) | Low (arena reset) |

---

## Part 13: GC Benchmarking

### 13.1 Measuring GC Impact

```javascript
// Run with: node --expose-gc --trace-gc benchmarks/gc-analysis.js

const { performance } = require('perf_hooks');

function measureGC(fn, iterations = 100) {
  const results = {
    times: [],
    heapGrowth: [],
    garbage: [],
    gcEvents: 0,
  };

  // Hook into GC events
  const gcCallback = () => { results.gcEvents++; };
  // Note: require('perf_hooks').monitorEventLoopDelay for more detail

  for (let i = 0; i < iterations; i++) {
    global.gc();  // Start clean
    const heapBefore = process.memoryUsage().heapUsed;

    const start = performance.now();
    fn();
    const elapsed = performance.now() - start;

    const heapAfter = process.memoryUsage().heapUsed;
    global.gc();
    const heapAfterGC = process.memoryUsage().heapUsed;

    results.times.push(elapsed);
    results.heapGrowth.push(heapAfter - heapBefore);
    results.garbage.push(heapAfter - heapAfterGC);
  }

  return {
    meanTime: results.times.reduce((a, b) => a + b) / iterations,
    meanHeapGrowth: results.heapGrowth.reduce((a, b) => a + b) / iterations,
    meanGarbage: results.garbage.reduce((a, b) => a + b) / iterations,
    gcEvents: results.gcEvents,
  };
}
```

### 13.2 GC-Specific Benchmarks

```javascript
// benchmarks/gc/backtracking.bench.js

// Measure GC impact of backtracking
const formulas = {
  noBacktrack: '-- : A |- -- : A',  // Direct identity
  lightBacktrack: '-- : A & B |- -- : A',  // One choice
  heavyBacktrack: '-- : (A & B) * (C & D) |- -- : A * C',  // Many choices
};

for (const [name, formula] of Object.entries(formulas)) {
  const result = measureGC(() => proveFormula(formula));
  console.log(`${name}:`);
  console.log(`  Time: ${result.meanTime.toFixed(2)} ms`);
  console.log(`  Heap growth: ${(result.meanHeapGrowth / 1024).toFixed(1)} KB`);
  console.log(`  Garbage: ${(result.meanGarbage / 1024).toFixed(1)} KB`);
}
```

---

## Part 14: Merkle-DAG Hash Consing Impact Analysis

This section analyzes the complexity changes when migrating from the current implementation to Merkle-DAG Hash Consing with arena-scoped memory management.

### 14.1 Atomic Operations: Current vs Merkle-DAG

#### Node Operations (lib/node.js → MerkleInterner)

| Operation | Current Code | Current Complexity | Merkle-DAG | New Complexity | Improvement |
|-----------|-------------|-------------------|------------|----------------|-------------|
| **Create** | `new Node(id, vals)` | O(1) | `interner.intern(node)` | O(k) lookup + O(1) store | Slightly slower (hash) |
| **Copy** | `node.copy()` recursive | O(n) | Return hash (immutable) | **O(1)** | **n× faster** |
| **Equality** | `t0.toString() === t1.toString()` | O(n) + O(n) = O(n) | `hashA === hashB` | **O(1)** | **n× faster** |
| **toString** | Rebuild string each call | O(n) | Cached after first call | O(1) amortized | **n× faster** |
| **isVar** | `isFreevar(rules[id].ruleName)` | O(1) | Same | O(1) | Same |

**Code trace — Current `copy()`:**
```javascript
// lib/node.js:23-26
copy() {
  return new Node(this.id,
    this.vals.map(v => (typeof v === "object") ? v.copy() : v))  // O(n) recursive
}
```

**Merkle-DAG equivalent:**
```javascript
// "Copy" is just returning the hash - data is immutable and shared
copy(hash) {
  return hash;  // O(1)
}
```

#### Sequent Operations (lib/sequent.js)

| Operation | Current Code | Current Complexity | Merkle-DAG | New Complexity | Improvement |
|-----------|-------------|-------------------|------------|----------------|-------------|
| **Context key** | `sha3(ast.toString())` | O(n) hash + O(n) string | Use formula hash directly | **O(1)** | **n× faster** |
| **add_to_linear_ctx** | Hash + store | O(n) | Store hash | **O(1)** | **n× faster** |
| **Sequent.copy** | Deep copy all formulas | O(m·n) | Copy hash references | **O(m)** | **n× faster** |
| **substitute** | `substitute(val, k, v)` per formula | O(m·k·n) | Create new interned nodes | O(m·k) amortized* | **n× faster** |
| **getFreeVariables** | Traverse all | O(m·n) | Cache per hash | O(m) amortized | **n× faster** |
| **renameUnique** | Copy + substitute | O(m·n + m·k·n) | Intern new vars | O(m·k) | **n× faster** |

*Substitution still traverses, but identical subtrees are found in interner → O(1) per shared subtree.

**Code trace — Current `add_to_linear_ctx`:**
```javascript
// lib/sequent.js:254-261
Sequent.add_to_linear_ctx = function (seq, ast, num = 1) {
  let id = sha3(ast.toString())  // O(n) toString + O(n) sha3
  if(id in seq.linear_ctx) {
    seq.linear_ctx[id].num += num;
  } else {
    seq.linear_ctx[id] = {num: num, val: ast}
  }
}
```

**Merkle-DAG equivalent:**
```javascript
Sequent.add_to_linear_ctx = function (seq, hash, num = 1) {
  // hash already computed during interning
  if(hash in seq.linear_ctx) {
    seq.linear_ctx[hash].num += num;
  } else {
    seq.linear_ctx[hash] = {num: num, hash: hash}  // O(1)
  }
}
```

#### Unification Operations (lib/mgu.js)

| Operation | Current Code | Current Complexity | Merkle-DAG | New Complexity | Improvement |
|-----------|-------------|-------------------|------------|----------------|-------------|
| **Equality check** | `t0.toString() === t1.toString()` | O(n) | `hash0 === hash1` | **O(1)** | **n× faster** |
| **Propagate** | `subs(v_.copy(), k, v)` per theta | O(k·n) | Intern substituted | O(k) amortized | **n× faster** |
| **Apply to G** | `G.map(([l,r]) => [subs(l,t0,t1), subs(r,t0,t1)])` | O(\|G\|·n) | Intern each result | O(\|G\|) amortized | **n× faster** |
| **Overall mgu** | Loop × above | O(k²·n) worst | Loop × above | **O(k²)** amortized | **n× faster** |

**Code trace — Current critical path:**
```javascript
// lib/mgu.js:23
let isEq = t0.toString() === t1.toString();  // O(n) every iteration!

// lib/mgu.js:36
G = G.map(([l, r]) => ([subs(l, t0, t1), subs(r, t0, t1)]))  // O(|G|·n) copies
```

**Merkle-DAG equivalent:**
```javascript
let isEq = hash0 === hash1;  // O(1)

G = G.map(([l, r]) => ([
  interner.substitute(l, t0Hash, t1Hash),  // Returns new hash, shares subtrees
  interner.substitute(r, t0Hash, t1Hash)
]))
```

#### Substitution Operations (lib/substitute.js)

| Operation | Current Code | Current Complexity | Merkle-DAG | New Complexity | Notes |
|-----------|-------------|-------------------|------------|----------------|-------|
| **Match check** | `node.id === key.id && node.vals[0] === key.vals[0]` | O(1) | Compare hashes | O(1) | Same |
| **Return value** | `val.copy()` | O(n) | Return hash | **O(1)** | **n× faster** |
| **Recurse** | `sub(v, key, val)` for each child | O(n) total | Intern result | O(k) + cache | Shared subtrees |

**Code trace — Current:**
```javascript
// lib/substitute.js:17-18
if(isSameConstructor && node.vals[0] === key.vals[0]) {
  return val.copy();  // O(n) EVERY substitution match
}
```

**Merkle-DAG equivalent:**
```javascript
if(nodeHash === keyHash) {
  return valHash;  // O(1) - just return the hash
}
// Recurse and intern result - subtrees are looked up, not copied
return interner.intern(node.ruleId, substitutedChildHashes);
```

### 14.2 Compound Operations: Current vs Merkle-DAG

#### Rule Application (lib/proofstate.js:360-428)

**Current flow:**
```
apply(pt, rule_name, id, rule)
  1. Copy persistent_ctx for each premise     → O(p·m·n)
  2. mgu([[rule.succedent, pt.succedent]])    → O(k²·n)
  3. mgu([[rule.ctx, pt.ctx]])                → O(k²·n)
  4. seq.substitute(theta) for each premise   → O(p·k·n)
  5. new PT({conclusion: seq})                → O(p)
  6. copyMS(linear_ctx)                       → O(m)

  Total: O(p·m·n + k²·n + p·k·n) = O((p·m + k²)·n)
```

**Merkle-DAG flow:**
```
apply(pt, rule_name, id, rule)
  1. Copy persistent_ctx (hash refs only)     → O(p·m)
  2. mgu (hash comparisons)                   → O(k²)
  3. mgu (hash comparisons)                   → O(k²)
  4. substitute (returns new hashes)          → O(p·k)
  5. new PT({conclusion: seqHash})            → O(p)
  6. copyMS(linear_ctx hashes)                → O(m)

  Total: O(p·m + k² + p·k) = O(p·(m+k) + k²)
```

**Improvement: O(n) factor eliminated from all terms.**

#### Identity Rules (tryIdPos/tryIdNeg)

**Current flow:**
```
tryIdPos(pt, state)
  1. For each ctx formula:
     - mgu([[ctxFormula, formula]])           → O(n²) per formula
  2. substitute(succedent, k, v) per theta    → O(k·n)
  3. Sequent.remove_from_antecedent()         → O(m)

  Worst case (all formulas checked): O(m·n² + k·n)
```

**Merkle-DAG flow:**
```
tryIdPos(pt, state)
  1. For each ctx formula:
     - Compare hashes first (often sufficient) → O(1)
     - If potential match, mgu on hashes       → O(k²)
  2. substitute returns new hash               → O(k)
  3. remove_from_antecedent (hash keys)        → O(m)

  Average case: O(m + k²)  (hash comparison filters most)
  Worst case: O(m·k² + k)
```

**Improvement: O(n²) → O(k²), and often O(1) due to hash filtering.**

#### Proof Search Step (Proofstate.auto)

**Current per-step:**
```
auto(pt, o)
  1. getFreeVariables(pt.conclusion)          → O(m·n)
  2. getInvertibleRule() - check polarities   → O(m)
  3. Either:
     a. apply() for invertible rule           → O((p·m + k²)·n)
     b. focus() choices loop                  → O(c × below)
        - tryIdPos/tryIdNeg                   → O(m·n² + k·n)
        - OR apply focused rule               → O((p·m + k²)·n)
  4. For each premise, recurse                → O(p × auto(...))
  5. theta propagation                        → O(k²·n)
  6. add_to_antecedent_bulk()                 → O(m·n)
  7. remove_structural_variables()            → O(m)

  Per step: O(m·n + (p·m + k² + c·m)·n + k²·n + m·n)
          = O((m + p·m + k² + c·m + k² + m)·n)
          = O((m·(2 + p + c) + 2k²)·n)
```

**Merkle-DAG per-step:**
```
auto(pt, o)
  1. getFreeVariables (cached per hash)       → O(m) or O(1) cache hit
  2. getInvertibleRule()                      → O(m)
  3. Either:
     a. apply() for invertible rule           → O(p·m + k²)
     b. focus() choices loop                  → O(c × below)
        - tryIdPos/tryIdNeg                   → O(m + k²)
        - OR apply focused rule               → O(p·m + k²)
  4. For each premise, recurse                → O(p × auto(...))
  5. theta propagation                        → O(k²)
  6. add_to_antecedent_bulk()                 → O(m)
  7. remove_structural_variables()            → O(m)

  Per step: O(m + m + p·m + k² + c·(m + k²) + k² + m + m)
          = O(m·(4 + p + c) + k²·(2 + c))
```

**Improvement: O(n) factor eliminated entirely. Per-step goes from O((m·p + k²)·n) to O(m·p + k²).**

### 14.3 Proof Search Complexity: Full Analysis

For a proof with:
- d = depth
- b = branching factor (focus choices + rule alternatives)
- m = average context size
- n = average formula size
- k = average variables per rule

**Current:**
```
T_current = O(b^d × step_cost)
          = O(b^d × (m·p + k²)·n)
          = O(b^d · n · (m·p + k²))
```

**Merkle-DAG:**
```
T_merkle = O(b^d × step_cost)
         = O(b^d × (m·p + k²))
         = O(b^d · (m·p + k²))
```

**Speedup factor: O(n)** — the average formula size is eliminated from the complexity.

For typical proofs:
- n = 10-50 (formula size)
- Expected speedup: **10-50×** on proof search

### 14.4 Memory and Allocation Analysis

#### Current: Allocations per Proof Step

| Allocation Site | Objects | Size (bytes) | Lifetime |
|-----------------|---------|--------------|----------|
| `node.copy()` per formula | O(m·n) | ~100 each | Short |
| `Sequent.copy()` | O(1) | ~500 | Medium |
| `toString()` strings | O(m·n) | ~50-200 | Very short |
| `sha3()` result strings | O(m) | 64 | Very short |
| Intermediate arrays | O(m + k) | Variable | Very short |
| `new PT()` per premise | O(p) | ~200 | Long (if success) |

**Total per step:** O(m·n + m·n + m + m + p) = O(m·n) allocations

**For proof of depth d with branching b:**
- Total allocations: O(b^d · m · n)
- On backtrack: 100% of branch allocations → garbage

#### Merkle-DAG: Allocations per Proof Step

| Allocation Site | Objects | Size (bytes) | Lifetime |
|-----------------|---------|--------------|----------|
| `intern()` new nodes | O(k) (only new) | ~50 each | Long (deduplicated) |
| Hash references | O(m) | 8 each (bigint) | Medium |
| Sequent shells | O(1) | ~100 | Medium |
| `new PT()` per premise | O(p) | ~200 | Long (if success) |

**Total per step:** O(k + m + 1 + p) = O(m + k) allocations

**For proof of depth d with branching b:**
- Total allocations: O(b^d · (m + k))
- Deduplicated via interning: Actual ≪ theoretical
- With arena: O(1) bulk discard on backtrack

**Allocation reduction: O(n) factor eliminated, plus deduplication.**

### 14.5 Garbage Collection: Current vs Arena

#### Current GC Pattern

```
Proof Search:
  Step 1: Allocate O(m·n) objects
    └── Minor GC triggered (~1MB threshold)
  Step 2: Allocate O(m·n) objects
    └── Some objects promoted to old gen
  ...
  Backtrack: All branch objects → garbage
    └── Minor GC collects young gen
    └── Eventually major GC for old gen

  GC Events: ~1 minor GC per step
  GC Time: ~1-5ms per minor, ~10-50ms per major
```

**Problem:** Constant GC pressure, unpredictable pauses.

#### Merkle-DAG + Arena GC Pattern

```
Proof Search with Arenas:
  Root Interner: (never collected during search)
    └── Contains base formulas from goal
    └── Grows monotonically, but slowly (deduplicated)

  Branch Arena A:
    Step 1: Intern O(k) nodes → arena local store
    Step 2: Intern O(k) nodes → arena local store
    ...
    Backtrack: arena.discard() → O(1), no GC

  Branch Arena B:
    Step 1: Intern O(k) nodes → arena local store
    ...
    Success: arena.commit() → O(|local|) merge to parent

  GC Events: Near zero during search
  GC Time: Bulk free on discard, minimal pause
```

#### Arena Operations Complexity

| Operation | Complexity | GC Impact |
|-----------|------------|-----------|
| `arena.fork()` | O(1) | Creates empty local map |
| `arena.intern(node)` | O(k) + O(1) lookup chain | No GC (local allocation) |
| `arena.discard()` | O(1) | No GC (drop reference) |
| `arena.commit()` | O(\|local\|) | No GC (merge hashes) |

**Implementation:**
```javascript
class ArenaInterner {
  constructor(parent = null) {
    this.parent = parent;
    this.local = new Map();  // hash → NodeData
  }

  intern(node) {
    const hash = this.computeHash(node);

    // Check parent chain (O(depth) but depth is small)
    let current = this;
    while (current) {
      if (current.local.has(hash)) return hash;
      current = current.parent;
    }

    // Store locally (no parent modification)
    this.local.set(hash, nodeData);
    return hash;
  }

  fork() {
    return new ArenaInterner(this);  // O(1)
  }

  commit() {
    // Merge local into parent
    if (this.parent) {
      for (const [hash, data] of this.local) {
        this.parent.local.set(hash, data);  // O(|local|)
      }
    }
  }

  discard() {
    // Just drop reference - GC handles it later in bulk
    this.local = null;  // O(1)
  }
}
```

#### GC Comparison Summary

| Metric | Current | Merkle-DAG + Arena |
|--------|---------|-------------------|
| Allocations per step | O(m·n) | O(m + k) |
| Minor GC frequency | Every few steps | Near zero |
| Major GC frequency | Occasional | Very rare |
| Backtrack cost | GC collects O(branch_size) | O(1) discard |
| Memory fragmentation | High (many small objects) | Low (arena blocks) |
| Pause predictability | Unpredictable | Predictable |

### 14.6 Complexity Summary Table

| Operation | Current | Merkle-DAG | Speedup |
|-----------|---------|------------|---------|
| Node.copy() | O(n) | O(1) | **n×** |
| Node equality | O(n) | O(1) | **n×** |
| Node.toString() | O(n) | O(1)* | **n×** |
| Context key | O(n) | O(1) | **n×** |
| Sequent.copy() | O(m·n) | O(m) | **n×** |
| Sequent.substitute() | O(m·k·n) | O(m·k) | **n×** |
| mgu() | O(k²·n) | O(k²) | **n×** |
| Rule application | O((p·m+k²)·n) | O(p·m+k²) | **n×** |
| Identity rule | O(m·n²) | O(m+k²) | **n²×** |
| Proof step | O((m·p+k²)·n) | O(m·p+k²) | **n×** |
| Full proof | O(b^d·n·(m·p+k²)) | O(b^d·(m·p+k²)) | **n×** |
| GC per step | O(m·n) objects | O(m+k) objects | **n×** |
| Backtrack | GC collects all | O(1) arena discard | **∞×** |

\* Cached after first computation

### 14.7 What We Lose

| Aspect | Current | Merkle-DAG | Trade-off |
|--------|---------|------------|-----------|
| Node creation | O(1) simple | O(k) hash + lookup | Slightly slower |
| Memory for interner | None | O(unique nodes) | Extra memory |
| Implementation complexity | Simple | Hash + arena + interner | More code |
| Debugging | Direct node inspection | Need to lookup by hash | Indirection |
| Zig port | Straightforward | Requires hash function | Need wyhash/rapidhash |

**Net assessment:** The O(n) improvement on all hot-path operations far outweighs the O(k) overhead on creation. For any non-trivial formula (n > 10), this is a significant win.

### 14.8 Estimated Real-World Impact

For the currying proof `(A * B) -o C |- A -o (B -o C)`:

| Metric | Current (estimated) | Merkle-DAG (estimated) | Improvement |
|--------|---------------------|------------------------|-------------|
| Proof steps | ~6 | ~6 | Same |
| Node copies | ~50-100 | ~0 | 100% reduction |
| String allocations | ~20-30 | ~6 (cached) | 80% reduction |
| mgu calls | ~10-15 | ~10-15 | Same count |
| mgu time | O(n²) per | O(k²) per | 10-25× faster |
| Total allocations | ~200 objects | ~30 objects | 85% reduction |
| Minor GCs | ~2-3 | 0 | 100% reduction |
| Backtrack overhead | GC pause | O(1) discard | Eliminated |

**Expected overall speedup: 10-50× depending on formula size.**

---

## Part 15: Implementation Verification Benchmarks

To verify the above analysis, implement these benchmarks:

### 15.1 Micro-benchmarks (Before/After)

```javascript
// benchmarks/merkle/equality.bench.js
const { BenchmarkRunner } = require('../lib/runner');

// Current implementation
function currentEquality(a, b) {
  return a.toString() === b.toString();
}

// Merkle-DAG implementation
function merkleEquality(hashA, hashB) {
  return hashA === hashB;
}

async function main() {
  const runner = new BenchmarkRunner({ warmup: 100, iterations: 10000 });

  // Test formulas of varying sizes
  const sizes = [5, 10, 20, 50, 100];  // Approximate node count

  for (const size of sizes) {
    const { nodeA, nodeB, hashA, hashB } = fixtures.createPair(size);

    const current = await runner.run(`current equality (n=${size})`, () => {
      currentEquality(nodeA, nodeB);
    });

    const merkle = await runner.run(`merkle equality (n=${size})`, () => {
      merkleEquality(hashA, hashB);
    });

    console.log(`Size ${size}: Current ${current.stats.mean}ms, Merkle ${merkle.stats.mean}ms`);
    console.log(`  Speedup: ${(current.stats.mean / merkle.stats.mean).toFixed(1)}×`);
  }
}
```

### 15.2 Integration Benchmarks

```javascript
// benchmarks/merkle/mgu.bench.js
async function benchmarkMGU() {
  const formulas = [
    { name: 'simple', a: 'A', b: 'A' },
    { name: 'medium', a: 'A * B -o C', b: 'X * Y -o Z' },
    { name: 'complex', a: '(A * B) -o (C & D)', b: '(X * Y) -o (Z & W)' },
  ];

  for (const { name, a, b } of formulas) {
    const nodeA = parse(a);
    const nodeB = parse(b);

    // Current
    const currentTime = benchmark(() => mgu([[nodeA, nodeB]]));

    // Merkle
    const hashA = interner.intern(nodeA);
    const hashB = interner.intern(nodeB);
    const merkleTime = benchmark(() => merkleMgu([[hashA, hashB]]));

    console.log(`${name}: ${currentTime}ms → ${merkleTime}ms (${(currentTime/merkleTime).toFixed(1)}× faster)`);
  }
}
```

### 15.3 GC Benchmarks

```javascript
// benchmarks/merkle/gc.bench.js
async function benchmarkGC() {
  const proofWithBacktracking = '-- : (A & B) * (C & D) |- -- : A * C';

  // Current - measure GC events
  global.gc();
  const beforeCurrent = process.memoryUsage().heapUsed;
  let gcEventsCurrent = 0;
  // ... run proof with GC tracking

  // Merkle + Arena - measure GC events
  global.gc();
  const beforeMerkle = process.memoryUsage().heapUsed;
  let gcEventsMerkle = 0;
  // ... run proof with arena

  console.log(`Current: ${gcEventsCurrent} GC events, ${heapGrowth}KB heap growth`);
  console.log(`Merkle:  ${gcEventsMerkle} GC events, ${heapGrowthMerkle}KB heap growth`);
}
```

---

## References

### Benchmarking
- [Benchmark.js](https://benchmarkjs.com/) — Statistical benchmarking library
- [Node.js perf_hooks](https://nodejs.org/api/perf_hooks.html) — Native performance APIs
- [V8 Performance Characteristics](https://github.com/davidmarkclements/v8-perf) — V8 optimization guide
- [The State of Benchmarking in Node.js](https://webpro.nl/articles/the-state-of-benchmarking-in-nodejs)
- [How JS Benchmarks Lie](https://medium.com/cacher-app/how-js-benchmarks-lie-fa35fa989ee0) — Pitfalls to avoid
- [micro-bmark](https://github.com/paulmillr/micro-bmark) — Nanosecond resolution benchmarking

### Garbage Collection
- [V8 Orinoco GC](https://v8.dev/blog/trash-talk) — V8's garbage collector architecture
- [V8 Parallel Scavenger](https://v8.dev/blog/orinoco-parallel-scavenger) — Young generation GC
- [Object Pooling in Games](https://gameprogrammingpatterns.com/object-pool.html) — Game programming pattern
- [Static Memory JS](https://web.dev/articles/speed-static-mem-pools) — GC-free patterns
- [Zig Allocators](https://zig.guide/standard-library/allocators/) — Arena allocator guide

### Hash Consing & Content Addressing
- [Hash consing - Wikipedia](https://en.wikipedia.org/wiki/Hash_consing) — Technique overview
- [Merkle DAG - IPFS](https://docs.ipfs.tech/concepts/merkle-dag/) — Content-addressed DAGs
- [ACL2 HONS-AND-MEMOIZATION](https://www.cs.utexas.edu/~moore/acl2/v6-3/HONS-AND-MEMOIZATION.html) — Theorem prover hash consing
- [Hash-Consing GC (Appel)](https://www.cs.princeton.edu/research/techreps/TR-412-93) — Generational integration
- [rapidhash](https://github.com/Nicoshev/rapidhash) — Fastest non-cryptographic hash
- [rapidhash-js](https://github.com/komiya-atsushi/rapidhash-js) — JavaScript implementation

### Related Systems
- [SAT Solver Memory](https://link.springer.com/chapter/10.1007/978-3-540-30494-4_20) — Memory-efficient solving
- [SMHasher](https://github.com/rurban/smhasher) — Hash function quality tests
