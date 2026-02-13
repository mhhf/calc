#!/usr/bin/env node
/**
 * Comprehensive benchmark for unification and substitution optimizations
 *
 * Usage:
 *   node tests/mde/benchmark-unify-subst.js [--baseline] [--phase1] [--phase2] [--all]
 */

const { performance } = require('perf_hooks');
const path = require('path');

// ============================================================================
// CONFIGURATION
// ============================================================================

const ITERATIONS = {
  micro: 10000,    // Micro benchmarks (single operation)
  small: 1000,     // Small proof
  large: 100,      // Large proof
  full: 10         // Full EVM-style proof
};

// ============================================================================
// BASELINE IMPLEMENTATIONS (Current)
// ============================================================================

let Store, mde, buildIndex;
let originalUnify, originalApply, originalOccurs;
let legacyUnify, legacyApply;

function loadModules() {
  Store = require('../../lib/kernel/store');
  mde = require('../../lib/engine');
  const prove = require('../../lib/engine/prove');
  buildIndex = prove.buildIndex;

  const unifyMod = require('../../lib/kernel/unify');
  const substMod = require('../../lib/kernel/substitute');

  // Current default implementations (may be optimized)
  originalUnify = unifyMod.unify;
  originalApply = substMod.apply;
  originalOccurs = substMod.occurs;

  // Legacy (slow) implementations for comparison
  legacyUnify = unifyMod.unifyIdempotent;
  legacyApply = substMod.applySequential;
}

// ============================================================================
// OPTIMIZED IMPLEMENTATIONS
// ============================================================================

// --- Simultaneous Substitution ---
function applySimultaneous(h, theta) {
  if (theta.length === 0) return h;
  const varMap = new Map(theta);

  function go(hash) {
    if (varMap.has(hash)) return varMap.get(hash);
    const node = Store.get(hash);
    if (!node) return hash;
    if (node.tag === 'atom' || node.tag === 'freevar') return hash;

    let changed = false;
    const newChildren = node.children.map(c => {
      if (typeof c === 'number') {
        const nc = go(c);
        if (nc !== c) changed = true;
        return nc;
      }
      return c;
    });
    return changed ? Store.intern(node.tag, newChildren) : hash;
  }
  return go(h);
}

// --- Simultaneous + Memoization ---
function applySimultaneousMemo(h, theta) {
  if (theta.length === 0) return h;
  const varMap = new Map(theta);
  const memo = new Map();

  function go(hash) {
    if (memo.has(hash)) return memo.get(hash);
    if (varMap.has(hash)) {
      memo.set(hash, varMap.get(hash));
      return varMap.get(hash);
    }

    const node = Store.get(hash);
    if (!node) return hash;
    if (node.tag === 'atom' || node.tag === 'freevar') return hash;

    let changed = false;
    const newChildren = node.children.map(c => {
      if (typeof c === 'number') {
        const nc = go(c);
        if (nc !== c) changed = true;
        return nc;
      }
      return c;
    });

    const result = changed ? Store.intern(node.tag, newChildren) : hash;
    memo.set(hash, result);
    return result;
  }
  return go(h);
}

// --- Union-Find Unification ---
class UnionFind {
  constructor() {
    this.parent = new Map();
  }

  find(v) {
    if (!this.parent.has(v)) return v;
    const p = this.parent.get(v);
    const pNode = Store.get(p);
    // If parent is not a metavar, it's the ground binding
    if (!pNode || pNode.tag !== 'freevar' || !pNode.children[0]?.startsWith('_')) {
      return p;
    }
    // Path compression
    const root = this.find(p);
    if (root !== p) this.parent.set(v, root);
    return root;
  }

  union(v, term) {
    this.parent.set(this.find(v), term);
  }

  toTheta() {
    const theta = [];
    const seen = new Set();
    for (const [v] of this.parent) {
      if (seen.has(v)) continue;
      const root = this.find(v);
      if (root !== v) {
        theta.push([v, root]);
        seen.add(v);
      }
    }
    return theta;
  }
}

function isMetavar(h) {
  const node = Store.get(h);
  return node && node.tag === 'freevar' && node.children[0]?.startsWith('_');
}

// Standard occurs check
function occursEager(v, h) {
  if (v === h) return true;
  const node = Store.get(h);
  if (!node) return false;
  return node.children.some(c => typeof c === 'number' ? occursEager(v, c) : false);
}

// Deferred occurs check - just mark, check at end
function unionFindUnify(a, b, deferOccurs = false) {
  const uf = new UnionFind();
  const G = [[a, b]];
  const deferredChecks = [];  // For deferred occurs check

  while (G.length) {
    const [t0raw, t1raw] = G.pop();
    const t0 = uf.find(t0raw);
    const t1 = uf.find(t1raw);

    if (t0 === t1) continue;

    if (isMetavar(t0)) {
      if (deferOccurs) {
        deferredChecks.push([t0, t1]);
      } else {
        if (occursEager(t0, t1)) return null;
      }
      uf.union(t0, t1);
      continue;
    }

    if (isMetavar(t1)) {
      G.push([t1, t0]);
      continue;
    }

    const n0 = Store.get(t0);
    const n1 = Store.get(t1);
    if (!n0 || !n1) return null;

    if (n0.tag === n1.tag && n0.children.length === n1.children.length) {
      for (let i = 0; i < n0.children.length; i++) {
        const c0 = n0.children[i];
        const c1 = n1.children[i];
        if (typeof c0 === 'number' && typeof c1 === 'number') {
          G.push([c0, c1]);
        } else if (c0 !== c1) {
          return null;
        }
      }
      continue;
    }
    return null;
  }

  // Deferred occurs check at end
  if (deferOccurs) {
    for (const [v, term] of deferredChecks) {
      const resolvedTerm = uf.find(term);
      if (occursInUF(v, resolvedTerm, uf)) return null;
    }
  }

  return uf.toTheta();
}

function occursInUF(v, h, uf) {
  const resolved = uf.find(h);
  if (v === resolved) return true;
  const node = Store.get(resolved);
  if (!node) return false;
  return node.children.some(c => typeof c === 'number' ? occursInUF(v, c, uf) : false);
}

// ============================================================================
// TEST CASE BUILDERS
// ============================================================================

function buildTestCases() {
  const e = Store.intern('atom', ['e']);
  const o = Store.intern('atom', ['o']);
  const i = Store.intern('atom', ['i']);
  const plus = Store.intern('atom', ['plus']);
  const f = Store.intern('atom', ['f']);

  // Helper to build nested term
  function buildNested(depth, base = e) {
    let term = base;
    for (let j = 0; j < depth; j++) {
      term = Store.intern('app', [j % 2 === 0 ? o : i, term]);
    }
    return term;
  }

  // Helper to build app chain
  function buildApp(head, ...args) {
    let term = head;
    for (const arg of args) {
      term = Store.intern('app', [term, arg]);
    }
    return term;
  }

  const cases = {};

  // Case 1: Small unification (3 vars)
  const X = Store.intern('freevar', ['_X']);
  const Y = Store.intern('freevar', ['_Y']);
  const Z = Store.intern('freevar', ['_Z']);
  cases.smallUnify = {
    pattern: buildApp(plus, X, Y, Z),
    ground: buildApp(plus, buildNested(3), buildNested(4), buildNested(5)),
    desc: 'plus(_X,_Y,_Z) ~ plus(nested3,nested4,nested5)'
  };

  // Case 2: Medium unification (6 vars)
  const vars6 = Array.from({length: 6}, (_, i) => Store.intern('freevar', ['_V' + i]));
  cases.mediumUnify = {
    pattern: buildApp(f, ...vars6),
    ground: buildApp(f, ...vars6.map((_, i) => buildNested(3 + i))),
    desc: 'f(_V0..._V5) ~ f(nested3...nested8)'
  };

  // Case 3: Large unification (12 vars)
  const vars12 = Array.from({length: 12}, (_, i) => Store.intern('freevar', ['_W' + i]));
  cases.largeUnify = {
    pattern: buildApp(f, ...vars12),
    ground: buildApp(f, ...vars12.map((_, i) => buildNested(2 + (i % 5)))),
    desc: 'f(_W0..._W11) ~ f(nested...)'
  };

  // Case 4: Small theta application
  cases.smallApply = {
    term: buildApp(plus, X, Y),
    theta: [[X, buildNested(3)], [Y, buildNested(4)], [Z, buildNested(5)]],
    desc: 'apply([X,Y,Z→nested], plus(X,Y))'
  };

  // Case 5: Large theta application
  const largeTheta = vars12.map((v, i) => [v, buildNested(3 + (i % 4))]);
  cases.largeApply = {
    term: buildApp(f, vars12[0], vars12[5], vars12[11]),
    theta: largeTheta,
    desc: 'apply(12 bindings, f(V0,V5,V11))'
  };

  // Case 6: Deep term application
  const deepTerm = buildApp(f,
    buildApp(plus, vars12[0], vars12[1], vars12[2]),
    buildApp(plus, vars12[3], vars12[4], vars12[5]),
    buildApp(plus, vars12[6], vars12[7], vars12[8])
  );
  cases.deepApply = {
    term: deepTerm,
    theta: largeTheta,
    desc: 'apply(12 bindings, f(plus(...),plus(...),plus(...)))'
  };

  return cases;
}

// ============================================================================
// BENCHMARK RUNNERS
// ============================================================================

function benchmark(name, fn, iterations) {
  // Warmup
  for (let i = 0; i < Math.min(100, iterations); i++) fn();

  const t0 = performance.now();
  for (let i = 0; i < iterations; i++) fn();
  const t1 = performance.now();

  return {
    name,
    iterations,
    totalMs: t1 - t0,
    avgUs: ((t1 - t0) / iterations) * 1000,
    opsPerSec: Math.round(iterations / ((t1 - t0) / 1000))
  };
}

function runMicroBenchmarks(cases, implementations) {
  const results = [];

  for (const [caseName, testCase] of Object.entries(cases)) {
    console.log(`\n  ${testCase.desc}`);

    for (const [implName, impl] of Object.entries(implementations)) {
      if (caseName.includes('Unify') && impl.unify) {
        const r = benchmark(
          `${caseName}/${implName}`,
          () => impl.unify(testCase.pattern, testCase.ground),
          ITERATIONS.micro
        );
        results.push({ case: caseName, impl: implName, ...r });
        console.log(`    ${implName.padEnd(20)} ${r.avgUs.toFixed(3)}µs  (${r.opsPerSec.toLocaleString()} ops/s)`);
      }

      if (caseName.includes('Apply') && impl.apply) {
        const r = benchmark(
          `${caseName}/${implName}`,
          () => impl.apply(testCase.term, testCase.theta),
          ITERATIONS.micro
        );
        results.push({ case: caseName, impl: implName, ...r });
        console.log(`    ${implName.padEnd(20)} ${r.avgUs.toFixed(3)}µs  (${r.opsPerSec.toLocaleString()} ops/s)`);
      }
    }
  }

  return results;
}

async function runProofBenchmarks(implementations) {
  const results = [];

  // Load calc
  const calc = await mde.load([path.join(__dirname, '../../calculus/ill/programs/bin.ill')]);
  const idx = buildIndex(calc.clauses, calc.types);

  const proofCases = [
    { expr: 'plus (i (i e)) (i e) X', desc: 'plus 3 1 X (small)' },
    { expr: 'plus (o (o (i (o (i e))))) (o (i (i (o (i (i (i e))))))) X', desc: 'plus 20 118 X (large)' },
  ];

  for (const pc of proofCases) {
    const goal = await mde.parseExpr(pc.expr);
    console.log(`\n  ${pc.desc}`);

    for (const [implName, impl] of Object.entries(implementations)) {
      if (!impl.prove) continue;

      const iters = pc.desc.includes('small') ? ITERATIONS.small : ITERATIONS.large;
      const r = benchmark(
        `proof/${pc.desc}/${implName}`,
        () => impl.prove(goal, calc.clauses, calc.types, { index: idx }),
        iters
      );
      results.push({ case: pc.desc, impl: implName, ...r });
      console.log(`    ${implName.padEnd(20)} ${r.avgUs.toFixed(1)}µs  (${r.opsPerSec.toLocaleString()} ops/s)`);
    }
  }

  return results;
}

// ============================================================================
// PROOF IMPLEMENTATIONS WITH DIFFERENT UNIFY/APPLY
// ============================================================================

function createProver(unifyFn, applyFn) {
  function freshenTerm(h, counter, prefix = '') {
    const suffix = `_${prefix}${counter}`;
    const renamed = new Map();

    function go(hash) {
      const node = Store.get(hash);
      if (!node) return hash;
      if (node.tag === 'freevar') {
        const name = node.children[0];
        if (typeof name === 'string' && name.startsWith('_')) {
          if (!renamed.has(hash)) {
            renamed.set(hash, Store.intern('freevar', [name + suffix]));
          }
          return renamed.get(hash);
        }
        return hash;
      }
      let changed = false;
      const newChildren = node.children.map(c => {
        if (typeof c === 'number') {
          const nc = go(c);
          if (nc !== c) changed = true;
          return nc;
        }
        return c;
      });
      return changed ? Store.intern(node.tag, newChildren) : hash;
    }
    return go(h);
  }

  function freshenClause(clause, counter) {
    const suffix = `_c${counter}`;
    const renamed = new Map();

    function go(h) {
      const node = Store.get(h);
      if (!node) return h;
      if (node.tag === 'freevar') {
        const name = node.children[0];
        if (typeof name === 'string' && name.startsWith('_')) {
          if (!renamed.has(h)) {
            renamed.set(h, Store.intern('freevar', [name + suffix]));
          }
          return renamed.get(h);
        }
        return h;
      }
      let changed = false;
      const newChildren = node.children.map(c => {
        if (typeof c === 'number') {
          const nc = go(c);
          if (nc !== c) changed = true;
          return nc;
        }
        return c;
      });
      return changed ? Store.intern(node.tag, newChildren) : h;
    }

    return {
      head: go(clause.hash),
      premises: clause.premises.map(go)
    };
  }

  function getHead(hash) {
    let h = hash;
    while (h) {
      const node = Store.get(h);
      if (!node) return null;
      if (node.tag === 'atom') return node.children[0];
      if (node.tag === 'freevar') return null;
      if (node.tag === 'app') h = node.children[0];
      else return null;
    }
    return null;
  }

  function getFirstArgCtor(hash) {
    let h = hash, firstArg = null;
    while (h) {
      const node = Store.get(h);
      if (!node || node.tag !== 'app') break;
      firstArg = node.children[1];
      h = node.children[0];
    }
    if (!firstArg) return null;
    const argHead = getHead(firstArg);
    if (argHead) return argHead;
    const node = Store.get(firstArg);
    return (node && node.tag === 'freevar') ? '_' : null;
  }

  function getCandidates(idx, goalHash) {
    const head = getHead(goalHash);
    if (!head) return { types: [], clauses: [] };
    const fa = getFirstArgCtor(goalHash) || '_';
    const ti = idx.types[head] || {};
    const ci = idx.clauses[head] || {};
    return {
      types: [...(ti[fa] || []), ...(fa !== '_' ? ti['_'] || [] : [])],
      clauses: [...(ci[fa] || []), ...(fa !== '_' ? ci['_'] || [] : [])],
    };
  }

  return function prove(goal, clauses, types, opts = {}) {
    const maxDepth = opts.maxDepth || 100;
    const idx = opts.index || buildIndex(clauses, types);
    let freshCounter = 0;

    function search(g, theta, depth) {
      if (depth > maxDepth) return null;

      const goalInst = applyFn(g, theta);
      const { types: candTypes, clauses: candClauses } = getCandidates(idx, goalInst);

      for (const [name, typeHash] of candTypes) {
        const freshType = freshenTerm(typeHash, freshCounter++, 'a');
        const newTheta = unifyFn(freshType, goalInst);
        if (newTheta !== null) {
          return [...theta, ...newTheta];
        }
      }

      for (const [name, clause] of candClauses) {
        const { head, premises } = freshenClause(clause, freshCounter++);
        const newTheta = unifyFn(head, goalInst);
        if (newTheta === null) continue;

        let currentTheta = [...theta, ...newTheta];
        let ok = true;

        for (const premise of premises) {
          const result = search(applyFn(premise, currentTheta), currentTheta, depth + 1);
          if (result === null) { ok = false; break; }
          currentTheta = result;
        }

        if (ok) return currentTheta;
      }

      return null;
    }

    const result = search(goal, [], 0);
    return { success: result !== null, theta: result };
  };
}

// ============================================================================
// MAIN
// ============================================================================

async function main() {
  const args = process.argv.slice(2);
  const runBaseline = args.includes('--baseline') || args.includes('--all') || args.length === 0;
  const runPhase1 = args.includes('--phase1') || args.includes('--all') || args.length === 0;
  const runPhase2 = args.includes('--phase2') || args.includes('--all') || args.length === 0;

  console.log('='.repeat(70));
  console.log('UNIFICATION & SUBSTITUTION OPTIMIZATION BENCHMARK');
  console.log('='.repeat(70));

  loadModules();
  const cases = buildTestCases();

  // Build implementations to test
  const implementations = {};

  if (runBaseline) {
    // True legacy baseline (sequential apply + idempotent unify)
    implementations.legacy = {
      unify: legacyUnify,
      apply: legacyApply,
      prove: createProver(legacyUnify, legacyApply)
    };

    // Current default (should now be optimized)
    implementations.current = {
      unify: originalUnify,
      apply: originalApply,
      prove: createProver(originalUnify, originalApply)
    };
  }

  if (runPhase1) {
    implementations.simultaneous = {
      apply: applySimultaneous,
      prove: createProver(originalUnify, applySimultaneous)
    };

    implementations.unionFind = {
      unify: (a, b) => unionFindUnify(a, b, false),
      prove: createProver((a, b) => unionFindUnify(a, b, false), originalApply)
    };

    implementations.phase1Combined = {
      unify: (a, b) => unionFindUnify(a, b, false),
      apply: applySimultaneous,
      prove: createProver((a, b) => unionFindUnify(a, b, false), applySimultaneous)
    };
  }

  if (runPhase2) {
    implementations.simultMemo = {
      apply: applySimultaneousMemo,
      prove: createProver(originalUnify, applySimultaneousMemo)
    };

    implementations.ufDeferred = {
      unify: (a, b) => unionFindUnify(a, b, true),
      prove: createProver((a, b) => unionFindUnify(a, b, true), originalApply)
    };

    implementations.phase2Combined = {
      unify: (a, b) => unionFindUnify(a, b, true),
      apply: applySimultaneousMemo,
      prove: createProver((a, b) => unionFindUnify(a, b, true), applySimultaneousMemo)
    };
  }

  // Run micro benchmarks
  console.log('\n' + '─'.repeat(70));
  console.log('MICRO BENCHMARKS (isolated operations)');
  console.log('─'.repeat(70));

  const microResults = runMicroBenchmarks(cases, implementations);

  // Run proof benchmarks
  console.log('\n' + '─'.repeat(70));
  console.log('PROOF BENCHMARKS (end-to-end)');
  console.log('─'.repeat(70));

  const proofResults = await runProofBenchmarks(implementations);

  // Summary
  console.log('\n' + '='.repeat(70));
  console.log('SUMMARY');
  console.log('='.repeat(70));

  // Calculate speedups vs legacy
  const legacyProof = proofResults.find(r => r.impl === 'legacy' && r.case.includes('large'));
  if (legacyProof) {
    console.log('\nSpeedup vs legacy (plus 20 118 X):');
    for (const r of proofResults.filter(r => r.case.includes('large'))) {
      const speedup = legacyProof.avgUs / r.avgUs;
      const bar = '█'.repeat(Math.min(50, Math.round(speedup * 5)));
      console.log(`  ${r.impl.padEnd(20)} ${speedup.toFixed(2)}x  ${bar}`);
    }
  }

  const legacyApplyResult = microResults.find(r => r.impl === 'legacy' && r.case === 'largeApply');
  if (legacyApplyResult) {
    console.log('\nSpeedup vs legacy (large apply - 12 bindings):');
    for (const r of microResults.filter(r => r.case === 'largeApply')) {
      const speedup = legacyApplyResult.avgUs / r.avgUs;
      console.log(`  ${r.impl.padEnd(20)} ${speedup.toFixed(2)}x`);
    }
  }

  const legacyDeepApply = microResults.find(r => r.impl === 'legacy' && r.case === 'deepApply');
  if (legacyDeepApply) {
    console.log('\nSpeedup vs legacy (deep apply - nested term):');
    for (const r of microResults.filter(r => r.case === 'deepApply')) {
      const speedup = legacyDeepApply.avgUs / r.avgUs;
      console.log(`  ${r.impl.padEnd(20)} ${speedup.toFixed(2)}x`);
    }
  }

  const legacyUnifyResult = microResults.find(r => r.impl === 'legacy' && r.case === 'largeUnify');
  if (legacyUnifyResult) {
    console.log('\nSpeedup vs legacy (large unify - 12 vars):');
    for (const r of microResults.filter(r => r.case === 'largeUnify')) {
      const speedup = legacyUnifyResult.avgUs / r.avgUs;
      console.log(`  ${r.impl.padEnd(20)} ${speedup.toFixed(2)}x`);
    }
  }
}

main().catch(console.error);
