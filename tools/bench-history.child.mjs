// tools/bench-history.child.mjs — one e2e iteration in a cold subprocess.
//
// Written by tools/bench-history.js into each worktree (as
// `_bench_history_child.mjs`) before spawning. Executed with cwd=worktree.
//
// .mjs extension forces ESM regardless of the worktree's package.json type,
// so this file's syntax stays consistent across pre- and post-bun-migration
// commits. The historical engine itself may be CJS or ESM — `loadDefault`
// uses bun's transparent CJS↔ESM interop to load either shape.
//
// Cache modes (env BENCH_CACHE_MODE):
//   nocache     → cache:false             (no compose cache r/w)
//   cache-miss  → CALC_COMPOSE_CACHE=1    (cache dir pre-wiped → cold build)
//   cache-hit   → CALC_COMPOSE_CACHE=1    (cache dir pre-warmed → restore)
//   noopts      → cache:false, fuseBasicBlocks:false, skipSpecialize:true
//
// Emits one BENCH_E2E_<METRIC>=<value> line per metric so the parent can
// extract without phase-ordering coupling. Older commits naturally emit
// fewer lines.

import path from 'node:path';
import fs from 'node:fs';
import { performance } from 'node:perf_hooks';

async function loadDefault(spec) {
  const m = await import(spec);
  return m.default ?? m;
}

try {
  const cacheMode = process.env.BENCH_CACHE_MODE || 'nocache';

  const tReq0 = performance.now();
  // Newer commits: calculus/ill/index.js is the ILL facade (mde.load
  // requires an explicit calculusConfig since audit 2026-09-02). Older
  // commits predate it — fall back to the generic entry, whose load()
  // still defaults to ILL there.
  const mde = await loadDefault('./calculus/ill/index.js')
    .catch(() => loadDefault('./lib/engine/index.js'));
  const requireMs = performance.now() - tReq0;

  const codePath = path.join(import.meta.dirname, 'calculus/ill/programs/multisig_nocall_solc_code.ill');
  const sourcePath = path.join(import.meta.dirname, 'calculus/ill/programs/multisig_nocall_solc_symbolic.ill');

  const phases = [];
  const onPhase = (pathName, ms, meta) => phases.push(meta ? [pathName, ms, meta] : [pathName, ms]);

  const loadOpts = { onPhase };
  if (cacheMode === 'nocache' || cacheMode === 'noopts') loadOpts.cache = false;
  if (cacheMode === 'noopts') {
    loadOpts.fuseBasicBlocks = false;
    loadOpts.skipSpecialize = true;
  }

  let bytecodeMs = 0;
  try {
    // Loader moved lib/engine/ill/ → calculus/ill/lib/ (e1f05633); probe both
    // so pre-move commits keep the bytecode facts (identical workload).
    const loaderRel = ['./calculus/ill/lib/bytecode-loader.js', './lib/engine/ill/bytecode-loader.js']
      .find(p => fs.existsSync(path.join(import.meta.dirname, p)));
    if (loaderRel && fs.existsSync(codePath)) {
      const { loadBytecode, bytecodeArrGetGuard } = await loadDefault(loaderRel);
      const tBc0 = performance.now();
      const hex = fs.readFileSync(codePath, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];
      const bc = loadBytecode(hex);
      bytecodeMs = performance.now() - tBc0;
      loadOpts.extraGrade0Facts = bc.facts;
      loadOpts.scopeGuard = bytecodeArrGetGuard;
    }
  } catch (e) { /* older commit without bytecode support — run without */ }

  // tree-utils is optional; older commits emit nodes=0, branches=0.
  let treeUtils = null;
  try { treeUtils = await loadDefault('./lib/engine/tree-utils.js'); } catch {}

  const EXPLORE_OPTS = { maxDepth: 400, structuralMemo: true, dangerouslyUseFFI: true };

  const t0 = performance.now();

  const tLoad0 = performance.now();
  const calc = mde.load(sourcePath, loadOpts);
  const loadMs = performance.now() - tLoad0;

  const tDec0 = performance.now();
  const state = (mde.normalizeQuery || mde.decomposeQuery)(calc.queries.get('symex'));
  const decMs = performance.now() - tDec0;
  const stateSize = (state && state.linear ? state.linear.length : 0) + (state && state.persistent ? state.persistent.length : 0);
  phases.push(['decompose', decMs, { stateSize, linear: state && state.linear ? state.linear.length : 0, persistent: state && state.persistent ? state.persistent.length : 0 }]);

  const tExp0 = performance.now();
  const tree = calc.explore(state, EXPLORE_OPTS);
  const expMs = performance.now() - tExp0;

  const nodes = treeUtils && treeUtils.countNodes ? treeUtils.countNodes(tree) : 0;
  const branches = treeUtils && treeUtils.countLeaves ? treeUtils.countLeaves(tree) : 0;
  phases.push(['explore', expMs, { nodes, branches, maxDepth: EXPLORE_OPTS.maxDepth }]);

  const elapsed = performance.now() - t0;

  // Cache-hit detection: snapshot-restore path skips compose entirely.
  const hasComposePhase = phases.some(p => p[0] === 'load/compose' || p[0].startsWith('load/compose/'));
  const cacheHit = !hasComposePhase;

  const hasLoadPhases = phases.some(p => p[0].startsWith('load/'));
  if (hasLoadPhases) phases.unshift(['load', loadMs, {
    rules: (calc && calc.compiledRules) ? calc.compiledRules.length : 0,
    clauses: (calc && calc.clauses) ? calc.clauses.size : 0,
    definitions: (calc && calc.definitions) ? calc.definitions.size : 0,
  }]);

  process.stdout.write('BENCH_E2E_RESULT=' + elapsed + '\n');
  process.stdout.write('BENCH_E2E_LOAD=' + loadMs + '\n');
  process.stdout.write('BENCH_E2E_DECOMPOSE=' + decMs + '\n');
  process.stdout.write('BENCH_E2E_EXPLORE=' + expMs + '\n');
  process.stdout.write('BENCH_E2E_CACHEHIT=' + (cacheHit ? 1 : 0) + '\n');
  process.stdout.write('BENCH_E2E_REQUIRE=' + requireMs + '\n');
  process.stdout.write('BENCH_E2E_BYTECODE=' + bytecodeMs + '\n');
  process.stdout.write('BENCH_E2E_PHASES=' + JSON.stringify(phases) + '\n');
} catch (err) {
  process.stderr.write('E2E_CHILD_ERROR: ' + (err && err.stack || err && err.message || String(err)) + '\n');
  process.exit(1);
}
