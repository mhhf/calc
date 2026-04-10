#!/usr/bin/env node
/**
 * ILL-native debug runner — observation directives + verbose judgment output.
 *
 * Processes #trace, #dump_state, #debug, #benchmark, #compare, #inspect
 * directives and provides enriched output for #expect* directives.
 *
 * Usage:
 *   node tools/debug-ill.js <file.ill>              # all directives
 *   node tools/debug-ill.js <file.ill> --only trace  # filter by kind
 *
 * See doc/documentation/ill-debug-framework.md.
 */

const path = require('path');
const {
  ROOT, PROGRAM, MAX_STEPS, MAX_DEPTH,
  scanDirectives, detectDuplicates, loadProgram,
  parseModality, decomposeQuery, extractGoals, buildProveOpts,
  resolveExecOpts, resolveQueryHash, normalizeLeafState,
  stateHasFreevars, isSubset,
  groupByPredicate, show, classifyLeaf, showInteresting, getAllLeaves,
  countLeaves, maxDepth, countNodes,
} = require('../lib/engine/directive-loader');

// ─── CLI ────────────────────────────────────────────────────────────────────

const args = process.argv.slice(2);
const flags = {};
const positional = [];
for (let i = 0; i < args.length; i++) {
  if (args[i] === '--only' && i + 1 < args.length) {
    flags.only = args[++i];
  } else if (args[i] === '--program' && i + 1 < args.length) {
    flags.program = args[++i];
  } else if (args[i] === '--bytecode' && i + 1 < args.length) {
    flags.bytecode = args[++i];
  } else if (args[i].startsWith('--')) {
    const [k, v] = args[i].slice(2).split('=');
    flags[k] = v || 'true';
  } else {
    positional.push(args[i]);
  }
}

if (positional.length === 0) {
  console.error('Usage: node tools/debug-ill.js <file.ill> [--only <kind>] [--program <path>]');
  process.exit(1);
}

// ─── Output Helpers ─────────────────────────────────────────────────────────

function header(kind, label) {
  const bar = '─'.repeat(Math.max(0, 70 - kind.length - label.length));
  console.log(`\n── ${kind}: ${label} ${bar}`);
}

// ─── Observation Handlers ───────────────────────────────────────────────────

/**
 * #trace — step-by-step rule/fact logging.
 * Uses the engine onStep hook for live output.
 */
function runTrace(calc, hash, settings) {
  const initial = decomposeQuery(hash);
  const eo = resolveExecOpts(settings);
  const filterRule = settings?.filter || null;

  const entries = [];
  // forward.run() emits { step }, explore() emits { depth } — coalesce via step ?? depth
  const onStep = ({ step, depth, rule, consumed, state }) => {
    if (filterRule && rule.name !== filterRule) return;
    const consumedFacts = Object.keys(consumed).map(h => show(Number(h)));
    const cls = classifyLeaf(state);
    entries.push({ pos: step ?? depth, rule: rule.name, consumed: consumedFacts, cls });
  };

  if (stateHasFreevars(initial)) {
    calc.explore(initial, { maxDepth: MAX_DEPTH, ...eo, onStep });
  } else {
    calc.exec(initial, { maxSteps: MAX_STEPS, ...eo, onStep });
  }

  if (entries.length === 0) {
    console.log('  (no steps fired)');
    return;
  }
  for (const s of entries) {
    console.log(`  step ${s.pos}: ${s.rule} — consumed: [${s.consumed.join(', ')}]`);
  }
  console.log(`  total: ${entries.length} steps`);
}

/**
 * #dump_state — grouped predicate state inspection.
 * Runs forward execution to quiescence, then dumps final state.
 */
function runDumpState(calc, hash, settings) {
  const initial = decomposeQuery(hash);
  const eo = resolveExecOpts(settings);
  const result = calc.exec(initial, { maxSteps: MAX_STEPS, ...eo });
  const state = result.state;
  const cls = classifyLeaf(state);

  console.log(`  status: ${cls} (${result.steps} steps, quiescent: ${result.quiescent})`);

  const groups = groupByPredicate(state);
  for (const [pred, facts] of [...groups.entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
    console.log(`  ${pred}: ${facts.join(', ')}`);
  }
}

/**
 * #debug — per-leaf exploration analysis.
 * Explores all paths and dumps per-leaf diagnostics.
 */
function runDebug(calc, hash, settings) {
  const initial = decomposeQuery(hash);
  const eo = resolveExecOpts(settings);
  const tree = calc.explore(initial, { maxDepth: MAX_DEPTH, ...eo });
  const leaves = getAllLeaves(tree);

  console.log(`  leaves: ${leaves.length}, depth: ${maxDepth(tree)}, nodes: ${countNodes(tree)}`);

  for (let i = 0; i < leaves.length; i++) {
    const leaf = leaves[i];
    const plain = normalizeLeafState(leaf);
    const cls = plain ? classifyLeaf(plain) : 'NO_STATE';
    const facts = plain ? showInteresting(plain, { exclude: [] }) : [];
    console.log(`  leaf ${i} [${leaf.type}/${cls}]: ${facts.join(', ') || '(empty)'}`);
  }
}

/**
 * #benchmark — warmup+N iterations with timing stats.
 */
function runBenchmark(calc, hash, settings) {
  const initial = decomposeQuery(hash);
  const iterations = settings?.iterations ? parseInt(settings.iterations, 10) : 10;
  const warmup = settings?.warmup ? parseInt(settings.warmup, 10) : 3;
  const mode = settings?.mode || 'exec';
  const eo = resolveExecOpts(settings);

  const runOnce = mode === 'explore'
    ? () => {
        const tree = calc.explore(initial, { maxDepth: MAX_DEPTH, ...eo });
        return { nodes: countNodes(tree), leaves: countLeaves(tree) };
      }
    : () => {
        const r = calc.exec(initial, { maxSteps: MAX_STEPS, ...eo });
        return { steps: r.steps, quiescent: r.quiescent };
      };

  // Warmup
  for (let i = 0; i < warmup; i++) runOnce();

  // Measure
  const times = [];
  let lastInfo;
  for (let i = 0; i < iterations; i++) {
    const t0 = performance.now();
    lastInfo = runOnce();
    times.push(performance.now() - t0);
  }
  times.sort((a, b) => a - b);

  const mean = times.reduce((a, b) => a + b) / times.length;
  const p50 = times[Math.floor(times.length / 2)];
  console.log(`  mean: ${mean.toFixed(2)}ms  p50: ${p50.toFixed(2)}ms  min: ${times[0].toFixed(2)}ms  max: ${times[times.length - 1].toFixed(2)}ms`);
  if (lastInfo) {
    const info = Object.entries(lastInfo).map(([k, v]) => `${k}: ${v}`).join(', ');
    console.log(`  ${info}`);
  }
}

/**
 * #compare — side-by-side mode comparison (e.g. FFI vs noFFI).
 */
function runCompare(calc, hash, settings) {
  const initial = decomposeQuery(hash);
  const modeA = settings?.mode_a || 'ffi';
  const modeB = settings?.mode_b || 'noffi';
  const diff = settings?.diff || 'node_count';
  const eo = resolveExecOpts(settings);

  function runMode(mode) {
    const useFFI = mode === 'ffi';
    if (stateHasFreevars(initial) || settings?.mode === 'explore') {
      const tree = calc.explore(initial, { maxDepth: MAX_DEPTH, ...eo, dangerouslyUseFFI: useFFI });
      return { nodes: countNodes(tree), leaves: countLeaves(tree) };
    } else {
      const r = calc.exec(initial, { maxSteps: MAX_STEPS, ...eo, dangerouslyUseFFI: useFFI });
      return { steps: r.steps, quiescent: r.quiescent };
    }
  }

  const a = runMode(modeA);
  const b = runMode(modeB);

  console.log(`  ${modeA}: ${JSON.stringify(a)}`);
  console.log(`  ${modeB}: ${JSON.stringify(b)}`);

  if (diff === 'node_count' && a.nodes !== undefined && b.nodes !== undefined) {
    console.log(`  diff: ${a.nodes === b.nodes ? 'MATCH' : `MISMATCH (${a.nodes} vs ${b.nodes})`}`);
  } else if (diff === 'steps' && a.steps !== undefined && b.steps !== undefined) {
    console.log(`  diff: ${a.steps === b.steps ? 'MATCH' : `MISMATCH (${a.steps} vs ${b.steps})`}`);
  }
}

/**
 * #inspect — compiled rule metadata dump.
 */
function runInspect(calc, _hash, settings) {
  const label = settings?.label || null;

  const rules = calc.forwardRules;
  const filtered = label
    ? rules.filter(r => r.sourceLabel === label || r.name === label || r.name.startsWith(label + '/'))
    : rules;

  if (filtered.length === 0) {
    console.log('  (no rules matched)');
    return;
  }

  for (const r of filtered) {
    const linCount = r.antecedent?.linear?.length || 0;
    const persCount = r.antecedent?.persistent?.length || 0;
    const slotCount = r.slots ? Object.keys(r.slots).length : 0;
    const alts = r.consequentAlts?.length || 1;
    const parts = [`${linCount} linear`, `${persCount} persistent`, `slots: ${slotCount}`];
    if (alts > 1) parts.push(`alts: ${alts}`);
    if (r.preserved?.length) parts.push(`preserved: ${r.preserved.length}`);
    console.log(`  ${r.name}: ${parts.join(', ')}`);
  }
  console.log(`  total: ${filtered.length} rules`);
}

// ─── Verbose Judgment Output ────────────────────────────────────────────────

/**
 * Verbose #expect* output — enriched trace for backward/forward judgments.
 */
function verboseJudgment(calc, kind, entry, modality) {
  if (entry.separator === '|-') {
    verboseBackward(calc, kind, entry, modality);
  } else if (entry.separator === '=>') {
    verboseForward(calc, kind, entry, modality);
  }
}

function verboseBackward(calc, kind, entry, modality) {
  const goals = extractGoals(entry.rhsHash);
  const settings = calc.querySettings.get(kind);
  const proveOpts = buildProveOpts(settings);

  const results = goals.map(g => {
    const result = calc.prove(g, proveOpts);
    const status = result.success ? 'PROVED' : 'FAILED';
    console.log(`  ${show(g)}: ${status}`);
    if (result.success && result.theta) {
      const bindings = result.theta.filter(([, v]) => v !== undefined);
      if (bindings.length > 0) {
        console.log(`    θ = { ${bindings.map(([k, v]) => `${k} ↦ ${show(v)}`).join(', ')} }`);
      }
    }
    return result;
  });

  const allSuccess = results.every(r => r.success);
  const expected = modality === 'not' ? !allSuccess : allSuccess;
  console.log(`  verdict: ${expected ? 'PASS' : 'FAIL'} (modality: ${modality})`);
}

function verboseForward(calc, kind, entry, modality) {
  const initial = decomposeQuery(entry.lhsHash);
  const pattern = decomposeQuery(entry.rhsHash);
  const settings = calc.querySettings.get(kind);
  const eo = resolveExecOpts(settings);

  if (stateHasFreevars(initial) || settings?.explore === 'true') {
    const tree = calc.explore(initial, { maxDepth: MAX_DEPTH, ...eo });
    const leaves = getAllLeaves(tree);

    console.log(`  explore: ${leaves.length} leaves, depth ${maxDepth(tree)}, ${countNodes(tree)} nodes`);

    let matchCount = 0;
    for (let i = 0; i < leaves.length; i++) {
      const leaf = leaves[i];
      if (leaf.type === 'dead' || leaf.type === 'memo') continue;
      const plain = normalizeLeafState(leaf);
      if (!plain) continue;
      const matches = isSubset(pattern, plain);
      if (matches) matchCount++;
      const cls = classifyLeaf(plain);
      const facts = showInteresting(plain, { exclude: [] });
      console.log(`  leaf ${i} [${leaf.type}/${cls}] ${matches ? '✓' : '✗'}: ${facts.join(', ') || '(empty)'}`);
    }

    const pass = modality === 'all' ? matchCount === leaves.filter(l => l.type === 'leaf').length
      : modality === 'not' ? matchCount === 0
      : matchCount > 0;
    console.log(`  verdict: ${pass ? 'PASS' : 'FAIL'} (${matchCount} matches, modality: ${modality})`);
  } else {
    const wantTrace = settings?.trace === 'true';
    const steps = wantTrace ? [] : null;
    const onStep = wantTrace
      ? ({ step, rule }) => steps.push({ step, rule: rule.name })
      : undefined;
    const result = calc.exec(initial, { maxSteps: MAX_STEPS, ...eo, ...(onStep ? { onStep } : {}) });

    if (steps) {
      for (const s of steps) console.log(`  [${s.step}] ${s.rule}`);
    }

    const state = result.state;
    const matches = isSubset(pattern, state);
    const cls = classifyLeaf(state);
    console.log(`  final [${cls}]: ${showInteresting(state, { exclude: [] }).join(', ')}`);
    console.log(`  steps: ${result.steps}, quiescent: ${result.quiescent}`);

    const pass = modality === 'all' ? matches
      : modality === 'not' ? !matches
      : matches;
    console.log(`  verdict: ${pass ? 'PASS' : 'FAIL'} (modality: ${modality})`);
  }
}

/**
 * #profile — per-predicate persistent goal breakdown.
 * Uses onProveSuccess/onProveFail hooks to show which predicates
 * are resolved by which tier (ffi/state/cache/clause) and which fail.
 *
 * Settings:
 *   mode: 'exec' (default) or 'explore'
 *   useFFI: 'true' (default) or 'false' — selects FFI vs noFFI path
 */
function runProfile(calc, hash, settings) {
  const initial = decomposeQuery(hash);
  const eo = resolveExecOpts(settings);
  const useFFI = settings?.useFFI !== 'false';
  const mode = settings?.mode || (stateHasFreevars(initial) ? 'explore' : 'exec');

  // Per-predicate tracking: { predName: { ffi, state, cache, clause, fail, nonGround, failReasons } }
  const byPred = {};
  let totalSuccess = 0, totalFail = 0, totalNonGround = 0;

  const { getPredicateHead } = require('../lib/kernel/ast');
  function getPred(goalHash) {
    return getPredicateHead(goalHash) || 'unknown';
  }
  function initPred(pred) {
    if (!byPred[pred]) byPred[pred] = { ffi: 0, state: 0, cache: 0, clause: 0, fail: 0, nonGround: 0, failReasons: {} };
  }

  const onProveSuccess = (goal, method, info) => {
    const pred = getPred(goal);
    initPred(pred);
    byPred[pred][method]++;
    if (info && !info.ground) { byPred[pred].nonGround++; totalNonGround++; }
    totalSuccess++;
  };

  const onProveFail = (goal, reason, info) => {
    const pred = getPred(goal);
    initPred(pred);
    byPred[pred].fail++;
    if (info && !info.ground) { byPred[pred].nonGround++; totalNonGround++; }
    byPred[pred].failReasons[reason] = (byPred[pred].failReasons[reason] || 0) + 1;
    totalFail++;
  };

  let steps = 0;
  const onStep = ({ step, depth }) => { steps = step ?? depth ?? steps; };

  const execOpts = {
    ...eo,
    dangerouslyUseFFI: useFFI,
    onProveSuccess,
    onProveFail,
    onStep,
  };

  // Read PROFILE data from engine if available
  const ffiProfile = require('../lib/engine/opt/ffi');
  const { getCacheProfile, resetCacheProfile } = require('../lib/engine/backward-cache');
  ffiProfile.resetProfile();
  resetCacheProfile();

  // Warmup run (no hooks — full speed, primes backward cache)
  if (mode === 'explore') {
    calc.explore(initial, { maxDepth: MAX_DEPTH, ...eo, dangerouslyUseFFI: useFFI });
  } else {
    calc.exec(initial, { maxSteps: MAX_STEPS, ...eo, dangerouslyUseFFI: useFFI });
  }
  const warmupCache = { ...getCacheProfile() };
  resetCacheProfile();
  ffiProfile.resetProfile();

  // Measured run (with hooks — bypasses compiled steps)
  const t0 = performance.now();
  if (mode === 'explore') {
    calc.explore(initial, { maxDepth: MAX_DEPTH, ...execOpts });
  } else {
    const result = calc.exec(initial, { maxSteps: MAX_STEPS, ...execOpts });
    steps = result.steps;
  }
  const elapsed = performance.now() - t0;
  const engineProfile = ffiProfile.getProfile();
  const cacheProfile = getCacheProfile();

  // Sort by total calls descending
  const entries = Object.entries(byPred)
    .map(([pred, counts]) => {
      const total = counts.ffi + counts.state + counts.cache + counts.clause + counts.fail;
      return { pred, ...counts, total };
    })
    .sort((a, b) => b.total - a.total);

  if (entries.length === 0) {
    console.log('  (no persistent goals fired)');
    return;
  }

  // Header
  const ffiLabel = useFFI ? 'ffi' : 'n/a';
  console.log(`  ${'predicate'.padEnd(24)} ${ffiLabel.padStart(6)} ${'state'.padStart(6)} ${'cache'.padStart(6)} ${'clause'.padStart(6)} ${'fail'.padStart(6)} ${'total'.padStart(6)} ${'!gnd'.padStart(5)}`);
  console.log(`  ${'─'.repeat(24)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(5)}`);

  for (const e of entries) {
    const ffiCol = useFFI ? String(e.ffi).padStart(6) : '   n/a';
    const ngCol = e.nonGround > 0 ? String(e.nonGround).padStart(5) : '    -';
    console.log(`  ${e.pred.padEnd(24)} ${ffiCol} ${String(e.state).padStart(6)} ${String(e.cache).padStart(6)} ${String(e.clause).padStart(6)} ${String(e.fail).padStart(6)} ${String(e.total).padStart(6)} ${ngCol}`);
  }

  console.log(`  ${'─'.repeat(24)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(6)} ${'─'.repeat(5)}`);
  const totalAll = totalSuccess + totalFail;
  console.log(`  ${'TOTAL'.padEnd(24)} ${String(totalSuccess).padStart(30)} ${String(totalFail).padStart(6)} ${String(totalAll).padStart(6)} ${totalNonGround > 0 ? String(totalNonGround).padStart(5) : '    -'}`);
  console.log(`  steps: ${steps}, mode: ${mode}, useFFI: ${useFFI}, elapsed: ${elapsed.toFixed(2)}ms`);
  console.log(`  cache: ${cacheProfile.hits} hits, ${cacheProfile.misses} misses, ${cacheProfile.negHits} neg-hits (warmup: ${warmupCache.hits}h/${warmupCache.misses}m/${warmupCache.negHits}n)`);
  if (engineProfile.clauseCalls > 0) {
    console.log(`  clause resolution: ${engineProfile.clauseCalls} calls, ${engineProfile.clauseTime?.toFixed(2) || 0}ms total`);
  }
}

// ─── Handler Registry ───────────────────────────────────────────────────────

const OBSERVATION_HANDLERS = {
  trace:      runTrace,
  dump_state: runDumpState,
  debug:      runDebug,
  benchmark:  runBenchmark,
  compare:    runCompare,
  inspect:    runInspect,
  profile:    runProfile,
};

/** Classify directive kind: observation, judgment, or unknown. */
function classifyDirective(kind) {
  for (const prefix of Object.keys(OBSERVATION_HANDLERS)) {
    if (kind === prefix || kind.startsWith(prefix + '_')) return 'observation';
  }
  if (kind.startsWith('expect')) return 'judgment';
  return null;
}

/** Get the observation handler name from a directive kind. */
function getObservationHandler(kind) {
  for (const prefix of Object.keys(OBSERVATION_HANDLERS)) {
    if (kind === prefix || kind.startsWith(prefix + '_')) return prefix;
  }
  return null;
}

// ─── Main ───────────────────────────────────────────────────────────────────

const filePath = path.resolve(positional[0]);
if (!filePath.endsWith('.ill')) {
  console.error('Error: expected .ill file');
  process.exit(1);
}

// Scan for ALL directives (observations + judgments)
const ALL_RE = /#(\w+)/g;
const fileDirectives = scanDirectives([filePath], ALL_RE);

// Filter to known directive kinds
for (const [file, names] of fileDirectives) {
  const filtered = new Set();
  for (const name of names) {
    if (classifyDirective(name) !== null) filtered.add(name);
  }
  if (filtered.size > 0) fileDirectives.set(file, filtered);
  else fileDirectives.delete(file);
}

if (fileDirectives.size === 0) {
  console.log('No directives found.');
  process.exit(0);
}

detectDuplicates(fileDirectives);
const programPath = flags.program ? path.resolve(flags.program) : PROGRAM;

// Bytecode specialization: --bytecode <codefile.ill> loads hex, produces grade-0 arr_get facts
let loadOpts = undefined;
if (flags.bytecode) {
  const fs = require('fs');
  const { loadBytecode, bytecodeArrGetGuard } = require('../lib/engine/ill/bytecode-loader');
  const bcPath = path.resolve(flags.bytecode);
  const bcContent = fs.readFileSync(bcPath, 'utf8');
  const hexMatch = bcContent.match(/bytecode\s+0x([0-9a-fA-F]+)/);
  if (!hexMatch) {
    console.error(`Error: no 'bytecode 0x...' found in ${bcPath}`);
    process.exit(1);
  }
  const bc = loadBytecode(hexMatch[1]);
  loadOpts = { extraGrade0Facts: bc.facts, scopeGuard: bytecodeArrGetGuard };
  console.log(`Bytecode loaded: ${hexMatch[1].length / 2} bytes, ${bc.facts.get('arr_get')?.length || 0} arr_get facts`);
}

const calc = loadProgram(programPath, fileDirectives, loadOpts);

// Process each directive
for (const [file, names] of fileDirectives) {
  const rel = path.relative(ROOT, file);
  console.log(`\n${rel}`);

  for (const kind of names) {
    const dtype = classifyDirective(kind);

    // Apply --only filter
    if (flags.only) {
      const handler = getObservationHandler(kind);
      if (handler !== flags.only && dtype !== flags.only && kind !== flags.only) continue;
    }

    if (dtype === 'observation') {
      const handlerName = getObservationHandler(kind);
      const handler = OBSERVATION_HANDLERS[handlerName];
      const settings = calc.querySettings.get(kind);

      // Observation directives use the queries map (no separator)
      let queryHash = calc.queries.get(kind);
      if (!queryHash && !settings?.query && !calc.splitQueries.has(kind)) {
        header(kind, '(not found in queries)');
        continue;
      }
      queryHash = resolveQueryHash(calc, kind, queryHash, settings);

      header(kind, handlerName);
      handler(calc, queryHash, settings);

    } else if (dtype === 'judgment') {
      const entry = calc.splitQueries.get(kind);
      if (!entry) {
        header(kind, '(not found in splitQueries)');
        continue;
      }
      const modality = parseModality(kind);
      header(kind, `${modality} ${entry.separator}`);
      verboseJudgment(calc, kind, entry, modality);
    }
  }
}
