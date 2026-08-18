// tools/bench-runtime.probe.mjs — cross-runtime cold-start probe.
//
// Spawned/bundled by tools/bench-runtime.js with CALC_ROOT pointing at the
// repository root. Loads the engine, runs one cold solc_symbolic e2e, and
// prints {runtime, loadMs, decMs, expMs, totalMs} on stdout.
//
// Designed to be either run directly (node/bun probe.mjs) or bundled via
// `bun build --target=bun` / `bun build --compile` — engine modules are
// resolved by absolute path so the bundle inlines the right files.

import path from 'node:path';
import fs from 'node:fs';
import { performance } from 'node:perf_hooks';

const tFull0 = performance.now();

const CALC_ROOT = process.env.CALC_ROOT;
if (!CALC_ROOT) {
  console.error('bench-runtime.probe: CALC_ROOT env var is required');
  process.exit(1);
}

async function loadDefault(spec) {
  const m = await import(spec);
  return m.default ?? m;
}

const mde = await loadDefault(path.join(CALC_ROOT, 'lib/engine/index.js'));
const { loadBytecode, bytecodeArrGetGuard } =
  await import(path.join(CALC_ROOT, 'lib/engine/ill/bytecode-loader.js'));

const codePath = path.join(CALC_ROOT, 'calculus/ill/programs/multisig_nocall_solc_code.ill');
const srcPath  = path.join(CALC_ROOT, 'calculus/ill/programs/multisig_nocall_solc_symbolic.ill');

const loadOpts = {};
try {
  const hex = fs.readFileSync(codePath, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];
  const bc = loadBytecode(hex);
  loadOpts.extraGrade0Facts = bc.facts;
  loadOpts.scopeGuard = bytecodeArrGetGuard;
} catch (e) { console.error('bc fail:', e.message); }

const tLoad0 = performance.now();
const calc = mde.load(srcPath, loadOpts);
const loadMs = performance.now() - tLoad0;

const tDec0 = performance.now();
const st = (mde.normalizeQuery || mde.decomposeQuery)(calc.queries.get('symex'));
const decMs = performance.now() - tDec0;

const tExp0 = performance.now();
calc.explore(st);
const expMs = performance.now() - tExp0;

const totalMs = performance.now() - tFull0;

process.stdout.write(JSON.stringify({
  runtime: typeof Bun !== 'undefined' ? 'bun' : 'node',
  loadMs, decMs, expMs, totalMs,
}) + '\n');
