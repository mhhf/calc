#!/usr/bin/env node
/**
 * bench-runtime.js — cross-runtime cold-start benchmark.
 *
 * Measures wall-clock time of a fresh spawn across runtimes:
 *   - node         (baseline, unbundled CJS)
 *   - bun          (unbundled CJS)
 *   - bun-bundled  (bun build --target=bun --format=cjs, unbundled runtime load)
 *   - bun-compiled (bun build --compile)
 *   - bun-compiled-bytecode (bun build --compile --minify --bytecode)
 *
 * Scenarios:
 *   - cold       (no compose cache)
 *   - cache-hit  (CALC_COMPOSE_CACHE=1, primed)
 *
 * Usage:
 *   node tools/bench-runtime.js [--runs=7] [--probe=multisig] [--json]
 *
 * Emits a markdown table to stdout. Pass --json for machine-readable output.
 */

'use strict';

import fs from 'fs';
import os from 'os';
import path from 'path';
import { spawnSync } from 'child_process';
const ROOT = path.resolve(import.meta.dirname, '..');
const BUN = process.env.BUN_BIN || '/nix/store/4b7jvqsqywnsb273svingfmpqschkszi-bun-1.3.11/bin/bun';
const NODE = process.env.NODE_BIN || 'node';
// Probe (sibling .mjs) reads CALC_ROOT to resolve engine modules.
process.env.CALC_ROOT = ROOT;

// ─── Args ───────────────────────────────────────────────────────────

function parseArgs(argv) {
  const opts = { runs: 7, probe: 'multisig', json: false, warmup: 2, skipBuild: false };
  for (const a of argv.slice(2)) {
    if (a === '--json') opts.json = true;
    else if (a === '--skip-build') opts.skipBuild = true;
    else if (a.startsWith('--runs=')) opts.runs = parseInt(a.slice(7), 10);
    else if (a.startsWith('--warmup=')) opts.warmup = parseInt(a.slice(9), 10);
    else if (a.startsWith('--probe=')) opts.probe = a.slice(8);
  }
  return opts;
}

// ─── Probe ──────────────────────────────────────────────────────────
//
// Probe source lives in a sibling .mjs file. CALC_ROOT env var tells the
// probe (or its bundled/compiled form) where to resolve engine modules.

const PROBE_SRC_PATH = path.join(import.meta.dirname, 'bench-runtime.probe.mjs');

// ─── Build artifacts ────────────────────────────────────────────────

function ensureArtifacts(skipBuild) {
  const tmp = path.join(os.tmpdir(), 'calc-bench-runtime');
  fs.mkdirSync(tmp, { recursive: true });
  // Copy probe into tmp so bun build emits artifacts next to it.
  const probePath = path.join(tmp, 'probe.mjs');
  fs.copyFileSync(PROBE_SRC_PATH, probePath);

  const bundledPath = path.join(tmp, 'probe-bundled.js');
  const compiledPath = path.join(tmp, 'probe-compiled');
  const compiledBytecodePath = path.join(tmp, 'probe-compiled-bytecode');

  if (skipBuild && fs.existsSync(bundledPath) && fs.existsSync(compiledPath)
      && fs.existsSync(compiledBytecodePath)) {
    return { probePath, bundledPath, compiledPath, compiledBytecodePath, tmp };
  }

  // bun build --target=bun → bundled ESM for bun runtime
  run(BUN, ['build', probePath, '--target=bun',
            `--outfile=${bundledPath}`], 'bun build (bundled)');
  // bun build --compile → self-contained binary
  run(BUN, ['build', probePath, '--compile',
            `--outfile=${compiledPath}`], 'bun build (compiled)');
  // bun build --compile --minify --bytecode → optimized binary
  run(BUN, ['build', probePath, '--compile', '--minify', '--bytecode',
            '--no-compile-autoload-dotenv', '--no-compile-autoload-bunfig',
            `--outfile=${compiledBytecodePath}`], 'bun build (compiled+bytecode)');

  return { probePath, bundledPath, compiledPath, compiledBytecodePath, tmp };
}

function run(bin, args, label) {
  const r = spawnSync(bin, args, { stdio: 'pipe' });
  if (r.status !== 0) {
    console.error(`[${label}] failed:`, r.stderr?.toString() || '(no stderr)');
    process.exit(1);
  }
}

// ─── Measurement ────────────────────────────────────────────────────

function measure(cmd, args, env, runs) {
  const samples = [];
  for (let i = 0; i < runs; i++) {
    const t0 = process.hrtime.bigint();
    const r = spawnSync(cmd, args, { env: { ...process.env, ...env }, stdio: 'pipe' });
    const wallMs = Number(process.hrtime.bigint() - t0) / 1e6;
    if (r.status !== 0) {
      console.error('spawn failed:', cmd, args.join(' '), r.stderr?.toString());
      continue;
    }
    let inner = null;
    try { inner = JSON.parse(r.stdout.toString().trim().split('\n').pop()); } catch {}
    samples.push({ wallMs, ...inner });
  }
  return samples;
}

function stats(samples, key) {
  const vs = samples.map(s => s[key]).filter(v => typeof v === 'number').sort((a,b) => a-b);
  if (!vs.length) return { avg: null, min: null, max: null };
  const avg = vs.reduce((a,b) => a+b, 0) / vs.length;
  return { avg, min: vs[0], max: vs[vs.length-1], median: vs[Math.floor(vs.length/2)] };
}

// ─── Main ───────────────────────────────────────────────────────────

function main() {
  const opts = parseArgs(process.argv);
  if (!fs.existsSync(BUN)) {
    console.error(`bun not found at ${BUN}; set BUN_BIN env var`);
    process.exit(1);
  }

  const art = ensureArtifacts(opts.skipBuild);

  // Per-mode cache dir — isolate cache-hit from cold
  const coldCacheDir = path.join(art.tmp, 'cache-cold');
  const hitCacheDir = path.join(art.tmp, 'cache-hit');
  fs.rmSync(coldCacheDir, { recursive: true, force: true });
  fs.rmSync(hitCacheDir, { recursive: true, force: true });
  fs.mkdirSync(coldCacheDir, { recursive: true });
  fs.mkdirSync(hitCacheDir, { recursive: true });

  // Prime cache-hit dir with one run of each runtime
  const primeEnv = { CALC_COMPOSE_CACHE: '1', CALC_CACHE_DIR: hitCacheDir };
  spawnSync(NODE, [art.probePath], { env: { ...process.env, ...primeEnv }, stdio: 'ignore' });
  spawnSync(BUN, [art.probePath], { env: { ...process.env, ...primeEnv }, stdio: 'ignore' });
  spawnSync(art.compiledBytecodePath, [], { env: { ...process.env, ...primeEnv }, stdio: 'ignore' });

  const configs = [
    { name: 'node + unbundled',          cmd: NODE, args: [art.probePath] },
    { name: 'bun + unbundled',           cmd: BUN,  args: [art.probePath] },
    { name: 'bun + bundled',             cmd: BUN,  args: [art.bundledPath] },
    { name: 'bun --compile',             cmd: art.compiledPath, args: [] },
    { name: 'bun --compile --bytecode',  cmd: art.compiledBytecodePath, args: [] },
  ];

  // Warm-up runs (discarded)
  for (const cfg of configs) {
    for (let i = 0; i < opts.warmup; i++) {
      spawnSync(cfg.cmd, cfg.args, { stdio: 'ignore' });
    }
  }

  const results = [];
  for (const cfg of configs) {
    const cold = measure(cfg.cmd, cfg.args, {}, opts.runs);
    const hit = measure(cfg.cmd, cfg.args,
      { CALC_COMPOSE_CACHE: '1', CALC_CACHE_DIR: hitCacheDir }, opts.runs);
    results.push({ name: cfg.name, cold: stats(cold, 'wallMs'),
                   hit: stats(hit, 'wallMs'),
                   coldTotal: stats(cold, 'totalMs'),
                   coldLoad: stats(cold, 'loadMs'),
                   coldExp: stats(cold, 'expMs') });
  }

  if (opts.json) {
    console.log(JSON.stringify({ opts, bun: BUN, node: NODE, results }, null, 2));
    return;
  }

  // Markdown table
  const f = v => v == null ? '—' : v.toFixed(0) + 'ms';
  console.log();
  console.log(`# bench-runtime.js (runs=${opts.runs}, warmup=${opts.warmup})`);
  console.log();
  console.log(`node: ${NODE}`);
  console.log(`bun:  ${BUN}`);
  console.log();
  console.log('| config                           | cold wall | cold load | cold explore | cache-hit wall |');
  console.log('| -------------------------------- | --------: | --------: | -----------: | -------------: |');
  for (const r of results) {
    console.log(`| ${r.name.padEnd(32)} | ${f(r.cold.avg).padStart(9)} | ${f(r.coldLoad.avg).padStart(9)} | ${f(r.coldExp.avg).padStart(12)} | ${f(r.hit.avg).padStart(14)} |`);
  }
  console.log();
  // Savings vs node baseline
  const base = results[0];
  console.log(`Relative to **${base.name}** (cold):`);
  for (const r of results.slice(1)) {
    const d = r.cold.avg - base.cold.avg;
    const pct = (d / base.cold.avg * 100).toFixed(0);
    console.log(`  ${r.name}: ${d >= 0 ? '+' : ''}${d.toFixed(0)}ms (${pct}%)`);
  }
}

main();
