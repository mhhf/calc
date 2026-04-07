#!/usr/bin/env node
/**
 * tools/test-timing.js — Measure per-file test execution time
 *
 * Discovers all test files, runs each individually, records wall-clock
 * duration and pass/fail/skip counts.  Produces a sorted table and
 * optional JSON report.
 *
 * Usage:
 *   node tools/test-timing.js [options]
 *
 * Options:
 *   --timeout=<ms>      Per-file timeout in ms  (default: 120000)
 *   --skip=<regex>      Skip files whose basename matches this pattern
 *   --only=<regex>      Only run files whose basename matches this pattern
 *   --category=<name>   Only run category: core | engine | all  (default: all)
 *   --save              Write JSON report to tools/test-timing-report.json
 *   --json              Print JSON to stdout instead of table
 *   --profile=<name>    Set CALC_PROFILE env var (bare | fast | evm)
 *   --concurrency=<n>   Max parallel files (default: 1, sequential)
 */

'use strict';

const { spawnSync } = require('child_process');
const path = require('path');
const fs = require('fs');

// ── CLI args ────────────────────────────────────────────────────────────

function parseArgs() {
  const args = {
    timeout: 120_000,
    skip: null,
    only: null,
    category: 'all',
    save: false,
    json: false,
    profile: null,
    concurrency: 1,
  };
  for (const a of process.argv.slice(2)) {
    const [k, v] = a.replace(/^--/, '').split('=');
    if (k === 'timeout')     args.timeout = Number(v);
    else if (k === 'skip')   args.skip = new RegExp(v);
    else if (k === 'only')   args.only = new RegExp(v);
    else if (k === 'category') args.category = v;
    else if (k === 'save')   args.save = true;
    else if (k === 'json')   args.json = true;
    else if (k === 'profile') args.profile = v;
    else if (k === 'concurrency') args.concurrency = Number(v);
    else { console.error(`Unknown option: --${k}`); process.exit(1); }
  }
  return args;
}

// ── Discovery ───────────────────────────────────────────────────────────

function discoverTestFiles(rootDir) {
  const testsDir = path.join(rootDir, 'tests');
  const engineDir = path.join(testsDir, 'engine');
  const vmtestDir = path.join(engineDir, 'vmtest');
  const files = [];

  // Core tests (tests/*.test.js + hash.js)
  if (fs.existsSync(testsDir)) {
    for (const f of fs.readdirSync(testsDir).sort()) {
      if (f.endsWith('.test.js') || f === 'hash.js') {
        files.push({
          path: path.join(testsDir, f),
          basename: f,
          category: 'core',
        });
      }
    }
  }

  // Engine tests (tests/engine/*.test.js)
  if (fs.existsSync(engineDir)) {
    for (const f of fs.readdirSync(engineDir).sort()) {
      if (f.endsWith('.test.js')) {
        files.push({
          path: path.join(engineDir, f),
          basename: `engine/${f}`,
          category: 'engine',
        });
      }
    }
  }

  // VMTest (tests/engine/vmtest/vmtest.test.js)
  const vmtest = path.join(vmtestDir, 'vmtest.test.js');
  if (fs.existsSync(vmtest)) {
    files.push({
      path: vmtest,
      basename: 'engine/vmtest/vmtest.test.js',
      category: 'engine',
    });
  }

  return files;
}

// ── Runner ──────────────────────────────────────────────────────────────

/**
 * Parse node:test TAP / spec output for summary counts.
 * Looks for lines like:  # tests 34  /  # pass 34  /  # fail 0  /  # duration_ms 1234
 */
function parseSummary(output) {
  const summary = { tests: 0, pass: 0, fail: 0, skip: 0, cancelled: 0 };
  const lines = output.split('\n');
  for (const line of lines) {
    const m = line.match(/^# (tests|pass|fail|skip|skipped|cancelled|todo)\s+(\d+)/);
    if (m) {
      const key = m[1] === 'skipped' ? 'skip' : m[1] === 'todo' ? 'skip' : m[1];
      if (key in summary) summary[key] = Number(m[2]);
    }
  }
  return summary;
}

function runOneFile(filePath, timeout, env) {
  const isEngine = filePath.includes(path.join('tests', 'engine'));
  const nodeFlags = isEngine ? ['--max-old-space-size=8192'] : [];

  const start = Date.now();
  const result = spawnSync(
    process.execPath,
    [...nodeFlags, '--test', filePath],
    {
      timeout,
      env: { ...process.env, ...env },
      stdio: ['pipe', 'pipe', 'pipe'],
      maxBuffer: 20 * 1024 * 1024,
    }
  );
  const duration = Date.now() - start;

  const stdout = (result.stdout || Buffer.alloc(0)).toString();
  const stderr = (result.stderr || Buffer.alloc(0)).toString();
  const combined = stdout + '\n' + stderr;

  let status;
  if (result.signal === 'SIGTERM' || result.error?.code === 'ETIMEDOUT') {
    status = 'timeout';
  } else if (result.status !== 0) {
    status = 'fail';
  } else {
    status = 'pass';
  }

  const summary = parseSummary(combined);

  return { duration, status, summary, stdout, stderr };
}

// ── Table formatting ────────────────────────────────────────────────────

function formatDuration(ms) {
  if (ms >= 60_000) return `${(ms / 60_000).toFixed(1)}m`;
  if (ms >= 1_000) return `${(ms / 1_000).toFixed(1)}s`;
  return `${ms}ms`;
}

function tierLabel(ms) {
  if (ms < 3_000)   return 'quick';
  if (ms < 30_000)  return 'normal';
  if (ms < 120_000) return 'slow';
  return 'VERY SLOW';
}

function statusIcon(s) {
  if (s === 'pass')    return 'PASS';
  if (s === 'fail')    return 'FAIL';
  if (s === 'timeout') return 'TIMEOUT';
  return s;
}

function printTable(results) {
  // Sort slowest first
  const sorted = [...results].sort((a, b) => b.duration - a.duration);

  // Column widths
  const nameW = Math.max(12, ...sorted.map(r => r.basename.length)) + 2;
  const durW = 10;
  const statW = 9;
  const tierW = 11;
  const hdr = [
    'File'.padEnd(nameW),
    'Duration'.padStart(durW),
    'Status'.padEnd(statW),
    'Tier'.padEnd(tierW),
    'Pass/Fail/Skip',
  ].join('  ');
  const sep = '─'.repeat(hdr.length);

  console.log('\n' + sep);
  console.log(hdr);
  console.log(sep);

  let totalDuration = 0;
  let totalPass = 0;
  let totalFail = 0;
  let totalSkip = 0;

  for (const r of sorted) {
    totalDuration += r.duration;
    totalPass += r.summary.pass;
    totalFail += r.summary.fail;
    totalSkip += r.summary.skip;

    const counts = `${r.summary.pass}/${r.summary.fail}/${r.summary.skip}`;
    const line = [
      r.basename.padEnd(nameW),
      formatDuration(r.duration).padStart(durW),
      statusIcon(r.status).padEnd(statW),
      tierLabel(r.duration).padEnd(tierW),
      counts,
    ].join('  ');
    console.log(line);
  }

  console.log(sep);
  console.log(
    `TOTAL: ${sorted.length} files  ${formatDuration(totalDuration)}  ` +
    `${totalPass} pass / ${totalFail} fail / ${totalSkip} skip`
  );
  console.log(sep + '\n');

  // Tier summary
  const tiers = { quick: [], normal: [], slow: [], 'VERY SLOW': [] };
  for (const r of sorted) tiers[tierLabel(r.duration)].push(r.basename);

  console.log('Tier breakdown:');
  for (const [tier, files] of Object.entries(tiers)) {
    if (files.length === 0) continue;
    console.log(`  ${tier} (${files.length}): ${files.join(', ')}`);
  }
  console.log('');
}

// ── Main ────────────────────────────────────────────────────────────────

function main() {
  const args = parseArgs();
  const rootDir = path.join(__dirname, '..');
  let files = discoverTestFiles(rootDir);

  // Filters
  if (args.category !== 'all') {
    files = files.filter(f => f.category === args.category);
  }
  if (args.skip) {
    files = files.filter(f => !args.skip.test(f.basename));
  }
  if (args.only) {
    files = files.filter(f => args.only.test(f.basename));
  }

  if (files.length === 0) {
    console.error('No test files matched filters.');
    process.exit(1);
  }

  const env = {};
  if (args.profile) env.CALC_PROFILE = args.profile;

  console.log(`Running ${files.length} test files (timeout: ${formatDuration(args.timeout)} per file)`);
  if (args.profile) console.log(`Profile: ${args.profile}`);
  console.log('');

  const results = [];

  for (let i = 0; i < files.length; i++) {
    const f = files[i];
    const progress = `[${i + 1}/${files.length}]`;
    process.stdout.write(`${progress} ${f.basename} ... `);

    const r = runOneFile(f.path, args.timeout, env);
    results.push({ ...f, ...r });

    const icon = r.status === 'pass' ? '✓' : r.status === 'timeout' ? '⏱' : '✗';
    console.log(`${icon} ${formatDuration(r.duration)}  (${r.summary.pass}p/${r.summary.fail}f/${r.summary.skip}s)`);
  }

  if (!args.json) {
    printTable(results);
  }

  // Build report
  const report = {
    timestamp: new Date().toISOString(),
    timeout: args.timeout,
    profile: args.profile || 'default',
    nodeVersion: process.version,
    files: results.map(r => ({
      basename: r.basename,
      category: r.category,
      duration: r.duration,
      status: r.status,
      tests: r.summary.tests,
      pass: r.summary.pass,
      fail: r.summary.fail,
      skip: r.summary.skip,
    })),
  };

  if (args.json) {
    console.log(JSON.stringify(report, null, 2));
  }

  if (args.save) {
    const outPath = path.join(__dirname, 'test-timing-report.json');
    fs.writeFileSync(outPath, JSON.stringify(report, null, 2) + '\n');
    console.log(`Report saved to ${outPath}`);
  }

  // Exit with failure code if any test failed
  const anyFail = results.some(r => r.status === 'fail');
  if (anyFail) process.exit(1);
}

main();
