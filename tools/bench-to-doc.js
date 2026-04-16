#!/usr/bin/env node
/**
 * Convert benchmark run files to a compiled markdown document
 * with chart data for os-web rendering.
 *
 * Reads all JSON files from a runs directory, aggregates per-commit
 * statistics (averaging means across multiple runs), and outputs
 * a markdown document with an embedded bench-chart code block.
 *
 * Usage:
 *   node tools/bench-to-doc.js --runs-dir=<dir>
 */

const { execSync } = require('child_process');
const fs = require('fs');
const path = require('path');

// ─── Arg parsing ──────────────────────────────────────────────────────────────

function parseArgs() {
  const args = process.argv.slice(2);
  let runsDir = null;
  for (const arg of args) {
    if (arg.startsWith('--runs-dir=')) runsDir = arg.slice(11);
  }
  return { runsDir };
}

// ─── Aggregation ──────────────────────────────────────────────────────────────

// Extract symex/e2e stats from a data record supporting both
// legacy flat format (pre-e2e: { mean, stddev, ... }) and new nested
// ({ symex: {...}, e2e: {...} }) format.
function extractSymex(data) {
  if (!data || data.error) return null;
  if (data.symex) return data.symex;
  if (typeof data.mean === 'number') {
    return { mean: data.mean, stddev: data.stddev };
  }
  return null;
}

function extractE2E(data) {
  if (!data || data.error) return null;
  return data.e2e || null;
}

function avg(xs) {
  if (!xs || xs.length === 0) return null;
  return xs.reduce((a, b) => a + b, 0) / xs.length;
}

// Merge per-phase stats across multiple bench runs for the same commit.
// Each run emits phases: { "path": { mean, stddev, runs, meta? } }. We average
// the means weighted by runs, and re-compute a pooled stddev as the
// simple average of reported stddevs (sufficient for display; the
// per-run stddev already captures within-run variance).
//
// Meta is merged field-by-field: numeric fields are averaged weighted by runs,
// array/boolean/string fields take the last-observed value.
function mergePhases(phasesList) {
  if (!phasesList || phasesList.length === 0) return null;
  const byPath = new Map();
  for (const phases of phasesList) {
    for (const [p, s] of Object.entries(phases)) {
      if (!byPath.has(p)) byPath.set(p, { sumMean: 0, sumStddev: 0, totalRuns: 0, entries: 0, metas: [] });
      const acc = byPath.get(p);
      const n = s.runs || 1;
      acc.sumMean += s.mean * n;
      acc.sumStddev += (s.stddev || 0);
      acc.totalRuns += n;
      acc.entries += 1;
      if (s.meta) acc.metas.push({ meta: s.meta, runs: n });
    }
  }
  const out = {};
  for (const [p, acc] of byPath) {
    const entry = {
      mean: acc.sumMean / acc.totalRuns,
      stddev: acc.sumStddev / acc.entries,
      runs: acc.totalRuns,
    };
    if (acc.metas.length > 0) entry.meta = _mergeMeta(acc.metas);
    out[p] = entry;
  }
  return out;
}

function _mergeMeta(weightedMetas) {
  const keys = new Set();
  for (const { meta } of weightedMetas) for (const k of Object.keys(meta)) keys.add(k);
  const out = {};
  for (const k of keys) {
    let numSum = 0, numWeight = 0;
    let last = undefined;
    let allNumeric = true;
    for (const { meta, runs } of weightedMetas) {
      const v = meta[k];
      if (v === undefined) continue;
      last = v;
      if (typeof v === 'number') {
        numSum += v * runs;
        numWeight += runs;
      } else {
        allNumeric = false;
      }
    }
    if (allNumeric && numWeight > 0) out[k] = numSum / numWeight;
    else out[k] = last;
  }
  return out;
}

function aggregate(runsDir) {
  const files = fs.readdirSync(runsDir).filter(f => f.endsWith('.json'));
  if (files.length === 0) {
    console.error('No JSON files found in', runsDir);
    process.exit(1);
  }

  // Collect all data points per commit (keyed by fullHash)
  const commitMap = new Map();

  for (const file of files) {
    const data = JSON.parse(fs.readFileSync(path.join(runsDir, file), 'utf8'));
    for (const result of data.results || []) {
      if (!result.data || result.data.error) continue;

      if (!commitMap.has(result.fullHash)) {
        commitMap.set(result.fullHash, {
          fullHash: result.fullHash,
          shortHash: result.shortHash,
          date: result.date,
          subject: result.subject,
          symexMeans: [],
          symexStddevs: [],
          e2eMeans: [],
          e2eStddevs: [],
          e2ePhasesList: [],
          nodes: result.data.nodes,
          branches: result.data.branches,
        });
      }

      const entry = commitMap.get(result.fullHash);
      const s = extractSymex(result.data);
      if (s) {
        entry.symexMeans.push(s.mean);
        entry.symexStddevs.push(s.stddev);
      }
      const e = extractE2E(result.data);
      if (e) {
        entry.e2eMeans.push(e.mean);
        entry.e2eStddevs.push(e.stddev);
        if (e.phases) entry.e2ePhasesList.push(e.phases);
      }
    }
  }

  // Compute aggregated stats per commit
  const commits = Array.from(commitMap.values())
    .filter(c => c.symexMeans.length > 0)
    .map(c => {
      const symexMean = avg(c.symexMeans);
      const symexStddev = avg(c.symexStddevs);
      const e2eMean = avg(c.e2eMeans);
      const e2eStddev = avg(c.e2eStddevs);
      const phases = mergePhases(c.e2ePhasesList);
      const e2e = e2eMean !== null
        ? { mean: e2eMean, stddev: e2eStddev, runCount: c.e2eMeans.length }
        : null;
      if (e2e && phases) e2e.phases = phases;
      return {
        fullHash: c.fullHash,
        shortHash: c.shortHash,
        date: c.date,
        subject: c.subject,
        // Legacy top-level fields (== symex) for backward compat
        mean: symexMean,
        stddev: symexStddev,
        runCount: c.symexMeans.length,
        // Explicit nested series
        symex: { mean: symexMean, stddev: symexStddev, runCount: c.symexMeans.length },
        e2e,
        nodes: c.nodes,
        branches: c.branches,
      };
    });

  // Sort by canonical git history order (oldest-first for chart left→right).
  // Map insertion order is unreliable across multiple run files (readdirSync is alphabetical).
  const maxLog = Math.max(200, commitMap.size * 3);
  const gitLog = execSync(`git log --format=%H --topo-order -n ${maxLog} HEAD --`, {
    encoding: 'utf8',
  }).trim().split('\n');
  const orderMap = new Map(gitLog.map((h, i) => [h, i]));
  commits.sort((a, b) => {
    const ia = orderMap.get(a.fullHash) ?? Infinity;
    const ib = orderMap.get(b.fullHash) ?? Infinity;
    return ib - ia;  // oldest first (higher git log index = older commit)
  });

  return { totalCommits: commits.length, totalRuns: files.length, commits };
}

// ─── Document generation ──────────────────────────────────────────────────────

function fmtMs(ms) {
  if (ms === undefined || ms === null) return '—';
  if (ms < 1) return `${(ms * 1000).toFixed(0)}µs`;
  if (ms < 100) return `${ms.toFixed(2)}ms`;
  return `${ms.toFixed(0)}ms`;
}

function buildDocument(agg) {
  const { totalCommits, totalRuns, commits } = agg;
  const dateStr = new Date().toISOString().slice(0, 10);

  const symexVals = commits.map(c => c.symex?.mean).filter(v => typeof v === 'number');
  const e2eVals = commits.map(c => c.e2e?.mean).filter(v => typeof v === 'number');

  const lines = [];

  // Frontmatter
  lines.push('---');
  lines.push('title: "Calc Benchmarks"');
  lines.push(`summary: "${totalCommits} commits across ${totalRuns} run${totalRuns === 1 ? '' : 's'} — explore solc_symbolic"`);
  lines.push('tags:');
  lines.push('  - benchmarks');
  lines.push('  - performance');
  lines.push('project: calc');
  lines.push('status: active');
  lines.push(`modified: "${dateStr}"`);
  lines.push('---');
  lines.push('');

  // Body
  lines.push('## Benchmark: explore solc_symbolic');
  lines.push('');
  lines.push('Two scenarios per commit (FFI + all optimizations enabled):');
  lines.push('');
  lines.push('- **Symex**: `explore()` on a pre-loaded state (hot-path only).');
  lines.push('- **End-to-end**: full `load()` + `decomposeQuery()` + `explore()` with `cache: false` — measures the cold-start cost users pay on first invocation.');
  lines.push('');
  lines.push(`- **Commits**: ${totalCommits}`);
  lines.push(`- **Benchmark runs**: ${totalRuns}`);
  lines.push(`- **Last updated**: ${dateStr}`);
  if (symexVals.length > 0) {
    lines.push(`- **Symex range**: ${fmtMs(Math.min(...symexVals))} — ${fmtMs(Math.max(...symexVals))}`);
  }
  if (e2eVals.length > 0) {
    lines.push(`- **E2E range**: ${fmtMs(Math.min(...e2eVals))} — ${fmtMs(Math.max(...e2eVals))}`);
  }
  lines.push('');

  // Embedded chart data
  lines.push('```bench-chart');
  lines.push(JSON.stringify({ commits }, null, 2));
  lines.push('```');
  lines.push('');

  return lines.join('\n');
}

// ─── Main ─────────────────────────────────────────────────────────────────────

const opts = parseArgs();
if (!opts.runsDir) {
  console.error('Usage: node tools/bench-to-doc.js --runs-dir=<dir>');
  process.exit(1);
}

const agg = aggregate(opts.runsDir);
process.stdout.write(buildDocument(agg));
