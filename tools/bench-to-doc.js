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

import { execSync } from 'child_process';
import fs from 'fs';
import path from 'path';
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

// Cap on commits emitted into the chart. Older commits are dropped — the chart
// becomes unreadable beyond ~35 entries (tick rotation + density), and recent
// improvements get visually compressed into the rightmost few pixels otherwise.
const MAX_COMMITS = 35;

// Scenarios we track end-to-end (each maps to a top-level field on the run
// data record). Adding a scenario here automatically wires it through
// aggregation, output JSON, and the renderer.
const SCENARIOS = [
  { key: 'e2e',          field: 'e2e',          label: 'cold' },          // alias for nocache
  { key: 'e2eCacheMiss', field: 'e2eCacheMiss', label: 'cache-miss' },
  { key: 'e2eCacheHit',  field: 'e2eCacheHit',  label: 'cache-hit' },
  { key: 'e2eNoOpts',    field: 'e2eNoOpts',    label: 'no-opts' },
];

// Sub-metrics carved out of the e2e (nocache) record. These are stats blocks
// emitted by bench-history.runner.mjs alongside the top-level mean.
const E2E_SUBFIELDS = ['load', 'decompose', 'explore', 'parentWall', 'loadPlusExplore'];

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

function extractScenario(data, field) {
  if (!data || data.error) return null;
  const s = data[field];
  return (s && typeof s.mean === 'number') ? s : null;
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
        const initial = {
          fullHash: result.fullHash,
          shortHash: result.shortHash,
          date: result.date,
          subject: result.subject,
          symexMeans: [],
          symexStddevs: [],
          e2ePhasesList: [],
          nodes: result.data.nodes,
          branches: result.data.branches,
        };
        for (const sc of SCENARIOS) {
          initial[`${sc.key}Means`] = [];
          initial[`${sc.key}Stddevs`] = [];
        }
        for (const sub of E2E_SUBFIELDS) {
          initial[`${sub}Means`] = [];
          initial[`${sub}Stddevs`] = [];
        }
        commitMap.set(result.fullHash, initial);
      }

      const entry = commitMap.get(result.fullHash);
      const s = extractSymex(result.data);
      if (s) {
        entry.symexMeans.push(s.mean);
        entry.symexStddevs.push(s.stddev);
      }
      for (const sc of SCENARIOS) {
        const v = extractScenario(result.data, sc.field);
        if (v) {
          entry[`${sc.key}Means`].push(v.mean);
          entry[`${sc.key}Stddevs`].push(v.stddev);
        }
      }
      // Sub-field stats live on the e2e (nocache) record
      const e = extractScenario(result.data, 'e2e');
      if (e) {
        for (const sub of E2E_SUBFIELDS) {
          const v = e[sub];
          if (v && typeof v.mean === 'number') {
            entry[`${sub}Means`].push(v.mean);
            entry[`${sub}Stddevs`].push(v.stddev || 0);
          }
        }
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
      const phases = mergePhases(c.e2ePhasesList);

      const scenarioOut = {};
      for (const sc of SCENARIOS) {
        const means = c[`${sc.key}Means`];
        if (means.length === 0) { scenarioOut[sc.key] = null; continue; }
        scenarioOut[sc.key] = {
          mean: avg(means),
          stddev: avg(c[`${sc.key}Stddevs`]),
          runCount: means.length,
        };
      }
      // Attach phases to the canonical e2e (nocache) record
      if (scenarioOut.e2e && phases) scenarioOut.e2e.phases = phases;

      // E2E sub-field aggregates (load / decompose / explore / parentWall / loadPlusExplore)
      const partsOut = {};
      for (const sub of E2E_SUBFIELDS) {
        const means = c[`${sub}Means`];
        if (means.length === 0) continue;
        partsOut[sub] = {
          mean: avg(means),
          stddev: avg(c[`${sub}Stddevs`]),
          runCount: means.length,
        };
      }

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
        // Scenarios — e2e/cache-miss/cache-hit/no-opts
        e2e: scenarioOut.e2e,
        e2eCacheMiss: scenarioOut.e2eCacheMiss,
        e2eCacheHit: scenarioOut.e2eCacheHit,
        e2eNoOpts: scenarioOut.e2eNoOpts,
        // E2E sub-phase splits (load/decompose/explore/etc.)
        e2eParts: Object.keys(partsOut).length > 0 ? partsOut : undefined,
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

  // Cap to MAX_COMMITS most-recent entries (chart density)
  const totalCommits = commits.length;
  const capped = commits.slice(-MAX_COMMITS);

  return { totalCommits, totalRuns: files.length, commits: capped };
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
  const shown = commits.length;
  const dateStr = new Date().toISOString().slice(0, 10);

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
  lines.push('Per commit (FFI + all optimizations enabled, multiple scenarios):');
  lines.push('');
  lines.push('- **Symex**: `explore()` on a pre-loaded state (hot-path only).');
  lines.push('- **Cold (nocache)**: full `load()` + `decomposeQuery()` + `explore()` with `cache: false` — first-invocation cost.');
  lines.push('- **Cache-miss**: cold load with compose disk cache enabled, miss path (writes cache).');
  lines.push('- **Cache-hit**: warm load with compose disk cache primed (where the recent 10× wins live).');
  lines.push('- **No-opts**: cold load with all optimizations disabled (regression detector).');
  lines.push('');
  lines.push(`- **Commits sampled**: ${totalCommits}${shown < totalCommits ? ` (chart shows last ${shown})` : ''}`);
  lines.push(`- **Benchmark runs**: ${totalRuns}`);
  lines.push(`- **Last updated**: ${dateStr}`);

  // Per-scenario range across the visible window
  for (const sc of SCENARIOS) {
    const vs = commits.map(c => c[sc.key]?.mean).filter(v => typeof v === 'number');
    if (vs.length > 0) {
      lines.push(`- **${sc.label} range**: ${fmtMs(Math.min(...vs))} — ${fmtMs(Math.max(...vs))} (n=${vs.length})`);
    }
  }
  const symexVals = commits.map(c => c.symex?.mean).filter(v => typeof v === 'number');
  if (symexVals.length > 0) {
    lines.push(`- **symex range**: ${fmtMs(Math.min(...symexVals))} — ${fmtMs(Math.max(...symexVals))}`);
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
