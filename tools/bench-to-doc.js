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
          means: [],
          stddevs: [],
          nodes: result.data.nodes,
          branches: result.data.branches,
        });
      }

      const entry = commitMap.get(result.fullHash);
      entry.means.push(result.data.mean);
      entry.stddevs.push(result.data.stddev);
    }
  }

  // Compute aggregated stats per commit
  const commits = Array.from(commitMap.values()).map(c => ({
    fullHash: c.fullHash,
    shortHash: c.shortHash,
    date: c.date,
    subject: c.subject,
    mean: c.means.reduce((a, b) => a + b, 0) / c.means.length,
    stddev: c.stddevs.reduce((a, b) => a + b, 0) / c.stddevs.length,
    runCount: c.means.length,
    nodes: c.nodes,
    branches: c.branches,
  }));

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

  const vals = commits.map(c => c.mean);
  const minMs = vals.length > 0 ? Math.min(...vals) : null;
  const maxMs = vals.length > 0 ? Math.max(...vals) : null;

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
  lines.push('Benchmark of `explore()` on `solc_symbolic` with FFI + all optimizations enabled.');
  lines.push('');
  lines.push(`- **Commits**: ${totalCommits}`);
  lines.push(`- **Benchmark runs**: ${totalRuns}`);
  lines.push(`- **Last updated**: ${dateStr}`);
  if (minMs !== null) {
    lines.push(`- **Range**: ${fmtMs(minMs)} — ${fmtMs(maxMs)}`);
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
