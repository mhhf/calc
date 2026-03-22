#!/usr/bin/env node
/**
 * Convert bench-history.js JSON output to a markdown document
 * with frontmatter compatible with os-web doc rendering.
 *
 * Usage:
 *   node tools/bench-to-doc.js <results.json>
 */

const fs = require('fs');
const path = require('path');

const inputFile = process.argv[2];
if (!inputFile) {
  console.error('Usage: node tools/bench-to-doc.js <results.json>');
  process.exit(1);
}

const data = JSON.parse(fs.readFileSync(inputFile, 'utf8'));
const { config, results, timestamp } = data;

const now = new Date(timestamp || Date.now());
const dateStr = now.toISOString().slice(0, 10);

function fmtMs(ms) {
  if (ms === undefined || ms === null) return '—';
  if (ms < 1) return `${(ms * 1000).toFixed(0)}µs`;
  if (ms < 100) return `${ms.toFixed(2)}ms`;
  return `${ms.toFixed(0)}ms`;
}

function fmtChange(current, baseline) {
  if (!baseline || !current) return '—';
  const pct = ((current - baseline) / baseline) * 100;
  const sign = pct > 0 ? '+' : '';
  return `${sign}${pct.toFixed(1)}%`;
}

// Find baseline (newest successful result)
let baselineMean = null;
for (const r of results) {
  if (r.data && !r.data.error) {
    baselineMean = r.data.mean;
    break;
  }
}

const successful = results.filter(r => r.data && !r.data.error);
const vals = successful.map(r => r.data.mean);
const minMs = vals.length > 0 ? Math.min(...vals) : null;
const maxMs = vals.length > 0 ? Math.max(...vals) : null;

// Build markdown
const lines = [];

lines.push('---');
lines.push('title: "Calc Benchmarks"');
lines.push(`summary: "${successful.length}/${results.length} commits benchmarked — explore solc_symbolic (${config.runs || '?'} runs, ${config.warmup || '?'} warmup)"`);
lines.push('tags:');
lines.push('  - benchmarks');
lines.push('  - performance');
lines.push('project: calc');
lines.push('status: active');
lines.push(`modified: "${dateStr}"`);
lines.push('---');
lines.push('');
lines.push('## Benchmark: explore solc_symbolic');
lines.push('');
lines.push(`Benchmark of \`explore()\` on \`solc_symbolic\` across ${results.length} commits with FFI + all optimizations enabled.`);
lines.push('');
lines.push(`- **Runs per commit**: ${config.runs || '?'} timed, ${config.warmup || '?'} warmup`);
lines.push(`- **Last updated**: ${dateStr}`);
if (minMs !== null) {
  lines.push(`- **Range**: ${fmtMs(minMs)} — ${fmtMs(maxMs)} (${((maxMs / minMs - 1) * 100).toFixed(1)}% spread)`);
}
lines.push('');
lines.push('| # | Commit | Date | Message | Nodes | Leaves | Mean | StdDev | vs HEAD |');
lines.push('|---|--------|------|---------|------:|-------:|-----:|-------:|--------:|');

for (let i = 0; i < results.length; i++) {
  const r = results[i];
  const subject = r.subject.length > 40 ? r.subject.slice(0, 37) + '...' : r.subject;

  if (r.data && r.data.error) {
    lines.push(`| ${i} | ${r.shortHash} | ${r.date} | ${subject} | — | — | ERROR | — | — |`);
  } else if (!r.data) {
    lines.push(`| ${i} | ${r.shortHash} | ${r.date} | ${subject} | — | — | — | — | — |`);
  } else {
    lines.push(`| ${i} | ${r.shortHash} | ${r.date} | ${subject} | ${r.data.nodes} | ${r.data.branches} | ${fmtMs(r.data.mean)} | ${fmtMs(r.data.stddev)} | ${fmtChange(r.data.mean, baselineMean)} |`);
  }
}

lines.push('');
lines.push(`*${successful.length}/${results.length} commits benchmarked successfully.*`);
lines.push('');

process.stdout.write(lines.join('\n'));
