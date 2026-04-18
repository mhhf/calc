#!/usr/bin/env node
/**
 * TODO_0216 Phase 0 H4 — V8 IC probe for apply()
 *
 * Spawns a child process with --trace-ic, exercises apply() across many
 * term/theta shapes, and greps the trace for `→megamorphic` transitions.
 * Writes baseline to doc/_scratch/0216-ic-baseline.json.
 *
 * Purpose: any new megamorphic site introduced by Phase 2 (idea A — Map-θ)
 * is a RES_0069-class regression. Compare post-phase run against baseline;
 * any new site aborts the phase.
 *
 * Usage:
 *   node tools/ic-probe.js
 *   node tools/ic-probe.js --compare   # compare against saved baseline
 */

import path from 'path';
import fs from 'fs';
import { spawnSync } from 'child_process';
const ROOT = path.resolve(import.meta.dirname, '..');
const BASELINE_PATH = path.join(ROOT, 'doc/_scratch/0216-ic-baseline.json');

function parseArgs() {
  return { compare: process.argv.includes('--compare') };
}

// Child script lives in a sibling .mjs file so codemods don't see source as
// data and rewrite imports inside string contents. See ic-probe.child.mjs.
const CHILD_SCRIPT_PATH = path.join(import.meta.dirname, 'ic-probe.child.mjs');

// V8 --log-ic CSV format (Node 22 / V8 12.x):
//   <ICType>,<pc>,<time>,<line>,<col>,<state-from>,<state-to>,<map>,<name>,<modifier>,<slow_reason>
// IC state chars: 0=uninit, .=premono, 1=mono, P=poly, N=mega, G=generic, ^=recompute.
//
// The V8 log doesn't stamp each IC line with a filename — only <line>,<col>.
// That's OK for a regression canary: we key each site by (ICType, line, col)
// and compare the full site set between baseline and a post-Phase-2 run. Any
// NEW triple with state N (megamorphic) is a RES_0069-class regression signal.
function parseTrace(logText) {
  const lines = logText.split('\n');
  const samples = [];
  let polyCount = 0;
  let megaCount = 0;
  const megaSites = {};

  for (const ln of lines) {
    if (!ln) continue;
    if (!/^(LoadIC|StoreIC|KeyedLoadIC|KeyedStoreIC|LoadGlobalIC|StoreGlobalIC|LoadPolymorphicIC|StorePolymorphicIC)\b/.test(ln)) continue;
    const f = ln.split(',');
    if (f.length < 7) continue;
    const icType = f[0];
    const line = f[3];
    const col = f[4];
    const stateTo = f[6];

    if (stateTo === 'N') {
      megaCount++;
      const key = `${icType}:${line}:${col}`;
      megaSites[key] = (megaSites[key] || 0) + 1;
      if (samples.length < 30) samples.push({ site: key, raw: ln.slice(0, 180) });
    } else if (stateTo === 'P') {
      polyCount++;
    }
  }

  return { megaCount, polyCount, megaSites, samples };
}

function main() {
  const { compare } = parseArgs();

  // V8 --log-ic writes to a log file (default v8.log). Use a unique path.
  const logPath = path.join(ROOT, `doc/_scratch/0216-ic-v8-${process.pid}.log`);
  fs.mkdirSync(path.dirname(logPath), { recursive: true });
  try { fs.unlinkSync(logPath); } catch { /* ignore */ }

  // V8 IC probing requires node (`--log-ic` is V8-specific; bun has no
  // equivalent). Hardcode `node` rather than using process.execPath so the
  // tool works correctly when this file is invoked under bun too.
  const res = spawnSync(
    'node',
    ['--log-ic', `--logfile=${logPath}`, '--no-logfile-per-isolate', CHILD_SCRIPT_PATH],
    {
      cwd: ROOT,
      encoding: 'utf8',
      maxBuffer: 256 * 1024 * 1024,
    }
  );

  if (res.status !== 0) {
    console.error('Child exited with code', res.status);
    console.error('STDOUT:', res.stdout.slice(-2000));
    console.error('STDERR (tail):', res.stderr.slice(-2000));
    process.exit(1);
  }
  if (!res.stdout.includes('__IC_PROBE_DONE__')) {
    console.error('Child did not emit done marker. stdout tail:', res.stdout.slice(-2000));
    process.exit(1);
  }

  // V8 may rewrite the log path with isolate/pid suffixes. Find any variant.
  const logDir = path.dirname(logPath);
  const logBase = path.basename(logPath);
  let logText = '';
  for (const f of fs.readdirSync(logDir)) {
    if (f === logBase || f.startsWith(logBase.replace(/\.log$/, ''))) {
      logText += fs.readFileSync(path.join(logDir, f), 'utf8') + '\n';
    }
  }
  if (!logText) {
    console.error(`No V8 log written at ${logPath}. Listing ${logDir}:`);
    console.error(fs.readdirSync(logDir).join('\n'));
    process.exit(1);
  }

  const parsed = parseTrace(logText);

  // Cleanup the v8 log files — only the JSON baseline is the artifact.
  for (const f of fs.readdirSync(logDir)) {
    if (f === logBase || f.startsWith(logBase.replace(/\.log$/, ''))) {
      try { fs.unlinkSync(path.join(logDir, f)); } catch { /* ignore */ }
    }
  }

  if (compare) {
    if (!fs.existsSync(BASELINE_PATH)) {
      console.error(`No baseline at ${BASELINE_PATH}. Run without --compare first.`);
      process.exit(2);
    }
    const baseline = JSON.parse(fs.readFileSync(BASELINE_PATH, 'utf8'));
    const baselineSites = new Set(Object.keys(baseline.megaSites));
    const currentSites = new Set(Object.keys(parsed.megaSites));
    const newSites = [...currentSites].filter(s => !baselineSites.has(s));
    console.log(`Baseline mega sites: ${baselineSites.size}, current: ${currentSites.size}, new: ${newSites.length}`);
    if (newSites.length > 0) {
      console.error('NEW megamorphic IC sites in apply()/Store hot path:');
      for (const s of newSites) console.error('  ' + s + ' hits=' + parsed.megaSites[s]);
      process.exit(3);
    }
    console.log('OK: no new megamorphic sites.');
    return;
  }

  const payload = {
    schema: '0216-ic-baseline/v1',
    recorded: new Date().toISOString(),
    node: process.version,
    megaCount: parsed.megaCount,
    polyCount: parsed.polyCount,
    megaSites: parsed.megaSites,
    samples: parsed.samples,
  };
  fs.mkdirSync(path.dirname(BASELINE_PATH), { recursive: true });
  fs.writeFileSync(BASELINE_PATH, JSON.stringify(payload, null, 2));
  console.log(`Wrote ${BASELINE_PATH}`);
  console.log(`mega=${parsed.megaCount} poly=${parsed.polyCount} distinct mega sites=${Object.keys(parsed.megaSites).length}`);
  for (const [site, hits] of Object.entries(parsed.megaSites).slice(0, 15)) {
    console.log(`  ${site} hits=${hits}`);
  }
}

main();
