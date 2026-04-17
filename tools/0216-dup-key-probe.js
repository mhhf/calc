#!/usr/bin/env node
/**
 * TODO_0216 Phase 0 H11 — duplicate-key-θ diagnostic
 *
 * Preload script: monkey-patches lib/kernel/substitute.js's `apply` so that
 * every call scans θ for duplicate keys. Any hit is logged to a JSON file.
 *
 * Phase 2 (idea A — Map-indexed θ) silently collapses duplicate keys to
 * last-wins, while HEAD's array-θ is first-wins (see substitute.js:97). If
 * any test path exercises duplicate keys where the first != last binding,
 * Map-θ would produce a semantically different result.
 *
 * Run:
 *   node --require tools/0216-dup-key-probe.js --test tests/...
 * Or hook into npm test:
 *   NODE_OPTIONS=--require=$PWD/tools/0216-dup-key-probe.js npm test
 *
 * On process exit, writes doc/_scratch/0216-dup-key-report.json with:
 *   { total_calls, dup_calls, first_ne_last, examples }
 *
 * first_ne_last === 0 ⇒ Map-θ is behaviourally safe.
 */

const fs = require('fs');
const path = require('path');
const Module = require('module');

const ROOT = path.resolve(__dirname, '..');
// node --test spawns a fresh worker per file; each one writes its own report
// line to a JSONL file (pre-cleared via 0216-dup-key-reset). After the suite
// the separate tools/0216-dup-key-report.js aggregator reads + summarises.
const OUT_JSONL  = path.join(ROOT, 'doc/_scratch/0216-dup-key.jsonl');
const OUT_SUMMARY = path.join(ROOT, 'doc/_scratch/0216-dup-key-report.json');
const MAX_EXAMPLES = 20;

const state = {
  total: 0,
  dup: 0,
  firstNeLast: 0,
  examples: [],
  seenSignatures: new Set(),
};

function recordDup(theta, firstNeLast) {
  state.dup++;
  if (firstNeLast) state.firstNeLast++;
  if (state.examples.length < MAX_EXAMPLES) {
    // Capture caller stack (skip first two frames: Error + this fn).
    const stk = new Error().stack.split('\n').slice(3, 10).map(s => s.trim());
    const sig = theta.map(p => `${p[0]}→${p[1]}`).join('|');
    if (!state.seenSignatures.has(sig)) {
      state.seenSignatures.add(sig);
      state.examples.push({ theta: theta.map(p => [p[0], p[1]]), firstNeLast, stack: stk });
    }
  }
}

// Hook require so we intercept substitute.js as soon as it loads.
const origResolve = Module._resolveFilename;
const origLoad = Module._load;
let patched = false;

Module._load = function(request, parent, ...rest) {
  const result = origLoad.call(this, request, parent, ...rest);
  if (!patched && result && typeof result.apply === 'function'
      && parent && parent.filename
      && /lib\/kernel\/substitute\.js$/.test(
           origResolve.call(Module, request, parent, false))) {
    // This is the code path where substitute.js exports itself.
  }
  return result;
};

// Simpler: wrap via direct require after the first import.
const substPath = require.resolve(path.join(ROOT, 'lib/kernel/substitute'));
const subst = require(substPath);
const origApply = subst.apply;

subst.apply = function instrumentedApply(h, theta) {
  state.total++;
  if (theta && theta.length >= 2) {
    // Detect any duplicate key.
    // Small θ sizes dominate; a linear scan is fine.
    let dup = false;
    let firstNeLast = false;
    for (let i = 0; i < theta.length; i++) {
      const k = theta[i][0];
      for (let j = i + 1; j < theta.length; j++) {
        if (theta[j][0] === k) {
          dup = true;
          if (theta[i][1] !== theta[j][1]) firstNeLast = true;
          break;
        }
      }
      if (dup && firstNeLast) break;
    }
    if (dup) recordDup(theta, firstNeLast);
  }
  return origApply(h, theta);
};

// Also try to replace it on subsequent reloads (belt-and-braces — Node may
// cache, but some test harnesses clear require.cache).
process.on('exit', () => {
  // Skip workers that never called apply (e.g. the --test dispatcher).
  if (state.total === 0) return;
  try {
    fs.mkdirSync(path.dirname(OUT_JSONL), { recursive: true });
    const line = JSON.stringify({
      pid: process.pid,
      argv: process.argv.slice(1).join(' '),
      total_calls: state.total,
      dup_calls: state.dup,
      first_ne_last: state.firstNeLast,
      examples: state.examples,
    }) + '\n';
    fs.appendFileSync(OUT_JSONL, line);
  } catch (e) {
    process.stderr.write(`[0216-dup-key] failed to write report: ${e.message}\n`);
  }
});
