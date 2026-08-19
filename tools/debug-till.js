#!/usr/bin/env node
/**
 * till-native debug runner — timed observation directives (TODO_0265 Phase 4c).
 *
 * The till twin of debug-ill.js, over settle() records instead of exec():
 *   #trace_*     — log view: [activation] rule consumed → produced @+d
 *   #timeline_*  — per-predicate lanes: jobs + token lifetimes
 *   #why_*       — provenance: producer chain of a fact (body = the fact)
 *   #why_not_*   — best failed candidate of a rule (body = the rule name)
 *   #state_*     — settled state dump
 *
 * Every directive takes a `settle: T` setting; `query: <kind>` points at a
 * shared scenario (`#run (settle: T) <state>.`). Rendering lives in
 * lib/engine/timed-render.js — the golden tests exercise the same functions.
 *
 * Usage: node tools/debug-till.js <file.ill> [--only <kind>]
 */

import path from 'path';
import Store from '../lib/kernel/store.js';
import mde from '../lib/engine/index.js';
import convert from '../lib/engine/convert.js';
import tillConfig from '../calculus/till/calculus-config.js';
import { traceLines, timelineLines, whyLines, whyNotLines, fmtFact } from '../lib/engine/timed-render.js';
import { normalizeTimedState } from '../lib/engine/timed.js';
import { toObject as _toObject } from '../lib/engine/fact-set.js';
import dl from './directive-loader.js';
const { ROOT, scanDirectives, detectDuplicates, resolveQueryHash } = dl;
const MAX_STEPS = 10000;

// ─── CLI ────────────────────────────────────────────────────────────

const args = process.argv.slice(2);
const flags = {};
const positional = [];
for (let i = 0; i < args.length; i++) {
  if (args[i] === '--only' && i + 1 < args.length) flags.only = args[++i];
  else if (args[i].startsWith('--')) flags[args[i].slice(2)] = 'true';
  else positional.push(args[i]);
}
if (positional.length === 0) {
  console.error('Usage: node tools/debug-till.js <file.ill> [--only <kind>]');
  process.exit(1);
}

function header(kind, label) {
  const bar = '─'.repeat(Math.max(0, 70 - kind.length - label.length));
  console.log(`\n── ${kind}: ${label} ${bar}`);
}

// ─── Shared settle run ──────────────────────────────────────────────

function runScenario(calc, hash, settings) {
  const initial = convert.decomposeQuery(hash);
  const opts = { maxSteps: MAX_STEPS };
  if (settings?.maxSteps) opts.maxSteps = parseInt(settings.maxSteps, 10);
  if (settings?.rules) opts.rules = settings.rules;
  if (settings?.seed !== undefined) opts.seed = parseInt(settings.seed, 10);
  if (settings?.useFFI !== undefined) opts.useFFI = settings.useFFI === 'true';
  const res = calc.settle(initial, settings.settle, opts);
  return { initial, res, T: calc.timedConfig.parseStamp(settings.settle) };
}

// ─── Handlers ───────────────────────────────────────────────────────

function runTraceD(calc, hash, settings) {
  const { res } = runScenario(calc, hash, settings);
  for (const line of traceLines(res.events)) console.log('  ' + line);
  console.log(`  total: ${res.steps} firings`);
}

function runTimeline(calc, hash, settings) {
  const { initial, res, T } = runScenario(calc, hash, settings);
  // Timeline lanes read the NORMALIZED initial (unstamped facts at 0, D11).
  const init = _toObject(normalizeTimedState(initial, calc.timedConfig));
  for (const line of timelineLines(res.events, init, T)) console.log('  ' + line);
}

function runWhy(calc, hash, settings, factHash) {
  const { initial, res } = runScenario(calc, hash, settings);
  const init = _toObject(normalizeTimedState(initial, calc.timedConfig));
  // The directive body is the fact — normalize an unstamped fact to @0.
  const target = Store.tag(factHash) === 'at'
    ? factHash
    : Store.put('at', [factHash, calc.timedConfig.effect.unit()]);
  console.log(`  why ${fmtFact(target)}`);
  for (const line of whyLines(res.events, init, target)) console.log('  ' + line);
}

function runWhyNot(calc, hash, settings, ruleAtom) {
  const ruleName = Store.tag(ruleAtom) === 'atom' ? Store.child(ruleAtom, 0) : null;
  const rule = calc.forwardRules.find(r => r.name === ruleName);
  if (!rule) { console.log(`  unknown rule '${ruleName}'`); return; }
  const { initial, res, T } = runScenario(calc, hash, settings);
  void res;
  // Diagnose against the SETTLED state (why is it not firing NOW).
  const settled = normalizeTimedState(calc.settle(initial, settings.settle).state, calc.timedConfig);
  const lines = whyNotLines(rule, settled, {
    calc: calc._calcContext, matchOpts: calc._buildMatchOpts({}),
    timedConfig: calc.timedConfig, horizon: T,
  });
  for (const line of lines) console.log('  ' + line);
}

function runState(calc, hash, settings) {
  const { res } = runScenario(calc, hash, settings);
  const facts = Object.entries(res.state.linear)
    .map(([h, c]) => fmtFact(Number(h)) + (c > 1 ? ` x${c}` : '')).sort();
  console.log('  ' + (facts.join(', ') || '(empty)'));
}

// ORDER MATTERS: why_not before why (prefix dispatch).
const HANDLERS = [
  ['why_not', runWhyNot],
  ['why', runWhy],
  ['trace', runTraceD],
  ['timeline', runTimeline],
  ['state', runState],
];

function handlerFor(kind) {
  for (const [prefix, fn] of HANDLERS) {
    if (kind === prefix || kind.startsWith(prefix + '_')) return [prefix, fn];
  }
  return null;
}

// ─── Main ───────────────────────────────────────────────────────────

const filePath = path.resolve(positional[0]);
const fileDirectives = scanDirectives([filePath], /#(\w+)/g);
for (const [file, names] of fileDirectives) {
  const filtered = new Set([...names].filter(n => handlerFor(n)));
  if (filtered.size > 0) fileDirectives.set(file, filtered);
  else fileDirectives.delete(file);
}
if (fileDirectives.size === 0) {
  console.log('No timed observation directives found.');
  process.exit(0);
}
detectDuplicates(fileDirectives);

const calc = mde.load(filePath, { calculusConfig: tillConfig, cache: false });

for (const [file, names] of fileDirectives) {
  console.log(path.relative(ROOT, file));
  for (const kind of names) {
    if (flags.only && kind !== flags.only && handlerFor(kind)[0] !== flags.only) continue;
    const [label, handler] = handlerFor(kind);
    const settings = calc.querySettings.get(kind);
    if (!settings || settings.settle == null) {   // null = unparseable value, e.g. (settle: -1)
      header(kind, '(missing settle: T setting)');
      continue;
    }
    const ownHash = calc.queries.get(kind);
    const queryHash = resolveQueryHash(calc, kind, ownHash, settings);
    header(kind, label);
    handler(calc, queryHash, settings, ownHash);
  }
}
