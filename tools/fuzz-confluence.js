#!/usr/bin/env node
/**
 * certifyConfluence fuzzer (audit item 8, THY_0036).
 *
 * Generates small random keyed token programs + initial states in the
 * destination-discipline's shape and checks, per trial:
 *
 *   1. SOUNDNESS (the property the certificate asserts): certified ⇒
 *      (a) exhaustive explore reaches ONE final state across every
 *          enumerated interleaving;
 *      (b) committed exec is invariant under RULE-ORDER permutation —
 *          a reloaded shuffle of the same rules reaches the same
 *          value-level final state (genuinely different commitment
 *          choices, beyond explore's per-rule under-approximation);
 *      (c) explore under the certificate prunes to exactly one leaf
 *          equal to the common final state (the opts.confluence wire).
 *   2. TAXONOMY: every refusal reason is one of the 20 pinned reasons
 *      (THY_0036 §6) — no unnamed refusal path.
 *   3. PERTURBATION: a certified trial with an injected duplicate
 *      destination must flip to refusal (D6 at fuzz scale).
 *
 * Programs terminate by construction: dispatch markers strictly
 * increase on every fire (measure argument), so explore/exec always
 * quiesce and final-state comparison is total.
 *
 * Usage: node tools/fuzz-confluence.js [--count N] [--seed N] [--verbose]
 * Reports failures; exits non-zero on any.
 */
'use strict';

import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../lib/kernel/store.js';
import illmde from '../calculus/ill/index.js';
import { getAllLeaves } from '../lib/engine/tree-utils.js';
import { toObject } from '../lib/engine/fact-set.js';
import { stateHashStr } from '../lib/engine/explore.js';
import { show } from '../lib/engine/show.js';

// The 20 pinned refusal reasons (THY_0036 §6) — a refusal outside this
// set is an unnamed refusal path, itself a failure.
const TAXONOMY = new Set([
  'no-connective-info', 'no-dispatch-declared',
  'timed-feature', 'internal-choice', 'existential-consequent',
  'dynamic-rule-production', 'unkeyed-pattern', 'multi-destination',
  'dispatch-arity', 'guard-production', 'unkeyed-production',
  'non-slot-reuse-production', 'unguarded-cell-production',
  'underdetermined-instance', 'overlapping-dispatch',
  'dynamic-rule-in-state', 'unkeyed-state-fact', 'duplicate-destination',
  'duplicate-persistent-value', 'guard-cell-coexistence',
]);

const DISC = {
  dest: { cf_tok: 0 },
  dispatch: 'cf_tok',
  persistentUnique: { cf_cell: { keys: [0], values: [1] } },
};

const HEADER =
  'cf_tok: (d: bin) -> (m: bin) -> type.\n' +
  'cf_sink: (d: bin) -> (m: bin) -> type.\n' +
  'cf_cell: (a: bin) -> (b: bin) -> type.\n';

// ─── Seeded PRNG (xorshift32) ───────────────────────────────────────
function makeRng(seed) {
  let s = (seed >>> 0) || 0x9e3779b9;
  return () => {
    s ^= s << 13; s >>>= 0;
    s ^= s >> 17;
    s ^= s << 5; s >>>= 0;
    return s / 0x100000000;
  };
}
const irnd = (rng, n) => Math.floor(rng() * n);

// ─── Generator ──────────────────────────────────────────────────────
// Markers 1..4, every rule fires m → m' with m' > m: termination by
// measure. Overlap (two rules on one marker), cell demands (equal =
// overlap survives → refusal; distinct ground = D2 exclusion), sinks
// (produce-only exemption), and D6 state violations are all reachable.
function genRules(rng) {
  const n = 1 + irnd(rng, 3);
  const lines = [];
  for (let i = 0; i < n; i++) {
    const m = 1 + irnd(rng, 3);                 // 1..3
    const m2 = m + 1 + irnd(rng, 4 - m);        // m+1..4
    const cell = rng() < 0.5 ? ` * !cf_cell D ${3 + irnd(rng, 2)}` : '';
    const sink = rng() < 0.4 ? ` * cf_sink D ${m2}` : '';
    lines.push(`rf${i}: cf_tok D ${m}${cell} -o { cf_tok D ${m2}${sink} }.`);
  }
  return lines;
}

function genState(rng) {
  const dests = [5, 6, 7];
  const facts = [];
  const nTok = 1 + irnd(rng, 3);
  for (let i = 0; i < nTok; i++) {
    // duplicate destinations reachable (10%): D6 must refuse them
    const d = rng() < 0.1 && facts.length
      ? facts[0].d : dests[irnd(rng, dests.length)];
    facts.push({ d, s: `cf_tok ${d} ${1 + irnd(rng, 3)}` });
  }
  const cells = [];
  const nCell = irnd(rng, 3);
  for (let i = 0; i < nCell; i++) {
    const k = dests[irnd(rng, dests.length)];
    cells.push(`!cf_cell ${k} ${3 + irnd(rng, 2)}`);
  }
  return { text: [...facts.map(f => f.s), ...cells].join(' * '), toks: facts };
}

// ─── Harness ────────────────────────────────────────────────────────
function loadProg(lines) {
  Store.clear();
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'fuzz-confl-'));
  const file = path.join(tmpDir, 'p.ill');
  fs.writeFileSync(file, HEADER + lines.join('\n') + '\n');
  try {
    return illmde.load(file, { cache: false });
  } finally {
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  }
}

const parseState = (text) =>
  illmde.decomposeQuery(illmde.parseExpr(text, illmde.illConfig.loader));

// Value-level rendering — Store ids differ across loads.
function finalStateKey(state) {
  const lin = Object.entries(state.linear || {})
    .filter(([, c]) => c > 0)
    .map(([h, c]) => `${show(Number(h))}x${c}`);
  const pers = Object.keys(state.persistent || {}).map(h => show(Number(h)));
  return [...lin.sort(), '|', ...pers.sort()].join(' ');
}

function runTrials({ count = 60, seed = 1, verbose = false } = {}) {
  const rng = makeRng(seed);
  const failures = [];
  let certified = 0, refused = 0;

  for (let t = 0; t < count; t++) {
    const rules = genRules(rng);
    const st = genState(rng);
    const label = `trial ${t} (seed ${seed})`;
    let calc, state, cert;
    try {
      calc = loadProg(rules);
      state = parseState(st.text);
      cert = calc.certifyConfluence(state, DISC);
    } catch (e) {
      failures.push(`${label}: harness error: ${e.message}\n  rules: ${rules.join(' ')}\n  state: ${st.text}`);
      continue;
    }

    if (!cert.confluent) {
      refused++;
      // Leg 2: taxonomy totality
      if (!TAXONOMY.has(cert.witness.reason)) {
        failures.push(`${label}: refusal reason '${cert.witness.reason}' outside the pinned taxonomy`);
      }
      if (verbose) console.log(`${label}: refused (${cert.witness.reason})`);
      continue;
    }
    certified++;

    // Leg 1a: exhaustive explore — one final state
    const tree = calc.explore(state, { maxDepth: 64 });
    const leaves = getAllLeaves(tree).filter(l => l.type === 'leaf');
    const distinct = new Set(leaves.map(l => stateHashStr(toObject(l.state))));
    if (distinct.size !== 1) {
      failures.push(`${label}: CERTIFIED but explore found ${distinct.size} distinct final states\n  rules: ${rules.join(' ')}\n  state: ${st.text}`);
      continue;
    }

    // Leg 1c: certificate-pruned explore — one leaf, the same state
    const pruned = calc.explore(state, { maxDepth: 64, confluence: cert });
    const prunedLeaves = getAllLeaves(pruned).filter(l => l.type === 'leaf');
    if (prunedLeaves.length !== 1 ||
        stateHashStr(toObject(prunedLeaves[0].state)) !== [...distinct][0]) {
      failures.push(`${label}: certificate-pruned explore diverged from the common final state`);
      continue;
    }

    // Leg 1b: committed exec invariant under rule-order permutation
    const res1 = calc.exec(parseState(st.text), { maxSteps: 200 });
    const shuffled = [...rules];
    for (let i = shuffled.length - 1; i > 0; i--) {
      const j = irnd(rng, i + 1);
      [shuffled[i], shuffled[j]] = [shuffled[j], shuffled[i]];
    }
    const key1 = finalStateKey(res1.state);
    const q1 = res1.quiescent;
    const calc2 = loadProg(shuffled);  // clears the Store — render keys first
    const res2 = calc2.exec(parseState(st.text), { maxSteps: 200 });
    if (!q1 || !res2.quiescent) {
      failures.push(`${label}: terminating-by-construction program did not quiesce`);
      continue;
    }
    const key2 = finalStateKey(res2.state);
    if (key1 !== key2) {
      failures.push(`${label}: CERTIFIED but exec diverged under rule reordering\n  order A: ${key1}\n  order B: ${key2}\n  rules: ${rules.join(' ')}\n  state: ${st.text}`);
      continue;
    }

    // Leg 3: perturbation — duplicate destination must refuse
    const dupTok = st.toks[0];
    const calc3 = loadProg(rules);
    const perturbed = parseState(`${st.text} * cf_tok ${dupTok.d} 2`);
    const cert3 = calc3.certifyConfluence(perturbed, DISC);
    if (cert3.confluent) {
      failures.push(`${label}: duplicate-destination perturbation still certified`);
    }

    if (verbose) console.log(`${label}: certified, ${leaves.length} interleavings, all legs held`);
  }

  return { certified, refused, failures };
}

// ─── CLI ────────────────────────────────────────────────────────────
const isMain = process.argv[1] &&
  path.resolve(process.argv[1]) === path.resolve(new URL(import.meta.url).pathname);
if (isMain) {
  const args = process.argv.slice(2);
  const opt = (name, dflt) => {
    const i = args.indexOf(`--${name}`);
    return i >= 0 ? Number(args[i + 1]) : dflt;
  };
  const res = runTrials({
    count: opt('count', 60),
    seed: opt('seed', 1),
    verbose: args.includes('--verbose'),
  });
  console.log(`fuzz-confluence: ${res.certified} certified, ${res.refused} refused, ${res.failures.length} failures`);
  for (const f of res.failures) console.error(`FAIL ${f}`);
  process.exit(res.failures.length ? 1 : 0);
}

export { runTrials };
