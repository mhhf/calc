#!/usr/bin/env node
/**
 * till fuzzer — TODO_0265 Phase 5 (infrastructure map: fuzz-till).
 *
 * Two property families, both against exact BigInt references:
 *
 *   1. q-operation trials: random ℚ≥0 rationals through the overloaded
 *      arithmetic/comparison family (qplus/qsub/qmul/qdiv, qlt/qle/qeq/
 *      qneq), FFI path AND clause path (prelude/rat.ill), each compared to
 *      a BigInt cross-multiplication reference — the FFI-principle gate
 *      (FFI is optimization, theory is semantics) at fuzz scale. The ℚ≥0
 *      contract (audit round 11) is fuzzed too: qsub with a < b and any
 *      negative-numerator input must REFUSE on both paths.
 *
 *   2. activation-spec trials: for random ground delay d, token stamp t,
 *      horizon h on the one-rule program `r: a -o { b }@(d)`:
 *        fires(settle(a@t, h))  ⟺  t ≤ h
 *        fired  ⇒ output stamped exactly t + d, next = null or > h
 *        pending ⇒ state unchanged, next = t
 *
 * Usage: node tools/fuzz-till.js [--count N] [--seed N] [--verbose]
 * Reports mismatches; exits non-zero on any failure.
 */
'use strict';

import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../lib/kernel/store.js';
import mde from '../lib/engine/index.js';
import backward from '../lib/engine/backchain.js';
import { makeILLBackchainOpts } from '../lib/engine/ill/backchain-ill.js';
import { binlitTheory } from '../lib/engine/ill/binlit-theory.js';
import { ratlitTheory, ratParts, installRatlitTheory } from '../lib/engine/theories/ratlit-theory.js';
import { defaultTheories, buildCanonicalizer } from '../lib/kernel/eq-theory.js';
import { apply } from '../lib/kernel/substitute.js';
import { putRat } from '../lib/kernel/rat-term.js';
import tillConfig from '../calculus/till/calculus-config.js';

const args = process.argv.slice(2);
let COUNT = 200, SEED = 0x7111, VERBOSE = false;
for (let i = 0; i < args.length; i++) {
  if (args[i] === '--count' && args[i + 1]) COUNT = parseInt(args[++i]);
  if (args[i] === '--seed' && args[i + 1]) SEED = parseInt(args[++i]);
  if (args[i] === '--verbose') VERBOSE = true;
}

let rngState = SEED | 1;
const rand = () => {
  rngState ^= rngState << 13; rngState ^= rngState >>> 17; rngState ^= rngState << 5;
  return (rngState >>> 0) / 0x100000000;
};
const randInt = (n) => Math.floor(rand() * n);

/** Random ℚ≥0 rational [n, d]: n in [0, 63], d in [1, 16]. */
function randRat() {
  return [BigInt(randInt(64)), BigInt(1 + randInt(16))];
}
const gcd = (a, b) => { a = a < 0n ? -a : a; while (b) [a, b] = [b, a % b]; return a; };
const norm = ([n, d]) => { if (n === 0n) return [0n, 1n]; const g = gcd(n, d); return [n / g, d / g]; };
const rstr = ([n, d]) => (d === 1n ? `${n}` : `${n}/${d}`);

// ─── section 1: q-operations, FFI ∥ clause ∥ BigInt reference ───────
const RAT_ILL = path.join(import.meta.dirname, '../calculus/till/prelude/rat.ill');
Store.clear();
installRatlitTheory();
const ec = mde.load(RAT_ILL);
const theories = [...defaultTheories, binlitTheory, ratlitTheory];
const canonicalize = buildCanonicalizer(theories);
const baseOpts = makeILLBackchainOpts({ theories, normalize: canonicalize });
const mv = (name) => Store.put('metavar', [name]);

function prove(goal, useFFI) {
  return backward.prove(goal, ec.clauses, ec.definitions, {
    ...baseOpts, maxDepth: 20000, allBuckets: true, useFFI,
  });
}

const QOPS = {
  qplus: ([an, ad], [bn, bd]) => norm([an * bd + bn * ad, ad * bd]),
  qsub: ([an, ad], [bn, bd]) => norm([an * bd - bn * ad, ad * bd]),
  qmul: ([an, ad], [bn, bd]) => norm([an * bn, ad * bd]),
  qdiv: ([an, ad], [bn, bd]) => norm([an * bd * (bn < 0n ? -1n : 1n), ad * (bn < 0n ? -bn : bn)]),
};
const QCMP = {
  qlt: (a, b) => a[0] * b[1] < b[0] * a[1],
  qle: (a, b) => a[0] * b[1] <= b[0] * a[1],
  qeq: (a, b) => a[0] * b[1] === b[0] * a[1],
  qneq: (a, b) => a[0] * b[1] !== b[0] * a[1],
};

let fails = 0, trials = 0;
const report = (msg) => { fails++; console.error(`MISMATCH: ${msg}`); };

for (let i = 0; i < COUNT; i++) {
  const a = randRat(), b = randRat();
  for (const [op, ref] of Object.entries(QOPS)) {
    if (op === 'qdiv' && b[0] === 0n) continue;
    // ℚ≥0 contract: qsub a b with a < b must refuse on BOTH paths
    const refuses = op === 'qsub' && a[0] * b[1] < b[0] * a[1];
    trials++;
    const out = mv('R');
    const goal = Store.put(op, [putRat(...a), putRat(...b), out]);
    for (const useFFI of [true, false]) {
      const res = prove(goal, useFFI);
      if (refuses) {
        if (res.success) report(`${op}(${rstr(a)}, ${rstr(b)}) ${useFFI ? 'FFI' : 'clause'}: proved a negative (ℚ≥0 contract)`);
        continue;
      }
      if (!res.success) { report(`${op}(${rstr(a)}, ${rstr(b)}) ${useFFI ? 'FFI' : 'clause'}: no proof`); continue; }
      let val = out;
      for (let k = 0; k < 500; k++) { const n = apply(val, res.theta); if (n === val) break; val = n; }
      const expected = putRat(...ref(a, b));
      if (canonicalize(val) !== expected) {
        report(`${op}(${rstr(a)}, ${rstr(b)}) ${useFFI ? 'FFI' : 'clause'}: got ${rstr(ratParts(canonicalize(val)) || [0n, 0n])}, want ${rstr(ref(a, b))}`);
      }
    }
  }
  // negative-numerator refusal (signed storage, unsigned ops — D14/round 11)
  if (i % 8 === 0) {
    trials++;
    const goal = Store.put('qplus', [putRat(-a[0] - 1n, a[1]), putRat(...b), mv('R')]);
    for (const useFFI of [true, false]) {
      if (prove(goal, useFFI).success) {
        report(`qplus(negative) ${useFFI ? 'FFI' : 'clause'}: proved despite ℚ≥0 contract`);
      }
    }
  }
  for (const [op, ref] of Object.entries(QCMP)) {
    trials++;
    const goal = Store.put(op, [putRat(...a), putRat(...b)]);
    const expected = ref(a, b);
    for (const useFFI of [true, false]) {
      const res = prove(goal, useFFI);
      if (res.success !== expected) {
        report(`${op}(${rstr(a)}, ${rstr(b)}) ${useFFI ? 'FFI' : 'clause'}: provable=${res.success}, want ${expected}`);
      }
    }
  }
}
console.log(`q-operations: ${trials} trials, ${fails} mismatches`);

// ─── section 2: activation-spec fuzzer (A@t fires under h iff t ≤ h) ─
const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'fuzz-till-'));
const cmpQ = (x, y) => { const l = x[0] * y[1], r = y[0] * x[1]; return l < r ? -1 : l > r ? 1 : 0; };
let atrials = 0, afails = 0;
const NPROGS = Math.max(4, Math.floor(COUNT / 16));
for (let p = 0; p < NPROGS; p++) {
  const d = norm(randRat({ nonNeg: true }));
  const file = path.join(dir, `act-${p}.ill`);
  fs.writeFileSync(file, `r: a -o { b }@(${d[0]}/${d[1]}).\n`);
  const calc = mde.load(file, { calculusConfig: tillConfig, cache: false });
  const aAtom = Store.put('atom', ['a']);
  const bAtom = Store.put('atom', ['b']);
  for (let j = 0; j < 8; j++) {
    atrials++;
    const t = norm(randRat({ nonNeg: true }));
    const h = norm(randRat({ nonNeg: true }));
    const S = { linear: { [Store.put('at', [aAtom, putRat(...t)])]: 1 }, persistent: {} };
    const res = calc.settle(S, rstr(h));
    const shouldFire = cmpQ(t, h) <= 0;
    const facts = Object.keys(res.state.linear).map(Number);
    const fired = res.events.length === 1;
    if (fired !== shouldFire) {
      afails++; console.error(`MISMATCH: a@${rstr(t)} settle(${rstr(h)}) d=${rstr(d)}: fired=${fired}, want ${shouldFire}`);
      continue;
    }
    if (shouldFire) {
      const want = Store.put('at', [bAtom, putRat(...norm([t[0] * d[1] + d[0] * t[1], t[1] * d[1]]))]);
      if (!(facts.length === 1 && facts[0] === want && res.state.linear[want] === 1)) {
        afails++; console.error(`MISMATCH: a@${rstr(t)} d=${rstr(d)}: output not b@t+d`);
      }
    } else {
      const still = Store.put('at', [aAtom, putRat(...t)]);
      if (!(facts.length === 1 && facts[0] === still) || cmpQ(ratParts(res.next), t) !== 0) {
        afails++; console.error(`MISMATCH: a@${rstr(t)} settle(${rstr(h)}): pending state/next wrong`);
      }
    }
    if (VERBOSE) console.log(`ok a@${rstr(t)} h=${rstr(h)} d=${rstr(d)} fired=${fired}`);
  }
}
fs.rmSync(dir, { recursive: true, force: true });
console.log(`activation spec: ${atrials} trials, ${afails} mismatches`);

if (fails + afails > 0) { console.error(`FAIL: ${fails + afails} total mismatches (seed ${SEED})`); process.exit(1); }
console.log(`PASS (seed ${SEED})`);
