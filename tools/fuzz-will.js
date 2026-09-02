#!/usr/bin/env node
/**
 * will fuzzer — audit 2026-09-02 (fuzz-scale gates for the ∃_ρ surface).
 *
 * Three property families:
 *
 *   1. mass trials: random ℚ>0 priors over fixed linear-recursive grammar
 *      SHAPES (self-recursive datasort; mutually-recursive even/odd pair)
 *      — the exact solver (calculus/will/lib/datasort-mass.js, rational
 *      Gaussian elimination over SCCs) against an independent float
 *      power iteration of the same inside-mass system derived from the
 *      program TEXT. Fixed shapes, random coefficients: random shapes
 *      mostly violate the f1-f4 fences by construction; varying the
 *      rationals is what exercises the elimination. Supercritical draws
 *      must be a load error AND divergent under iteration.
 *
 *   2. B6 trials: on the same programs, every sample-mode collapse must
 *      report importance ≡ m(conditioning sort) EXACTLY (BigInt rational
 *      equality) for every seed — the zero-variance identity (THY_0030
 *      Proposition 2) at fuzz scale.
 *
 *   3. perturbation trials: a certified collapse tree (certifyCollapse)
 *      with one random mutation — weight numerator flip, token member
 *      swap, token drop, sort swap, mass-table doctor — must be REJECTED
 *      by kernel.verifyTree. Random perturbation is the standard
 *      adversarial gate for certificate checkers.
 *
 * Usage: node tools/fuzz-will.js [--count N] [--seed N] [--verbose]
 * Reports mismatches; exits non-zero on any failure.
 */
'use strict';

import fs from 'fs';
import os from 'os';
import path from 'path';
import { fileURLToPath } from 'url';
import Store from '../lib/kernel/store.js';
import mde from '../lib/engine/index.js';
import willConfig, { loadWillSequent } from '../calculus/will/calculus-config.js';
import { createKernel } from '../lib/prover/kernel.js';
import { certifyCollapse } from '../lib/prover/timed/elaborate-collapse.js';
import { programFromCalc } from '../lib/prover/timed/elaborate-trace.js';

const ROOT = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');
const MEASURE = path.join(ROOT, 'calculus/will/prelude/measure.will');

const args = process.argv.slice(2);
let COUNT = 60, SEED = 0x3111, VERBOSE = false;
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

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'fuzz-will-'));
process.on('exit', () => fs.rmSync(tmp, { recursive: true, force: true }));
let fileNo = 0;
const loadProg = (src) => {
  const f = path.join(tmp, `p${fileNo++}.will`);
  fs.writeFileSync(f, src);
  return mde.load(f, { calculusConfig: willConfig, cache: false });
};
const atom = (n) => Store.put('atom', [n]);
let failures = 0;
const fail = (msg) => { failures++; console.error(`FAIL: ${msg}`); };

// ── grammar shapes: random ℚ>0 priors, fixed fence-respecting structure ──
// prior as "n/d" text + float value. Base-member priors range freely;
// the recursive-constructor prior is drawn small so the recursion
// coefficient a = pcons·m(bit) lands mostly subcritical with a real
// supercritical tail (both branches stay exercised).
const randPrior = () => {
  const n = 1 + randInt(6), d = 1 + randInt(4);
  return { txt: d === 1 ? `${n}` : `${n}/${d}`, val: n / d };
};
const randConsPrior = () => {
  const n = 1 + randInt(3), d = 5 + randInt(8);
  return { txt: `${n}/${d}`, val: n / d };
};

/** shape A: self-recursive datasort over a cons-list.
 *  m(bit) = pb0+pb1; m(lst) = pnil + pcons·m(bit)·m(lst);
 *  m(ok)  = pnil + pcons·m(bit)·m(ok). Subcritical iff pcons·m(bit) < 1. */
function shapeA() {
  const pb0 = randPrior(), pb1 = randPrior(), pnil = randPrior(), pcons = randConsPrior();
  const src = `#import(${MEASURE})
bit: sort.
b0: bit @w ${pb0.txt}.
b1: bit @w ${pb1.txt}.
lst: sort.
nil: lst @w ${pnil.txt}.
cons: (h: bit) -> (t: lst) -> lst @w ${pcons.txt}.
ok <: lst.
ok/n: ok nil.
ok/c: ok (cons H T) <- ok T.
mk: type.
box: (x: lst) -> type.
spawn: mk -o { exists X: ok @w. box X }.
`;
  const mbit = pb0.val + pb1.val;
  const a = pcons.val * mbit;   // recursion coefficient for lst AND ok
  const iterate = () => {       // independent power iteration (200 steps)
    let mlst = 0, mok = 0;
    for (let k = 0; k < 200; k++) { mlst = pnil.val + a * mlst; mok = pnil.val + a * mok; }
    return { lst: mlst, ok: mok, bit: mbit };
  };
  return { src, sub: a < 1 - 1e-9, sup: a > 1 + 1e-9, iterate, sort: 'ok' };
}

/** shape B: mutually-recursive even/odd over the same list grammar.
 *  m(even) = pnil + pcons·m(bit)·m(odd); m(odd) = pcons·m(bit)·m(even). */
function shapeB() {
  const pb0 = randPrior(), pb1 = randPrior(), pnil = randPrior(), pcons = randConsPrior();
  const src = `#import(${MEASURE})
bit: sort.
b0: bit @w ${pb0.txt}.
b1: bit @w ${pb1.txt}.
lst: sort.
nil: lst @w ${pnil.txt}.
cons: (h: bit) -> (t: lst) -> lst @w ${pcons.txt}.
even <: lst.
odd <: lst.
even/n: even nil.
even/c: even (cons H T) <- odd T.
odd/c: odd (cons H T) <- even T.
mk: type.
box: (x: lst) -> type.
spawn: mk -o { exists X: even @w. box X }.
`;
  const mbit = pb0.val + pb1.val;
  const a = pcons.val * mbit;
  const iterate = () => {
    let me = 0, mo = 0, mlst = 0;
    for (let k = 0; k < 400; k++) {
      const e2 = pnil.val + a * mo, o2 = a * me;
      mlst = pnil.val + a * mlst; me = e2; mo = o2;
    }
    return { even: me, odd: mo, lst: mlst, bit: mbit };
  };
  return { src, sub: a < 1 - 1e-9, sup: a > 1 + 1e-9, iterate, sort: 'even' };
}

const ratVal = ([n, d]) => Number(n) / Number(d);
const ratEq = (a, b) => a && b && a[0] * b[1] === b[0] * a[1];

// ── 1 + 2: mass agreement + B6 invariant ────────────────────────────
let massTrials = 0, b6Trials = 0, skippedCritical = 0;
for (let t = 0; t < COUNT; t++) {
  const shape = t % 2 === 0 ? shapeA() : shapeB();
  if (!shape.sub && !shape.sup) { skippedCritical++; continue; }   // near-critical: skip
  let calc = null, err = null;
  try { calc = loadProg(shape.src); } catch (e) { err = e; }
  if (shape.sup) {
    if (!err || !/critical|singular|negative|diverg/i.test(err.message)) {
      fail(`trial ${t}: supercritical grammar loaded without divergence error (a>1)`);
    }
    continue;
  }
  if (err) { fail(`trial ${t}: subcritical grammar refused: ${err.message}`); continue; }
  massTrials++;
  const ref = shape.iterate();
  for (const [s, want] of Object.entries(ref)) {
    const got = calc.masses && calc.masses.get(s);
    if (!got) {
      if (s === 'bit' || s === 'lst') continue;   // classifier masses may be keyed differently
      fail(`trial ${t}: no solved mass for '${s}'`); continue;
    }
    const g = ratVal(got);
    if (Math.abs(g - want) > 1e-6 * Math.max(1, Math.abs(want))) {
      fail(`trial ${t}: m(${s}) solver=${g} power-iteration=${want}`);
    }
  }
  // B6: importance ≡ m(conditioning sort) exactly, every seed
  const mS = calc.masses.get(shape.sort);
  for (let seed = 0; seed < 5; seed++) {
    b6Trials++;
    const r = calc.collapse({ linear: { [atom('mk')]: 1 }, persistent: {} }, { seed: SEED + seed });
    if (!r.ground) { fail(`trial ${t} seed ${seed}: collapse not ground`); continue; }
    if (!ratEq(r.importance, mS)) {
      fail(`trial ${t} seed ${seed}: importance ${r.importance} ≠ m(${shape.sort}) ${mS}`);
    }
  }
}

// ── 3: certificate perturbation ─────────────────────────────────────
const CERT_SRC = `#import(${MEASURE})
tile_t: sort.
sea: tile_t @w 2.
coast: tile_t @w 1.
land: tile_t @w 2.
warm <: tile_t.
warm/s: warm sea.
warm/c: warm coast.
mk: type.
tile: (t: tile_t) -> type.
spawn: mk -o { exists T: warm @w. tile T }.
`;
const certCalc = loadProg(CERT_SRC);
const seqCalc = loadWillSequent();
const kernel = createKernel(seqCalc);
const drawNodes = (node, acc = []) => {
  if (node.state && node.state.draw) acc.push(node);
  for (const p of node.premises || []) drawNodes(p, acc);
  return acc;
};
const PERTURB = [
  ['weight-flip', (r) => {
    const ds = drawNodes(r.tree).filter((n) => !n.state.draw.open);
    if (!ds.length) return false;
    const d = ds[randInt(ds.length)].state.draw;
    d.weight = [d.weight[0] + 1n + BigInt(randInt(5)), d.weight[1]];
    return true;
  }],
  ['member-swap', (r) => {
    const ds = drawNodes(r.tree).filter((n) => !n.state.draw.open);
    if (!ds.length) return false;
    const d = ds[randInt(ds.length)].state.draw;
    const other = d.member === 'sea' ? 'coast' : 'sea';
    d.member = other; d.witness = atom(other);   // consistent lie: weight/tokens now disagree
    return true;
  }],
  ['sort-swap', (r) => {
    const ds = drawNodes(r.tree).filter((n) => !n.state.draw.open);
    if (!ds.length) return false;
    ds[randInt(ds.length)].state.draw.sort = 'tile_t';   // wave says warm
    return true;
  }],
  ['nonmember-witness', (r) => {
    const ds = drawNodes(r.tree).filter((n) => !n.state.draw.open);
    if (!ds.length) return false;
    const d = ds[randInt(ds.length)].state.draw;
    d.member = 'land'; d.witness = atom('land');   // outside warm
    return true;
  }],
];
let perturbTrials = 0;
for (let t = 0; t < Math.max(12, COUNT / 4); t++) {
  const r = certifyCollapse({
    engineCalc: certCalc, calculus: seqCalc, kernel,
    state: { linear: { [atom('mk')]: 1 }, persistent: {} },
    collapseOpts: { seed: SEED + 1000 + t },
  });
  if (r.verdict !== 'certified') { fail(`perturb trial ${t}: base run not certified: ${r.reason}`); continue; }
  const [name, mutate] = PERTURB[t % PERTURB.length];
  if (!mutate(r)) continue;
  perturbTrials++;
  const v = kernel.verifyTree(r.tree, { program: programFromCalc(certCalc) });
  if (v.valid) fail(`perturb trial ${t}: '${name}' mutation ACCEPTED by verifyTree`);
}

console.log(`fuzz-will: ${massTrials} mass trials, ${b6Trials} B6 draws, ${perturbTrials} perturbations, ${skippedCritical} near-critical skipped (seed ${SEED})`);
if (failures > 0) { console.error(`FAIL: ${failures} total failures (seed ${SEED})`); process.exit(1); }
console.log('all properties held');
