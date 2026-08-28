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
 *      negative-numerator input must REFUSE on both paths. The grade
 *      algebra's partial residual ⊖ (TODO_0273) is a third leg: it must
 *      agree with qsub on definedness (null ⟺ a < b) and value, and
 *      backward plus-solve (one addend free, result ground; both positions,
 *      ℕ and ℚ pairs) is fuzzed as: FFI complete (success ⟺ a ≥ b,
 *      H = a − b — num.plus tower dispatch incl. qplus solve modes), clause
 *      path sound-only (success ⇒ correct H; carry cases may hit the
 *      depth bound — plus/s4 subgoal order). No path derives a negative
 *      residual — the fence is derivational.
 *
 *   2. activation-spec trials: for random ground delay d, token stamp t,
 *      horizon h on the one-rule program `r: a -o { b }@(d)`:
 *        fires(settle(a@t, h))  ⟺  t ≤ h
 *        fired  ⇒ output stamped exactly t + d, next = null or > h
 *        pending ⇒ state unchanged, next = t
 *
 * Later sections (3-6): Theorem-1 exactness through the sequent bridge,
 * pure backward monad towers / retiming against BigInt oracles, the
 * cohort-firing differential (batch ≡ batch:false — state, next, and the
 * RLE event expansion, per seed), and ample-set containment (every
 * settle world, over many seeds, appears in settleExplore's leaves — the
 * 119a755e bug class, fuzz-scale).
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
import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import tillConfig, { loadTillSequent } from '../calculus/till/calculus-config.js';
import { buildTimedConfig } from '../lib/engine/timed/timed.js';
import { certifyRun } from '../lib/prover/timed/elaborate-trace.js';

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
const tillCfg = (await import('../calculus/till/calculus-config.js')).default;
const _tillFace = buildTimedConfig(tillCfg);   // derived hash faces (0284 audit)
const ec = mde.load(RAT_ILL, { calculusConfig: tillCfg, cache: false });
const theories = [...defaultTheories, binlitTheory, ratlitTheory];
const canonicalize = buildCanonicalizer(theories);
// till's FFI meta (num.* tower dispatch), not ILL's bin-only defaults —
// the fuzzer must exercise the same FFI face the till engine runs
const baseOpts = makeILLBackchainOpts({
  theories, normalize: canonicalize, getFFIMeta: tillCfg.backward.getFFIMeta,
});
const mv = (name) => Store.put('metavar', [name]);

function prove(goal, useFFI) {
  return backward.prove(goal, ec.clauses, ec.definitions, {
    ...baseOpts, maxDepth: 20000, allBuckets: true, useFFI,
  });
}

const QOPS = {
  plus: ([an, ad], [bn, bd]) => norm([an * bd + bn * ad, ad * bd]),
  qsub: ([an, ad], [bn, bd]) => norm([an * bd - bn * ad, ad * bd]),
  mul: ([an, ad], [bn, bd]) => norm([an * bn, ad * bd]),
  qdiv: ([an, ad], [bn, bd]) => norm([an * bd * (bn < 0n ? -1n : 1n), ad * (bn < 0n ? -bn : bn)]),
};
const QCMP = {
  lt: (a, b) => a[0] * b[1] < b[0] * a[1],
  le: (a, b) => a[0] * b[1] <= b[0] * a[1],
  eq: (a, b) => a[0] * b[1] === b[0] * a[1],
  neq: (a, b) => a[0] * b[1] !== b[0] * a[1],
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
  // algebra residual ⊖ (TODO_0273): must agree with qsub on definedness
  // and value — the algebra is to the theory what FFI is to clauses.
  // The fenced residual is the DERIVED hash face (buildTimedConfig, 0284
  // audit) — fuzzing it here pins the derivation, not a hand-written face.
  {
    trials++;
    const r = _tillFace.effect.residual(putRat(...a), putRat(...b));
    const neg = a[0] * b[1] < b[0] * a[1];
    const want = neg ? null : putRat(...QOPS.qsub(a, b));
    if (r !== want) {
      report(`residual(${rstr(a)}, ${rstr(b)}): got ${r === null ? 'null' : rstr(ratParts(r) || [0n, 0n])}, want ${want === null ? 'null' : rstr(QOPS.qsub(a, b))}`);
    }
  }
  // residual-as-backward-plus (TODO_0273): solve one addend of plus with
  // the result ground, over ℕ (bin fast path + tower fallback) AND ℚ
  // (qplus solve modes), in BOTH free positions.
  //   FFI path:    COMPLETE decision procedure — success ⟺ a ≥ b, H = a − b
  //     (num.plus: bin first-free mode, qplus solve modes for the rest).
  //   clause path: SOUND but search-incomplete (plus/s4 orders `plus M N Q`
  //     before `inc Q R`, so carry cases leave two subgoal vars free and SLD
  //     can diverge to the depth bound). Soundness only: success ⇒ correct
  //     H; no-proof tolerated. No path may ever derive a negative residual —
  //     the fence is derivational.
  if (i % 4 === 0) {
    const pairs = [
      [[BigInt(randInt(50)), 1n], [BigInt(randInt(50)), 1n]],   // ℕ pair
      [a, b],                                                    // ℚ pair
    ];
    for (const [pa, pb] of pairs) {
      const ge = pa[0] * pb[1] >= pb[0] * pa[1];
      const want = QOPS.qsub(pa, pb);
      for (const pos of [0, 1]) {
        for (const useFFI of [true, false]) {
          trials++;
          const H = mv('H');
          const args = pos === 0
            ? [H, putRat(...pb), putRat(...pa)]
            : [putRat(...pb), H, putRat(...pa)];
          const res = prove(Store.put('plus', args), useFFI);
          const label = `plus solve pos${pos} (${rstr(pa)} ⊖ ${rstr(pb)}) ${useFFI ? 'FFI' : 'clause'}`;
          if (res.success) {
            if (!ge) { report(`${label}: derived a negative residual (fence breach)`); continue; }
            let val = H;
            for (let k = 0; k < 500; k++) { const n = apply(val, res.theta); if (n === val) break; val = n; }
            if (canonicalize(val) !== putRat(...want)) {
              report(`${label}: got H=${rstr(ratParts(canonicalize(val)) || [0n, 0n])}, want ${rstr(want)}`);
            }
          } else if (useFFI && ge) {
            report(`${label}: FFI solve mode must be complete, want H=${rstr(want)}`);
          }
        }
      }
    }
  }
  // negative-numerator refusal (signed storage, unsigned ops — D14/round 11)
  if (i % 8 === 0) {
    trials++;
    const goal = Store.put('plus', [putRat(-a[0] - 1n, a[1]), putRat(...b), mv('R')]);
    for (const useFFI of [true, false]) {
      if (prove(goal, useFFI).success) {
        report(`plus(negative) ${useFFI ? 'FFI' : 'clause'}: proved despite ℚ≥0 contract`);
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

// ─── section 1b: gill min/max — FFI ∥ clause ∥ order reference ──────
// The collapsed tower names (TODO_0011 §3 / 0284 P2): gill's FFI meta
// routes min/max → num.min/num.max; the clause face lives in gill's
// prelude (num.gill /q instances at the bound). Reference = order-
// theoretic selection; coherence: the result IS one of the arguments.
{
  const NUM_GILL = path.join(import.meta.dirname, '../calculus/gill/prelude/num.gill');
  const gillCfg = (await import('../calculus/gill/calculus-config.js')).default;
  const gec = mde.load(NUM_GILL, { calculusConfig: gillCfg, cache: false });
  const gOpts = makeILLBackchainOpts({
    theories, normalize: canonicalize, getFFIMeta: gillCfg.backward.getFFIMeta,
  });
  const gprove = (goal, useFFI) => backward.prove(goal, gec.clauses, gec.definitions, {
    ...gOpts, maxDepth: 20000, allBuckets: true, useFFI,
  });
  let mtrials = 0, mfails = 0;
  const mreport = (msg) => { mfails++; fails++; console.error(`MISMATCH: ${msg}`); };
  for (let i = 0; i < COUNT; i++) {
    const a = randRat(), b = randRat();
    for (const op of ['min', 'max']) {
      mtrials++;
      const le = a[0] * b[1] <= b[0] * a[1];
      const want = op === 'min' ? (le ? a : b) : (le ? b : a);
      const out = mv('R');
      const goal = Store.put(op, [putRat(...a), putRat(...b), out]);
      for (const useFFI of [true, false]) {
        const res = gprove(goal, useFFI);
        if (!res.success) { mreport(`${op}(${rstr(a)}, ${rstr(b)}) ${useFFI ? 'FFI' : 'clause'}: no proof`); continue; }
        let val = out;
        for (let k = 0; k < 500; k++) { const n = apply(val, res.theta); if (n === val) break; val = n; }
        if (canonicalize(val) !== putRat(...want)) {
          mreport(`${op}(${rstr(a)}, ${rstr(b)}) ${useFFI ? 'FFI' : 'clause'}: got ${rstr(ratParts(canonicalize(val)) || [0n, 0n])}, want ${rstr(want)}`);
        }
      }
    }
  }
  console.log(`gill min/max: ${mtrials} trials, ${mfails} mismatches`);
}

// ─── section 2: activation-spec fuzzer (A@t fires under h iff t ≤ h) ─
const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'fuzz-till-'));
const cmpQ = (x, y) => { const l = x[0] * y[1], r = y[0] * x[1]; return l < r ? -1 : l > r ? 1 : 0; };
let atrials = 0, afails = 0;
const NPROGS = Math.max(4, Math.floor(COUNT / 16));
for (let p = 0; p < NPROGS; p++) {
  const d = norm(randRat({ nonNeg: true }));
  const file = path.join(dir, `act-${p}.ill`);
  fs.writeFileSync(file, `a: type.\nb: type.\nr: a -o { b }@(${d[0]}/${d[1]}).\n`);
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

// ─── section 3: Theorem-1 exactness (THY_0018 — ASAP = principal grade) ─
// For the one-rule program a ⊸ {b}@d from a@t, the operational stamp is
// u = t + d. v1 is EXACT accounting (stamped-atom subeffecting is Stage 2 —
// till.rules header): through the sequent prover with the settle bridge,
// the production claim {b@u'}@(u+1) from a@t is derivable ⟺ u' = u —
//   b@u       derivable    (soundness: the @fire instance is a derivation)
//   b@(u/2)   UNDERIVABLE  (minimality: no derivation beats the critical
//             path — {}L's partial residual ⊖ preserves the lower bound)
//   b@(u+1)   UNDERIVABLE  (exactness: the bridge's rightFocus matches
//             stamps exactly; retiming lifts CONTEXT stamps, not claims)
// Retiming (at_l) is witnessed where it lives, on hypothesis stamps:
//   b@u ⊢ b@(u+1) derivable, b@(u+1) ⊢ b@u underivable.
const calcSeq = loadTillSequent();
const { specs, alternatives } = buildRuleSpecs(calcSeq);
const prover = createProver(calcSeq);
let mtrials = 0, mfails = 0;
const mdir = fs.mkdtempSync(path.join(os.tmpdir(), 'fuzz-till-min-'));
const MPROGS = Math.max(3, Math.floor(COUNT / 32));
for (let p = 0; p < MPROGS; p++) {
  const d = norm(randRat({ nonNeg: true }));
  const file = path.join(mdir, `min-${p}.ill`);
  fs.writeFileSync(file, `a: type.\nb: type.\nr: a -o { b }@(${d[0]}/${d[1]}).\n`);
  const ec = mde.load(file, { calculusConfig: tillConfig, cache: false });
  const aAtom = Store.put('atom', ['a']);
  const bAtom = Store.put('atom', ['b']);
  for (let j = 0; j < 4; j++) {
    const t = norm(randRat({ nonNeg: true }));
    const u = norm([t[0] * d[1] + d[0] * t[1], t[1] * d[1]]);   // t + d
    const T = [u[0] + u[1], u[1]];                              // horizon u + 1
    const judge = (up) => {
      const succ = Store.put('monad', [putRat(...T), Store.put('at', [bAtom, putRat(...up)])]);
      const seq = Seq.fromArrays([Store.put('at', [aAtom, putRat(...t)])], [], succ);
      return prover.prove(seq, { rules: specs, alternatives, engineCalc: ec }).success;
    };
    mtrials += 2;
    if (!judge(u)) {
      mfails++; console.error(`MISMATCH: b@${rstr(u)} underivable at its operational stamp (t=${rstr(t)}, d=${rstr(d)})`);
    }
    if (judge([u[0] + u[1], u[1]])) {
      mfails++; console.error(`MISMATCH: b@(${rstr(u)}+1) derivable — exact accounting violated (t=${rstr(t)}, d=${rstr(d)})`);
    }
    if (u[0] > 0n) {
      mtrials++;
      if (judge(norm([u[0], u[1] * 2n]))) {
        mfails++; console.error(`MISMATCH: b@(${rstr(u)}/2) derivable — beats the critical path (t=${rstr(t)}, d=${rstr(d)})`);
      }
    }
    // at_l retiming on hypothesis stamps (delaying availability is free;
    // never early) — pure backward, no engine
    mtrials += 2;
    const u1 = [u[0] + u[1], u[1]];
    const retime = (from, to) => prover.prove(
      Seq.fromArrays([Store.put('at', [bAtom, putRat(...from)])], [],
        Store.put('at', [bAtom, putRat(...to)])),
      { rules: specs, alternatives }).success;
    if (!retime(u, u1)) {
      mfails++; console.error(`MISMATCH: retiming b@${rstr(u)} ⊢ b@(${rstr(u)}+1) underivable`);
    }
    if (retime(u1, u)) {
      mfails++; console.error(`MISMATCH: reverse retiming b@(${rstr(u)}+1) ⊢ b@${rstr(u)} derivable`);
    }
  }
}
fs.rmSync(mdir, { recursive: true, force: true });
console.log(`Thm1 minimality: ${mtrials} trials, ${mfails} mismatches`);

// ─── section 4: backward-prover fuzz — monad towers + at_l retiming ──
// Pure backward, no bridge (TODO_0274): the sequent prover itself against
// exact BigInt oracles, driving the theory premises (monad_l's `!qsub`,
// at_l's `!le`) with random rational grades.
//   towers:  {…{a}@d_i…} ⊢ {a}@f  derivable ⟺ f ≥ Σd_i (graded-μ + sub)
//   retime:  a@t1 ⊢ a@t2           derivable ⟺ t1 ≤ t2
// Every success must FULLY verify (kernel valid, no unverified steps) —
// pure sequent proofs have no bridge escape hatch.
const kernel4 = createKernel(calcSeq);
const fzAtom = Store.put('atom', ['fz']);
let btrials = 0, bfails = 0;
const BT = Math.max(60, Math.floor(COUNT / 2));
for (let i = 0; i < BT; i++) {
  const n = randInt(4);
  const ds = Array.from({ length: n }, () => norm(randRat()));
  const f = norm(randRat());
  let lhs = fzAtom;
  for (const d of ds) lhs = Store.put('monad', [putRat(...d), lhs]);
  const rhs = Store.put('monad', [putRat(...f), fzAtom]);
  const [sn, sd] = ds.reduce(([an, ad], [bn, bd]) => [an * bd + bn * ad, ad * bd], [0n, 1n]);
  const oracle = f[0] * sd >= sn * f[1];
  btrials++;
  const r = prover.prove(Seq.fromArrays([lhs], [], rhs), { rules: specs, alternatives });
  if (!!r.success !== oracle) {
    bfails++; console.error(`MISMATCH: tower [${ds.map(rstr).join(',')}] ⊢ @${rstr(f)}: prover=${!!r.success}, want ${oracle}`);
  } else if (r.success) {
    const v = kernel4.verifyTree(r.proofTree);
    if (!v.valid) { bfails++; console.error(`MISMATCH: tower kernel rejected: ${v.errors.join('; ')}`); }
    else if (v.unverified) { bfails++; console.error(`MISMATCH: tower proof has unverified steps: ${v.unverified}`); }
  }
  btrials++;
  const t1 = norm(randRat()), t2 = norm(randRat());
  const rOracle = t1[0] * t2[1] <= t2[0] * t1[1];
  const rr = prover.prove(
    Seq.fromArrays([Store.put('at', [fzAtom, putRat(...t1)])], [],
      Store.put('at', [fzAtom, putRat(...t2)])),
    { rules: specs, alternatives });
  if (!!rr.success !== rOracle) {
    bfails++; console.error(`MISMATCH: retime ${rstr(t1)} → ${rstr(t2)}: prover=${!!rr.success}, want ${rOracle}`);
  } else if (rr.success) {
    const v = kernel4.verifyTree(rr.proofTree);
    if (!v.valid || v.unverified) {
      bfails++; console.error(`MISMATCH: retime kernel: ${(v.errors || []).join('; ')} ${v.unverified || ''}`);
    }
  }
}
console.log(`backward prover: ${btrials} trials, ${bfails} mismatches`);

// ─── section 5: cohort-firing differential (TODO_0278 B1, audit) ────
// Random terminating programs with batching-prone shapes (counted
// produces, counted takes, windowed sweeps): settle with batch (default)
// must equal settle with { batch: false } — state-identical, same next,
// and the RLE expansion of the batched events must reproduce the
// sequential event list exactly (order included, per seed).
const canonState = (s) => {
  const lin = Object.entries(s.linear || {}).map(([h, c]) => `${h}x${c}`).sort();
  const per = Object.keys(s.persistent || {}).sort();
  return lin.join(',') + '|' + per.join(',');
};
const evKey = (e) => {
  const m = (o) => Object.entries(o || {}).map(([h, c]) => `${h}x${c}`).sort().join(' ');
  return `${e.rule}@${e.activation}[${m(e.consumed)}->${m(e.produced)}]`;
};
const expandEv = (events) =>
  events.flatMap(e => Array(e.multiplicity || 1).fill(e)).map(evKey).join(';');
const bdir = fs.mkdtempSync(path.join(os.tmpdir(), 'fuzz-till-batch-'));
let ktrials = 0, kfails = 0;
const KPROGS = Math.max(4, Math.floor(COUNT / 16));
for (let p = 0; p < KPROGS; p++) {
  const d1 = 1 + randInt(3), d2 = 1 + randInt(3), D = 1 + randInt(20);
  const K = 2 + randInt(5), J = 1 + randInt(3);
  const spoil = rand() < 0.5;
  const text = [
    `#import(${RAT_ILL})`,
    'a: type.', 'w: type.', 'p: type.',
    `gen: a -o { !_${K} w }@${d1}.`,
    `mill: !_${J} w -o { p }@${d2}.`,
    ...(spoil ? [`spoil: p@Q * after (Q+${D}) -o { I }.`] : []),
  ].join('\n');
  const file = path.join(bdir, `b-${p}.ill`);
  fs.writeFileSync(file, text);
  const calc = mde.load(file, { calculusConfig: tillConfig, cache: false });
  const aAtom = Store.put('atom', ['a']);
  const wAtom = Store.put('atom', ['w']);
  for (let j = 0; j < 4; j++) {
    ktrials++;
    const S = { linear: { [aAtom]: 1 + randInt(4), [wAtom]: randInt(20) } };
    const seed = randInt(1000);
    const on = calc.settle({ linear: { ...S.linear }, persistent: {} }, '1000', { seed });
    const off = calc.settle({ linear: { ...S.linear }, persistent: {} }, '1000', { seed, batch: false });
    if (canonState(on.state) !== canonState(off.state)) {
      kfails++; console.error(`MISMATCH batch state (K=${K} J=${J} spoil=${spoil} seed=${seed}):\n${text}`);
      continue;
    }
    if ((on.next || null) !== (off.next || null)) {
      kfails++; console.error(`MISMATCH batch next (seed=${seed}):\n${text}`);
      continue;
    }
    if (expandEv(on.events) !== expandEv(off.events)) {
      kfails++; console.error(`MISMATCH batch RLE expansion (seed=${seed}):\n${text}`);
    }
  }
}
fs.rmSync(bdir, { recursive: true, force: true });
console.log(`batch differential: ${ktrials} trials, ${kfails} mismatches`);

// ─── section 6: ample-set containment (settleExplore ⊇ settle worlds) ─
// Random programs with a persistent-consequent producer beside a
// !-guarded consumer (the 119a755e bug class): every settle outcome, over
// many seeds, must appear in settleExplore's leaf set — explore commits
// an order only when provably exhaustive (the ample-set condition).
const edir = fs.mkdtempSync(path.join(os.tmpdir(), 'fuzz-till-ample-'));
let etrials = 0, efails = 0;
const EPROGS = Math.max(4, Math.floor(COUNT / 16));
for (let p = 0; p < EPROGS; p++) {
  const d1 = randInt(3), d2 = 1 + randInt(2), d3 = 1 + randInt(2);
  const text = [
    'a: type.', 'b: type.', 'c: type.', 'res: type.', 'k: bin -> type.',
    `mk: a -o { !k 1 }@${d1}.`,
    `grab: b -o { c }@${d2}.`,
    `need: b * !k 1 -o { res }@${d3}.`,
  ].join('\n');
  const file = path.join(edir, `e-${p}.ill`);
  fs.writeFileSync(file, text);
  const calc = mde.load(file, { calculusConfig: tillConfig, cache: false });
  const aAtom = Store.put('atom', ['a']);
  const bAtom = Store.put('atom', ['b']);
  const S = () => ({ linear: { [aAtom]: 1, [bAtom]: 1 + randInt(2) }, persistent: {} });
  const s0 = S();
  const leaves = new Set(
    calc.settleExplore({ linear: { ...s0.linear }, persistent: {} }, '50')
      .leaves.map(l => canonState(l.state)));
  for (let seed = 0; seed < 20; seed++) {
    etrials++;
    const r = calc.settle({ linear: { ...s0.linear }, persistent: {} }, '50', { seed });
    if (!leaves.has(canonState(r.state))) {
      efails++; console.error(`MISMATCH ample set: seed ${seed} world missing from explore:\n${text}`);
    }
  }
}
fs.rmSync(edir, { recursive: true, force: true });
console.log(`ample-set containment: ${etrials} trials, ${efails} mismatches`);

// ─── section 7: run certification (TODO_0294 B4) — settle→elaborate→verify ─
// Random multi-rule programs with positive rational delays, plus the
// section-6 persistent shape: EVERY settle run must elaborate into an
// @fire chain the kernel FULLY re-derives from the program's rule data
// (fire-check.js, no modeSwitch trust). Elaboration is total on legal
// traces of supported rules (THY_0018 §5) — any non-'certified' verdict
// here is an engine/elaborator disagreement, i.e. a found bug.
const kernelSeq = createKernel(calcSeq);
const gdir = fs.mkdtempSync(path.join(os.tmpdir(), 'fuzz-till-cert-'));
let gtrials = 0, gfails = 0;
const GPROGS = Math.max(4, Math.floor(COUNT / 16));
const certHorizon = putRat(8n, 1n);
for (let p = 0; p <= GPROGS; p++) {
  const atoms = ['ca', 'cb', 'cc', 'cd', 'ce'];
  let text;
  if (p === GPROGS) {
    // fixed persistent-conclusion + persistent-goal shape (section 6 class)
    text = ['ca: type.', 'cb: type.', 'cres: type.', 'ck: bin -> type.',
      'mk: ca -o { !ck 1 }@1.',
      'need: cb * !ck 1 -o { cres }@1.'].join('\n');
  } else if (p === GPROGS - 1) {
    // fixed counted-take + counted-produce + whole-bind shape (gap closures)
    text = ['ca: type.', 'cb: type.', 'cw: bin -> type.',
      'trim: !_3 ca -o { !_2 cb }@1.',
      'allb: !_W cb -o { cw W }@2.'].join('\n');
  } else if (p === GPROGS - 2) {
    // fixed possessed-loli shape (Phase 6c: produced rule token fires)
    text = ['ca: type.', 'cb: type.', 'cc: type.',
      'mk: cc -o { (ca -o {cb}@2) }@1.'].join('\n');
  } else {
    const lines = atoms.map(x => `${x}: type.`);
    const R = 2 + randInt(3);
    for (let i = 0; i < R; i++) {
      // mass-nonincreasing (|outs| ≤ |ins|): random duplication rules
      // otherwise grow token counts exponentially under cohort batching
      // (the Int32 run-length fence throws — a guard, not a bug)
      const nIn = 1 + randInt(2);
      const ins = Array.from({ length: nIn }, () => atoms[randInt(atoms.length)]);
      const outs = Array.from({ length: 1 + randInt(nIn) }, () => atoms[randInt(atoms.length)]);
      const num = 1 + randInt(4), den = [1, 2, 4][randInt(3)];
      lines.push(`r${i}: ${ins.join(' * ')} -o { ${outs.join(' * ')} }@(${num}/${den}).`);
    }
    text = lines.join('\n');
  }
  const file = path.join(gdir, `c-${p}.ill`);
  fs.writeFileSync(file, text);
  const gc = mde.load(file, { calculusConfig: tillConfig, cache: false });
  const state = { linear: {}, persistent: {} };
  if (p >= GPROGS - 2) {
    state.linear[Store.put('atom', ['ca'])] = p === GPROGS - 1 ? 4 + randInt(5) : 1;
    state.linear[Store.put('atom', ['cb'])] = 1;
    if (p === GPROGS - 2) state.linear[Store.put('atom', ['cc'])] = 1;
  } else {
    for (const x of atoms) { const c = randInt(3); if (c) state.linear[Store.put('atom', [x])] = c; }
    if (!Object.keys(state.linear).length) state.linear[Store.put('atom', ['ca'])] = 1;
  }
  gtrials++;
  let r;
  try {
    r = certifyRun({
      engineCalc: gc, calculus: calcSeq, kernel: kernelSeq,
      state, horizon: '8', horizonTerm: certHorizon,
      settleOpts: { maxSteps: 500 },
    });
  } catch (e) {
    r = { verdict: 'threw', reason: e.message };
  }
  if (r.verdict !== 'certified') {
    gfails++;
    console.error(`MISMATCH certification: ${r.verdict} (${r.reason || (r.errors || []).join('; ')}) on:\n${text}`);
  }
}
fs.rmSync(gdir, { recursive: true, force: true });
console.log(`run certification: ${gtrials} trials, ${gfails} mismatches`);

const total = fails + afails + mfails + bfails + kfails + efails + gfails;
if (total > 0) { console.error(`FAIL: ${total} total mismatches (seed ${SEED})`); process.exit(1); }
console.log(`PASS (seed ${SEED})`);
