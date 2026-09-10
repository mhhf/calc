#!/usr/bin/env node
/**
 * Mode-system decision-procedure fuzzer (audit remediation, THY_0039 §6).
 *
 * The load-time well-modedness checker rests on two small decision procedures
 * whose subtlety is the reason the repo fuzzes its decision procedures
 * (fuzz-ffi, fuzz-confluence, fuzz-till). This fuzzes both against brute force:
 *
 *   1. orderUnsat — SOUNDNESS: if it reports UNSAT, no assignment over a bounded
 *      integer window satisfies the conjunction (a FALSE UNSAT would fabricate a
 *      spurious exclusivity certificate and mis-certify a non-functional
 *      predicate, §6.1). Completeness (missed UNSATs) is reported as info only.
 *   2. guardCoverageVerdict — EXACTNESS: over the discrete floor-0 domain the
 *      rep-point verdict must agree with exhaustive evaluation over [0, WIN):
 *      'ok' ⇔ every point has exactly one feasible alternative; 'uncovered' ⇒
 *      some point has none; 'overlap' ⇒ some point has more than one. A
 *      disagreement on 'ok' means the rep-point set missed a cell (unsound V2).
 *
 * Windows are sized above the max constant so any bounded model / cell is in
 * range; false passes from out-of-window witnesses are therefore negligible.
 *
 * Usage: node tools/fuzz-well-moded.js [--count N] [--seed N] [--verbose]
 * Reports failures; exits non-zero on any.
 */
'use strict';

import { orderUnsat, guardCoverageVerdict } from '../lib/engine/well-moded.js';

const argv = process.argv.slice(2);
const getArg = (flag, def) => { const i = argv.indexOf(flag); return i >= 0 ? Number(argv[i + 1]) : def; };
const COUNT = getArg('--count', 2000);
const SEED = getArg('--seed', 0x9E3779B9);
const VERBOSE = argv.includes('--verbose');

// mulberry32 — deterministic, seedable.
function rng(seed) {
  let s = seed >>> 0;
  return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}

const r = rng(SEED);
const pick = (n) => Math.floor(r() * n);

// ── 1. orderUnsat soundness ─────────────────────────────────────────
const SYMS = ['a', 'b', 'c', 'd'];
const OPS = ['=', '≠', '<', '<='];
const MAXC = 6;
const WIN = MAXC + SYMS.length + 2; // any model of the fragment lives in [0,WIN)
const holdsRel = (op, x, y) => (op === '=' ? x === y : op === '≠' ? x !== y : op === '<' ? x < y : x <= y);

function orderUnsatTrial() {
  const n = 1 + pick(8);
  const randOperand = () => (r() < 0.5 ? { s: SYMS[pick(SYMS.length)] } : { c: BigInt(pick(MAXC + 1)) });
  const atoms = [];
  for (let i = 0; i < n; i++) atoms.push({ op: OPS[pick(OPS.length)], a: randOperand(), b: randOperand() });
  const said = orderUnsat(atoms);
  // brute force over [0,WIN)
  const val = (o, asg) => (o.c !== undefined ? Number(o.c) : asg[o.s]);
  const used = [...new Set(atoms.flatMap((at) => [at.a, at.b]).filter((o) => o.s !== undefined).map((o) => o.s))];
  const asg = {};
  const search = (idx) => {
    if (idx === used.length) return atoms.every((at) => holdsRel(at.op, val(at.a, asg), val(at.b, asg)));
    for (let v = 0; v < WIN; v++) { asg[used[idx]] = v; if (search(idx + 1)) return true; }
    return false;
  };
  const hasModel = search(0);
  return { atoms, said, hasModel };
}

// ── 2. guardCoverageVerdict exactness ───────────────────────────────
const GOPS = ['=', '#', '<c', 'c<', '≤c', 'c≤'];
const GMAXC = 5;
const GWIN = BigInt(GMAXC) + 3n;
const holdsG = (g, rv) => { switch (g.op) {
  case '=': return rv === g.c; case '#': return rv !== g.c;
  case '<c': return rv < g.c; case 'c<': return g.c < rv;
  case '≤c': return rv <= g.c; default: return g.c <= rv; } };

function coverageTrial() {
  const nAlts = 2 + pick(3);
  const perAlt = [];
  for (let a = 0; a < nAlts; a++) {
    const nG = pick(3);
    const gs = [];
    for (let k = 0; k < nG; k++) gs.push({ op: GOPS[pick(GOPS.length)], c: BigInt(pick(GMAXC)) });
    perAlt.push(gs);
  }
  const verdict = guardCoverageVerdict(perAlt, 0n);
  let anyUncovered = false, anyOverlap = false;
  for (let rv = 0n; rv < GWIN; rv++) {
    let feas = 0;
    for (const gs of perAlt) if (gs.every((g) => holdsG(g, rv))) feas++;
    if (feas === 0) anyUncovered = true;
    if (feas > 1) anyOverlap = true;
  }
  const ok = !anyUncovered && !anyOverlap;
  let bad = null;
  if (verdict === 'ok' && !ok) bad = 'ok-but-not (missed cell)';
  if (verdict === 'uncovered' && !anyUncovered) bad = 'uncovered-but-covered';
  if (verdict === 'overlap' && !anyOverlap) bad = 'overlap-but-exclusive';
  return { perAlt, verdict, ok, bad };
}

let soundnessViolations = 0, checkedUnsat = 0, missedUnsat = 0;
let coverageMismatches = 0;
for (let t = 0; t < COUNT; t++) {
  const o = orderUnsatTrial();
  if (o.said) { checkedUnsat++; if (o.hasModel) { soundnessViolations++; if (VERBOSE) console.error('FALSE UNSAT:', JSON.stringify(o.atoms)); } }
  else if (!o.hasModel) missedUnsat++;
  const c = coverageTrial();
  if (c.bad) { coverageMismatches++; if (VERBOSE) console.error('COVERAGE MISMATCH (' + c.bad + '):', JSON.stringify(c.perAlt.map((gs) => gs.map((g) => g.op + g.c)))); }
}

console.log(`fuzz-well-moded: ${COUNT} trials, seed ${SEED}`);
console.log(`  orderUnsat: ${checkedUnsat} UNSAT verdicts checked, ${soundnessViolations} false-UNSAT, ${missedUnsat} missed-UNSAT (info; sound-direction incompleteness)`);
console.log(`  guardCoverageVerdict: ${coverageMismatches} disagreements with exhaustive [0,${GWIN}) evaluation`);

if (soundnessViolations > 0 || coverageMismatches > 0) {
  console.error(`FAIL: ${soundnessViolations} orderUnsat soundness violations, ${coverageMismatches} coverage mismatches`);
  process.exit(1);
}
console.log('all properties held.');
