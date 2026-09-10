/**
 * checkGTC soundness fuzzer (TODO_0009 rung 3, Inc-3).
 *
 * The Global Trace Condition checker (lib/prover/gtc-check.js) is in the TCB, so
 * a soundness hole there is a soundness hole in every cyclic proof. This fuzzer
 * builds random VALID back-edge records (companion = bud, a genuine νR/μL
 * progress step, conserved context) — which must be ACCEPTED — then applies each
 * canonical UNSOUNDNESS mutation and asserts it is REJECTED:
 *   H-progress : delete the progressing step            → reject
 *   H-side     : flip νR→νL or μL→μR (wrong side)        → reject
 *   H-principal: retag the progressing principal to an atom → reject
 *   H-resource : add/drop a linear formula at the bud    → reject
 *   H-succ     : change the bud succedent                → reject
 *
 * Property: every valid record accepts, every mutant rejects (100%). A single
 * valid-reject or mutant-accept fails the run.
 *
 * Usage: node tools/fuzz-gtc.js [--count N] [--seed N] [--verbose]
 * Exits non-zero on any failure.
 */
'use strict';

import Store from '../lib/kernel/store.js';
import Seq from '../lib/kernel/sequent.js';
import { checkGTC } from '../lib/prover/gtc-check.js';
import { loadILL } from '../calculus/ill/index.js';
import { buildForwardParser } from '../calculus/ill/lib/forward-parser.js';

const args = process.argv.slice(2);
const getArg = (f, d) => { const i = args.indexOf(f); return i >= 0 ? Number(args[i + 1]) : d; };
const COUNT = getArg('--count', 300);
let seed = getArg('--seed', 0x9e3779b9) >>> 0;
const VERBOSE = args.includes('--verbose');
const rand = () => { seed = (seed * 1664525 + 1013904223) >>> 0; return seed / 0x100000000; };
const pick = (a) => a[Math.floor(rand() * a.length)];

const ATOMS = ['a', 'b', 'c', 'd'];
const CONN = ['&', '*', '+'];
const FILLER = ['with_l1', 'with_r', 'tensor_l', 'tensor_r', 'oplus_r1', 'id', 'one_r'];

const calc = await loadILL();
const fp = buildForwardParser();
const opts = { roles: calc.roles, contextStructure: calc.contextStructure, canonicalize: calc.canonicalize };

// A random fixed-point formula and which side it progresses on.
function randomFixpoint() {
  const binder = pick(['mu', 'nu']);            // mu → μL (left), nu → νR (right)
  const at = pick(ATOMS), conn = pick(CONN);
  const hash = fp(`${binder} X. (${at} ${conn} X)`);
  return { binder, hash, progRule: binder === 'nu' ? 'nu_r' : 'mu_l', side: binder === 'nu' ? 'R' : 'L' };
}

// Build a VALID back-edge: companion = bud, a progressing step at a random slot
// among fillers, contexts conserved. For nu the fixpoint is the succedent; for
// mu it sits in the linear context (with a fixed succedent).
function validBackEdge() {
  const fx = randomFixpoint();
  const otherLin = rand() < 0.5 ? [pick(ATOMS)] : [];   // arbitrary conserved linear ctx
  let seqObj;
  if (fx.side === 'R') {
    seqObj = Seq.fromArrays(otherLin.map(fp), [], fx.hash);
  } else {
    seqObj = Seq.fromArrays([fx.hash, ...otherLin.map(fp)], [], fp(pick(ATOMS)));
  }
  // rule/principal sequence with the progress step at a random position
  const n = 1 + Math.floor(rand() * 3);
  const ruleNames = [], principals = [];
  const progAt = Math.floor(rand() * n);
  for (let i = 0; i < n; i++) {
    if (i === progAt) { ruleNames.push(fx.progRule); principals.push(fx.hash); }
    else { ruleNames.push(pick(FILLER)); principals.push(rand() < 0.5 ? fp(pick(ATOMS)) : 0); }
  }
  return { bud: seqObj, companion: seqObj, ruleNames, principals, _fx: fx, _progAt: progAt, _otherLin: otherLin };
}

// clone a back-edge shallowly (arrays copied so mutations don't leak)
const clone = (be) => ({ bud: be.bud, companion: be.companion, ruleNames: [...be.ruleNames], principals: [...be.principals] });

const mutators = {
  'H-progress': (be, src) => { be.ruleNames[src._progAt] = 'with_r'; be.principals[src._progAt] = fp(pick(ATOMS)); },
  'H-side': (be, src) => { be.ruleNames[src._progAt] = src._fx.binder === 'nu' ? 'nu_l' : 'mu_r'; },
  'H-principal': (be, src) => { be.principals[src._progAt] = fp(pick(ATOMS)); },
  'H-resource': (be, src) => {
    // add a linear formula at the bud that the companion lacks
    const extra = src._fx.side === 'R'
      ? Seq.fromArrays([...src._otherLin.map(fp), fp('d')], [], src._fx.hash)
      : Seq.fromArrays([src._fx.hash, ...src._otherLin.map(fp), fp('d')], [], src.bud.succedent);
    be.bud = extra;
  },
  'H-succ': (be, src) => {
    const s = src._fx.side === 'R'
      ? Seq.fromArrays(src._otherLin.map(fp), [], fp('nu X. (d & X)'))
      : Seq.fromArrays([src._fx.hash, ...src._otherLin.map(fp)], [], fp('d'));
    // ensure the succ actually differs from companion's
    if (s.succedent !== be.companion.succedent) be.bud = s;
    else be.bud = Seq.fromArrays([], [], fp('c'));
  },
};

let validAccepted = 0, mutantsRejected = 0, mutantsTotal = 0;
const failures = [];

for (let t = 0; t < COUNT; t++) {
  const be = validBackEdge();
  const vr = checkGTC([be], opts);
  if (!vr.valid) {
    failures.push(`trial ${t}: VALID record REJECTED — ${vr.errors.join('; ')}`);
    continue;
  }
  validAccepted++;
  for (const [name, mut] of Object.entries(mutators)) {
    const m = clone(be);
    mut(m, be);
    mutantsTotal++;
    const r = checkGTC([m], opts);
    if (r.valid) failures.push(`trial ${t}: mutant ${name} ACCEPTED (soundness hole!)`);
    else mutantsRejected++;
  }
  if (VERBOSE && t < 5) console.log(`trial ${t}: ${be._fx.binder} ${be._fx.progRule}, ok`);
}

console.log(`fuzz-gtc: ${COUNT} trials, seed 0x${(getArg('--seed', 0x9e3779b9) >>> 0).toString(16)}`);
console.log(`  valid accepted: ${validAccepted}/${COUNT}`);
console.log(`  mutants rejected: ${mutantsRejected}/${mutantsTotal}`);
if (failures.length) {
  console.error(`FAIL: ${failures.length} soundness violations`);
  for (const f of failures.slice(0, 20)) console.error('  ' + f);
  process.exit(1);
}
console.log('all properties held.');
