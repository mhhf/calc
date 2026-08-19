/**
 * till randomized exec-⊆-explore containment fuzz — TODO_0265 Phase 5
 * (round-13.5 remaining item 1).
 *
 * Generates small random till programs (plain / pair / read / count / woplus
 * / mkloli arcs × zero / positive delays × 2-4 rules over 3-6 atoms) and
 * random stamped initial states, then checks the load-bearing engine laws
 * on each. mkloli rules BIRTH possessed rules (Phase 6c): the containment /
 * replay / split / scheduler laws are thereby proven over DYNAMIC rule
 * sets, not just static ones:
 *
 *   - CONTAINMENT: every settle() outcome (any seed) is a settleExplore leaf
 *     — the test class that would have caught round-13's partial-order
 *     reduction bug (explore committing an order that exec can escape).
 *   - REPLAY: same seed ⇒ identical event trace (D17 stateless PRF).
 *   - SPLIT: settle(settle(S,T/2),T) ≡ settle(S,T) under one seed (E5).
 *   - SCHEDULER: dirty tracking ≡ rescan, trace-identical (P3/D13).
 *
 * Everything derives from one fixed master seed — failures reproduce exactly.
 * Programs whose random rule set forms a zero-delay cycle trip the Zeno
 * guard in explore and are skipped (counted; the suite asserts most run).
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import { loadTill, stampedStr, traceKey } from './till-helpers.js';

const MASTER_SEED = 0xC0FFEE;
const PROGRAMS = 40;
const EXEC_SEEDS = 10;

// ─── deterministic PRNG (xorshift32) ────────────────────────────────
let rngState = MASTER_SEED | 1;
const rand = () => {
  rngState ^= rngState << 13; rngState ^= rngState >>> 17; rngState ^= rngState << 5;
  return (rngState >>> 0) / 0x100000000;
};
const pick = (xs) => xs[Math.floor(rand() * xs.length)];
const randInt = (n) => Math.floor(rand() * n);

// ─── program generator ──────────────────────────────────────────────
// NOTE: single letters i/o/e are binary-literal digits, not atoms — use
// two-letter names so every generated fact is a plain atom.
const ATOMS = ['wa', 'wb', 'wc', 'wd', 'we', 'wf'];
const DELAYS = ['', '', '@1', '@(1/2)', '@2'];   // '' = zero delay (D11 unit)

function genProgram(idx) {
  const nAtoms = 3 + randInt(4);                 // 3-6 atoms
  const atoms = ATOMS.slice(0, nAtoms);
  const nRules = 2 + randInt(3);                 // 2-4 rules
  const lines = [`% till-fuzz generated program #${idx} (master seed ${MASTER_SEED})`];
  for (let i = 0; i < nRules; i++) {
    const kind = pick(['plain', 'plain', 'pair', 'read', 'count', 'woplus', 'mkloli', 'mkloli']);
    const delay = pick(DELAYS);
    // Zero-delay rules produce only atoms STRICTLY LATER in the alphabet
    // than everything they consume: the zero-delay subgraph is a DAG by
    // construction — no Zeno cycles, no D16 lint warnings. Positive-delay
    // rules are unconstrained. Instant-feeding races survive: a zero-delay
    // output can still enable/steal from later-atom consumers at the
    // same instant (the round-13 ample-set cases).
    const zero = delay === '';
    const consumeIdx = () => (zero ? randInt(atoms.length - 1) : randInt(atoms.length));
    const ia = consumeIdx();
    const A = atoms[ia];
    const ic = kind === 'pair' ? consumeIdx() : randInt(atoms.length);
    const C = atoms[ic];
    const prodPool = zero
      ? atoms.slice((kind === 'pair' ? Math.max(ia, ic) : ia) + 1)
      : atoms;
    const B = prodPool.length ? pick(prodPool) : atoms[atoms.length - 1];
    const D = prodPool.length ? pick(prodPool) : atoms[atoms.length - 1];   // woplus alt 2
    if (kind === 'mkloli') {
      // Possessed-rule producer: A -o { (X -o {B}@di) }@d. The born rule is
      // one-shot by linearity; zero-delay chains stay alphabet-increasing
      // ACROSS rule birth (A < X when the outer delay is zero, X < B when
      // the inner one is) — the DAG termination argument extends.
      const innerDelay = pick(['', '@1', '@(1/2)']);
      const poolX = zero ? atoms.slice(ia + 1) : atoms;
      const X = poolX.length ? pick(poolX) : atoms[atoms.length - 1];
      const poolB = innerDelay === ''
        ? atoms.slice(atoms.indexOf(X) + 1) : atoms;
      const B2 = poolB.length ? pick(poolB) : atoms[atoms.length - 1];
      lines.push(`r${i}: ${A} -o { (${X} -o { ${B2} }${innerDelay}) }${delay}.`);
      continue;
    }
    if (kind === 'plain') lines.push(`r${i}: ${A} -o { ${B} }${delay}.`);
    else if (kind === 'pair') lines.push(`r${i}: ${A} * ${C} -o { ${B} }${delay}.`);
    else if (kind === 'read') lines.push(`r${i}: read ${C} * ${A} -o { ${B} }${delay}.`);
    else if (kind === 'count') lines.push(`r${i}: !_2 ${A} -o { ${B} }${delay}.`);
    else lines.push(`r${i}: ${A} -o { woplus 1/4 ${B} ${D} }${delay}.`);
  }
  // random stamped initial state: 0-2 tokens at stamp 0, 0-1 at stamp 1
  const linear = {};
  let tokens = 0;
  for (const a of atoms) {
    const h = Store.put('atom', [a]);
    const c0 = randInt(3);
    if (c0 > 0) { linear[h] = c0; tokens += c0; }
    if (rand() < 0.4) {
      const h1 = Store.put('at', [h, Store.put1('binlit', 1n)]);
      linear[h1] = 1; tokens += 1;
    }
  }
  if (tokens === 0) linear[Store.put('atom', [atoms[0]])] = 1;
  return { text: lines.join('\n') + '\n', state: { linear, persistent: {} }, horizon: pick(['1', '2', '3']) };
}

describe('till fuzz — exec ⊆ explore containment + determinism laws', () => {
  let dir, programs;
  before(() => {
    dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-fuzz-'));
    programs = [];
    for (let i = 0; i < PROGRAMS; i++) {
      const p = genProgram(i);
      p.file = path.join(dir, `prog-${i}.ill`);
      fs.writeFileSync(p.file, p.text);
      programs.push(p);
    }
  });
  after(() => { fs.rmSync(dir, { recursive: true, force: true }); });

  it('every exec outcome is an explore leaf; replay/split/scheduler agree', () => {
    let ran = 0, skipped = 0;
    for (const p of programs) {
      const calc = loadTill(p.file);
      let full;
      try {
        // maxSteps bounds TOTAL fired events across the tree; random
        // programs can be legitimately exponential (woplus regeneration
        // chains — the tree IS the distribution), so keep the budget small
        // and skip-count what exceeds it.
        full = calc.settleExplore(p.state, p.horizon, { maxSteps: 2000 });
      } catch (e) {
        if (/Zeno|maxSteps|stack cap/.test(e.message)) { skipped++; continue; }   // cycle or blowup
        throw new Error(`explore failed on:\n${p.text}\n${e.message}`);
      }
      ran++;
      const leafBags = new Set(full.leaves.map(l => stampedStr(l.state)));
      for (let seed = 0; seed < EXEC_SEEDS; seed++) {
        const res = calc.settle(p.state, p.horizon, { seed });
        const outcome = stampedStr(res.state);
        assert.ok(leafBags.has(outcome),
          `containment violated (seed ${seed}, horizon ${p.horizon}):\n${p.text}\n` +
          `exec: ${outcome}\nleaves:\n  ${[...leafBags].join('\n  ')}`);
      }
      // replay: same seed ⇒ identical trace
      const t1 = calc.settle(p.state, p.horizon, { seed: 3 });
      const t2 = calc.settle(p.state, p.horizon, { seed: 3 });
      assert.equal(traceKey(t2.events), traceKey(t1.events), `replay diverged:\n${p.text}`);
      // horizon-split metamorphic (E5) under a fixed seed
      const mids = { 1: '1/2', 2: '1', 3: '3/2' };
      const mid = calc.settle(p.state, mids[p.horizon], { seed: 3 }).state;
      const resumed = calc.settle(mid, p.horizon, { seed: 3 }).state;
      assert.equal(stampedStr(resumed), stampedStr(t1.state), `split diverged:\n${p.text}`);
      // dirty scheduler ≡ rescan
      const dirty = calc.settle(p.state, p.horizon, { seed: 3, scheduler: 'dirty' });
      assert.equal(traceKey(dirty.events), traceKey(t1.events), `scheduler diverged:\n${p.text}`);
    }
    assert.ok(ran >= PROGRAMS / 2, `too many Zeno skips: ${skipped}/${PROGRAMS}`);
  });
});
