/**
 * Untimed exec-⊆-explore containment fuzz — Phase 5.5 (generalizing the
 * till fuzz harness that found four engine bugs to the untimed engine,
 * which had no law-based generator coverage).
 *
 * Random small ILL programs (plain / pair / preserved-$ / multi-output
 * arcs over 3-4 atoms, production strictly later in the alphabet than
 * consumption ⇒ terminating by construction) and random initial states.
 * Laws checked per program:
 *
 *   - CONTAINMENT: forward.run's committed-choice outcome is a leaf of
 *     the exhaustive explore tree.
 *   - PERMUTATION: the explore LEAF SET is invariant under rule
 *     declaration order (reachability is order-free; only exec's
 *     committed choice may move — and must land in the same set).
 *
 * One fixed master seed — failures reproduce exactly.
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { toObject } from '../../lib/engine/fact-set.js';
// bagStr is calculus-agnostic (inner-head multiset string) — shared with till
import { bagStr } from './till-helpers.js';

const MASTER_SEED = 0xF0DDE2;
const PROGRAMS = 25;

let rngState = MASTER_SEED | 1;
const rand = () => {
  rngState ^= rngState << 13; rngState ^= rngState >>> 17; rngState ^= rngState << 5;
  return (rngState >>> 0) / 0x100000000;
};
const pick = (xs) => xs[Math.floor(rand() * xs.length)];
const randInt = (n) => Math.floor(rand() * n);

const ATOMS = ['wa', 'wb', 'wc', 'wd'];

function genProgram(idx) {
  const nAtoms = 3 + randInt(2);                 // 3-4 atoms
  const atoms = ATOMS.slice(0, nAtoms);
  const nRules = 2 + randInt(2);                 // 2-3 rules
  const rules = atoms.map(a => `${a}: type.`);   // closed-world: declare tokens
  for (let i = 0; i < nRules; i++) {
    const kind = pick(['plain', 'plain', 'pair', 'preserved', 'multi']);
    // consume from the alphabet prefix, produce STRICTLY later — the
    // production order is a DAG, so every run terminates (untimed rules
    // are all "zero-delay"); preserved $ facts are not productions.
    const ia = randInt(atoms.length - 1);
    const A = atoms[ia];
    const ic = randInt(atoms.length - 1);
    const C = atoms[ic];
    const pool = atoms.slice((kind === 'pair' ? Math.max(ia, ic) : ia) + 1);
    const B = pick(pool);
    const D = pick(pool);
    if (kind === 'plain') rules.push(`r${i}: ${A} -o { ${B} }.`);
    else if (kind === 'pair') rules.push(`r${i}: ${A} * ${C} -o { ${B} }.`);
    else if (kind === 'preserved') rules.push(`r${i}: $${pick(atoms)} * ${A} -o { ${B} }.`);
    else rules.push(`r${i}: ${A} -o { ${B} * ${D} }.`);
  }
  const linear = {};
  let tokens = 0;
  for (const a of atoms) {
    const c = randInt(3);
    if (c > 0) { linear[Store.put('atom', [a])] = c; tokens += c; }
  }
  if (tokens === 0) linear[Store.put('atom', [atoms[0]])] = 1;
  return { idx, rules, state: { linear, persistent: {} } };
}

describe('untimed fuzz — exec ⊆ explore + rule-order invariance', () => {
  let dir, programs;
  before(() => {
    dir = fs.mkdtempSync(path.join(os.tmpdir(), 'fwd-fuzz-'));
    programs = [];
    for (let i = 0; i < PROGRAMS; i++) {
      const p = genProgram(i);
      p.file = path.join(dir, `p${i}.ill`);
      p.fileRev = path.join(dir, `p${i}-rev.ill`);
      fs.writeFileSync(p.file, p.rules.join('\n') + '\n');
      fs.writeFileSync(p.fileRev, p.rules.slice().reverse().join('\n') + '\n');
      programs.push(p);
    }
  });
  after(() => { fs.rmSync(dir, { recursive: true, force: true }); });

  it('committed-choice outcome is an explore leaf; leaf set is order-invariant', () => {
    for (const p of programs) {
      const calc = mde.load(p.file, { cache: false });
      const calcRev = mde.load(p.fileRev, { cache: false });
      const leafSet = (c) => new Set(
        getAllLeaves(c.explore(p.state, { maxDepth: 200 }))
          .map(l => bagStr(toObject(l.state))));
      const leaves = leafSet(calc);
      const leavesRev = leafSet(calcRev);
      assert.deepEqual([...leavesRev].sort(), [...leaves].sort(),
        `leaf set changed under rule permutation:\n${p.rules.join('\n')}`);
      for (const c of [calc, calcRev]) {
        const out = bagStr(c.exec(p.state).state);
        assert.ok(leaves.has(out),
          `exec outcome not an explore leaf:\n${p.rules.join('\n')}\nexec: ${out}\nleaves: ${[...leaves].join(' | ')}`);
      }
    }
  });
});
