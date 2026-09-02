/**
 * explore() caller-state integrity + determinism fuzzer (TODO_0272 M7).
 *
 * explore() copies the caller's state into an internal FactSet and drives a DFS
 * that mutates it in place, restoring via Arena undo on backtrack. The existing
 * suites check leaf containment; nothing checked (a) that the caller's state is
 * untouched, or (b) that a full explore is deterministic — the observable
 * proxy for clean arena undo (residue on backtrack would corrupt sibling
 * branches and surface as run-to-run drift). This fuzzes random branching
 * states and asserts both.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import mde from '../../calculus/ill/index.js';
import { explore, stateHashStr } from '../../lib/engine/explore.js';
import { countNodes, countLeaves, maxDepth, toDot } from '../../lib/engine/tree-utils.js';
import Store from '../../lib/kernel/store.js';

function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// A full structural + per-leaf-state fingerprint of an explore tree.
const treeFingerprint = (tree) =>
  `${countNodes(tree)}|${countLeaves(tree)}|${maxDepth(tree)}||${toDot(tree)}`;

describe('TODO_0272 M7 — explore integrity + determinism fuzz', { timeout: 20000 }, () => {
  let calc, atoms;
  before(async () => {
    Store.clear();
    calc = await mde.load([path.join(import.meta.dirname, 'fixtures/nondet.ill')]);
    // Content-addressed hashes for the branching atoms.
    atoms = {
      start: await mde.parseExpr('start'),
      left: await mde.parseExpr('left'),
      right: await mde.parseExpr('right'),
    };
  });

  it('caller state is untouched + explore is deterministic (400 random states)', () => {
    const r = rng(0x30303);
    let branched = 0;
    for (let i = 0; i < 400; i++) {
      // Random branching state: 1-4 starts + a few loose left/right.
      const linear = {};
      linear[atoms.start] = 1 + Math.floor(r() * 4);
      if (r() < 0.5) linear[atoms.left] = 1 + Math.floor(r() * 2);
      if (r() < 0.5) linear[atoms.right] = 1 + Math.floor(r() * 2);
      const state = { linear, persistent: {} };

      const before = stateHashStr(state);
      const opts = { maxDepth: 3 + Math.floor(r() * 6), calc: calc._calcContext };

      const tree1 = explore(state, calc.forwardRules, opts);
      // (a) caller-state integrity — explore must not mutate the input.
      assert.strictEqual(stateHashStr(state), before,
        `explore mutated the caller state for case #${i}`);

      // (b) determinism — a second run on the same input is identical.
      const tree2 = explore(state, calc.forwardRules, opts);
      assert.strictEqual(treeFingerprint(tree1), treeFingerprint(tree2),
        `explore non-deterministic for case #${i} (arena-undo residue?)`);

      if (tree1.type === 'branch') branched++;
    }
    assert.ok(branched > 50, `too few branching cases (${branched}) — state generator skew`);
  });
});
