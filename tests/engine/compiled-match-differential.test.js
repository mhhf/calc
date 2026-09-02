/**
 * Compiled-vs-interpreted match differential fuzzer (TODO_0272 M7).
 *
 * compilePM/execPM (compiled pattern-match instructions) and matchIndexed
 * (the interpreted tree-walking matcher) must agree on EVERY pattern/subject
 * pair: same success/failure, and identical slot bindings on success. The
 * existing compiled-matcher tests are hand-crafted; this fuzzes random pattern
 * trees against (a) subjects built by instantiating the pattern (forced
 * matches — checks binding fidelity) and (b) independent ground subjects
 * (mostly mismatches — checks rejection agreement).
 *
 * No binlit/i-o-e terms: cross-tag equational rewriting is fuzzed by fuzz-ffi;
 * here we isolate the structural matcher so a divergence is a real matcher bug.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import calculus from '../../lib/calculus/index.js';
import Store from '../../lib/kernel/store.js';
import { compilePM, execPM } from '../../lib/engine/compile.js';
import { matchIndexed, undoSave, undoRestore, undoDiscard } from '../../lib/kernel/unify.js';
import { apply } from '../../lib/kernel/substitute.js';
import { collectMetavars } from '../../lib/engine/pattern-utils.js';
import { loadILL } from '../../calculus/ill/index.js';

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
const pick = (r, arr) => arr[Math.floor(r() * arr.length)];

describe('TODO_0272 M7 — compiled vs interpreted match differential', () => {
  let AST, ground, metavars;
  before(async () => {
    const ill = await loadILL();
    AST = ill.AST;
    Store.registerTag('p1'); Store.registerTag('p2'); Store.registerTag('s');
    ground = ['a', 'b', 'c', 'd', 'stop'].map(n => AST.atom(n));
    metavars = ['m0', 'm1', 'm2', 'm3'].map(n => AST.metavar(n));
  });

  const groundTerm = (r, d) => d <= 0 ? pick(r, ground) : (() => {
    const k = r();
    if (k < 0.4) return pick(r, ground);
    if (k < 0.55) return Store.put('s', [groundTerm(r, d - 1)]);
    if (k < 0.75) return AST.tensor(groundTerm(r, d - 1), groundTerm(r, d - 1));
    if (k < 0.9) return Store.put('p2', [groundTerm(r, d - 1), groundTerm(r, d - 1)]);
    return Store.put('p1', [groundTerm(r, d - 1)]);
  })();

  // A pattern tree — same shape space as groundTerm but leaves may be metavars.
  const patTerm = (r, d) => d <= 0 ? (r() < 0.55 ? pick(r, metavars) : pick(r, ground)) : (() => {
    const k = r();
    if (k < 0.35) return r() < 0.6 ? pick(r, metavars) : pick(r, ground);
    if (k < 0.5) return Store.put('s', [patTerm(r, d - 1)]);
    if (k < 0.7) return AST.tensor(patTerm(r, d - 1), patTerm(r, d - 1));
    if (k < 0.88) return Store.put('p2', [patTerm(r, d - 1), patTerm(r, d - 1)]);
    return Store.put('p1', [patTerm(r, d - 1)]);
  })();

  function slotsOf(pattern) {
    const set = new Set();
    collectMetavars(pattern, set);
    const slots = {};
    let i = 0;
    for (const mv of set) slots[mv] = i++;
    return { slots, count: i };
  }

  // Interpreted match with proper undo-stack hygiene.
  function interp(pattern, subject, theta, slots) {
    const save = undoSave();
    const ok = matchIndexed(pattern, subject, theta, slots);
    if (ok) undoDiscard(save); else undoRestore(save);
    return ok;
  }

  function runDifferential(seed, makeSubject) {
    const r = rng(seed);
    let matched = 0, missed = 0;
    for (let i = 0; i < 4000; i++) {
      const pattern = patTerm(r, 1 + Math.floor(r() * 3));
      const { slots, count } = slotsOf(pattern);
      if (count > 32) continue;
      const subject = makeSubject(r, pattern, slots);

      const theta1 = new Array(count);
      const instr = compilePM(pattern, slots);
      const okC = !!execPM(instr, subject, theta1);

      const theta2 = new Array(count);
      const okI = interp(pattern, subject, theta2, slots);

      assert.strictEqual(okC, okI,
        `match disagreement #${i}: compiled=${okC} interpreted=${okI}`);
      if (okC) {
        matched++;
        for (let s = 0; s < count; s++) {
          assert.strictEqual(theta1[s], theta2[s],
            `binding slot ${s} disagreement #${i}: compiled=${theta1[s]} interpreted=${theta2[s]}`);
        }
      } else missed++;
    }
    return { matched, missed };
  }

  it('agrees on instantiated subjects (forced matches, 4000 pairs)', () => {
    // Build the subject by substituting each pattern metavar with a ground term.
    const { matched, missed } = runDifferential(0x9A9A, (r, pattern, slots) => {
      const theta = Object.keys(slots).map(mv => [Number(mv), groundTerm(r, 1)]);
      return apply(pattern, theta);
    });
    assert.ok(matched > 3000, `expected mostly matches, got ${matched} (missed ${missed})`);
  });

  it('agrees on independent ground subjects (mostly mismatches, 4000 pairs)', () => {
    const { matched, missed } = runDifferential(0x7B7B, (r) => groundTerm(r, 1 + Math.floor(r() * 3)));
    assert.ok(missed > 500, `expected many mismatches, got ${missed} (matched ${matched})`);
  });
});
