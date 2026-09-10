/**
 * Focused-prover path loop detection (TODO_0009 rung 3, Inc-2).
 *
 * Opt-in `opts.detectLoops`: a sequent recurring identically at INVERSION entry
 * on its own DFS path is an infinite (fixpoint) unfolding with no finite proof
 * descending through it → fail fast. This is the μ inductive "fail on loop"
 * half in the focused backward prover (the analogue of rung-1's SLD loopCheck),
 * and it conservatively refuses ν-loops too until Inc-4's cyclic proofs
 * reinstate guarded coinductive back-edges (certified by the TCB GTC checker).
 *
 * Pins: (1) FINITE proofs are unaffected — detectLoops off ≡ on (the focus/blur
 * phase dance revisits the same seq without progress and must NOT self-trigger);
 * (2) a genuine ν-loop fails FAST and stably across maxDepth (no depth-driven
 * blowup / stack overflow); (3) the path Set is scoped — the same sequent on
 * two different DFS branches still proves (clears on backtrack); (4) default-off
 * leaves behaviour identical.
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import Seq from '../../lib/kernel/sequent.js';
import { createProver } from '../../lib/prover/focused.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { loadILL } from '../../calculus/ill/index.js';
import { buildForwardParser } from '../../calculus/ill/lib/forward-parser.js';

describe('focused prover — path loop detection (Inc-2)', () => {
  let calc, fp, prover, base;
  before(async () => {
    calc = await loadILL();
    fp = buildForwardParser();
    const built = buildRuleSpecs(calc);
    prover = createProver(calc);
    base = { rules: built.specs, alternatives: built.alternatives };
  });
  // linear ctx, persistent (cartesian) ctx, succedent
  const prove = (lin, succ, opts = {}, cart = []) =>
    prover.prove(Seq.fromArrays(lin.map(fp), cart.map(fp), fp(succ)), { ...base, ...opts });

  it('finite proofs are unaffected: detectLoops off ≡ on (all succeed)', () => {
    const finite = [
      [['mu X. (a & X)'], 'a'], [[], 'mu X. (I + X)'], [[], 'nu X. (I & I)'],
      [['nu X. (a & I)'], 'a'], [['mu X. (a & (b & X))'], 'b'],
      [['a * b'], 'a * b'], [['a'], 'a'], [[], 'I'], [['a -o b', 'a'], 'b'],
    ];
    for (const [lin, succ] of finite) {
      const off = prove(lin, succ).success;
      const on = prove(lin, succ, { detectLoops: true }).success;
      assert.equal(off, true, `finite proof should succeed: ${JSON.stringify([lin, succ])}`);
      assert.equal(on, off, `detectLoops must not change finite result: ${JSON.stringify([lin, succ])}`);
    }
  });

  it('a genuine ν-loop fails and does so FAST + stably across maxDepth', () => {
    // |- nu X. (a * X): unfolds forever (νR → a * νX → tensor_r → νX …), the
    // `a` branch is unprovable so it fails either way, but detectLoops cuts the
    // recursion instead of descending. Stable at large maxDepth (no blowup).
    const g = () => Seq.fromArrays([], [], fp('nu X. (a * X)'));
    for (const md of [50, 500, 5000]) {
      const on = prover.prove(g(), { ...base, maxDepth: md, detectLoops: true });
      assert.equal(on.success, false, `ν-loop must fail (maxDepth ${md})`);
    }
  });

  it('conservatively refuses a coinductively-TRUE guarded signal (Inc-4 will accept it)', () => {
    // !a ; |- nu X. (a & X) is TRUE coinductively (a always available), but with
    // no cyclic proofs yet the loop is refused — sound under-approximation.
    const r = prove([], 'nu X. (a & X)', { detectLoops: true, maxDepth: 2000 }, ['a']);
    assert.equal(r.success, false);
  });

  it('path-scoped: the same subgoal on two additive branches still proves', () => {
    // !a ; |- a & a : with_r copies the context to BOTH branches, each proving
    // `|- a` from !a. The identical subgoal recurs across SIBLING branches (not
    // one path), so the path Set must clear on backtrack — else the 2nd branch
    // false-loops. Must succeed with detectLoops on.
    const r = prove([], 'a & a', { detectLoops: true }, ['a']);
    assert.equal(r.success, true, 'sibling repetition must not be treated as a loop');
    assert.equal(prove([], 'a & a', {}, ['a']).success, true);
  });
});
