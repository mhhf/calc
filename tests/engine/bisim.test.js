/**
 * Structural bisimulation of execution trees (TODO_0009 §7, Inc-7).
 * bisimilar:true ⇒ a strong bisimulation relates the two trees (same branching,
 * related terminal states under stateEq); bisimilar:false returns a
 * counterexample. Tested on hand-built explore()-shaped trees.
 */
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { bisimTrees } from '../../lib/engine/bisim.js';

const leaf = (s) => ({ type: 'leaf', state: s });
const branch = (...edges) => ({ type: 'branch', children: edges });
const edge = (rule, child) => ({ rule, child });

describe('bisimTrees — structural bisimulation (Inc-7)', () => {
  it('identical trees are bisimilar', () => {
    const t = branch(edge('a', leaf(1)), edge('b', leaf(2)));
    const u = branch(edge('a', leaf(1)), edge('b', leaf(2)));
    assert.equal(bisimTrees(t, u).bisimilar, true);
  });

  it('branch-order does not matter (edges matched by rule label)', () => {
    const t = branch(edge('a', leaf(1)), edge('b', leaf(2)));
    const u = branch(edge('b', leaf(2)), edge('a', leaf(1)));
    assert.equal(bisimTrees(t, u).bisimilar, true);
  });

  it('a differing leaf state breaks bisimilarity with a counterexample', () => {
    const t = branch(edge('a', leaf(1)));
    const u = branch(edge('a', leaf(999)));
    const r = bisimTrees(t, u);
    assert.equal(r.bisimilar, false);
    assert.deepEqual(r.counterexample.path, ['a']);
    assert.match(r.counterexample.reason, /states not equivalent/);
  });

  it('bisimilar up to rule renaming (ruleMap)', () => {
    // program B uses debit/credit where A uses transfer — map both to 'move'.
    const A = branch(edge('transfer', leaf(1)));
    const B = branch(edge('debit', leaf(1)));
    assert.equal(bisimTrees(A, B).bisimilar, false, 'raw labels differ');
    assert.equal(bisimTrees(A, B, { ruleMap: { transfer: 'move', debit: 'move' } }).bisimilar, true);
  });

  it('different branching degree is not bisimilar', () => {
    const t = branch(edge('a', leaf(1)), edge('b', leaf(2)));
    const u = branch(edge('a', leaf(1)));
    const r = bisimTrees(t, u);
    assert.equal(r.bisimilar, false);
    assert.match(r.counterexample.reason, /branching degree/);
  });

  it('terminal states compared under a caller stateEq (equivalence, not identity)', () => {
    // states {v:1} vs {v:1} are distinct objects — need a stateEq
    const t = branch(edge('a', leaf({ v: 1 })));
    const u = branch(edge('a', leaf({ v: 1 })));
    assert.equal(bisimTrees(t, u).bisimilar, false, 'object identity fails by default');
    assert.equal(bisimTrees(t, u, { stateEq: (x, y) => x.v === y.v }).bisimilar, true);
  });

  it('dead (pruned) edges are ignored on both sides', () => {
    const t = branch(edge('a', leaf(1)), edge('x', { type: 'dead' }));
    const u = branch(edge('a', leaf(1)));
    assert.equal(bisimTrees(t, u).bisimilar, true);
  });

  it('cycle / bound / memo terminals are compared by state', () => {
    const t = branch(edge('a', { type: 'cycle', state: 7 }));
    const u = branch(edge('a', { type: 'cycle', state: 7 }));
    assert.equal(bisimTrees(t, u).bisimilar, true);
    const w = branch(edge('a', { type: 'cycle', state: 8 }));
    assert.equal(bisimTrees(t, w).bisimilar, false);
    // a cycle vs a leaf at the same point is a structural mismatch
    assert.equal(bisimTrees(t, branch(edge('a', leaf(7)))).bisimilar, false);
  });

  it('nested structure is matched recursively; divergence reports its path', () => {
    const t = branch(edge('a', branch(edge('b', leaf(1)))));
    const u = branch(edge('a', branch(edge('b', leaf(2)))));
    const r = bisimTrees(t, u);
    assert.equal(r.bisimilar, false);
    assert.deepEqual(r.counterexample.path, ['a', 'b']);
  });
});
