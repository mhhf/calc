/**
 * E2E tests for noFFI adversarial soundness.
 *
 * Verifies that all persistent goals are provable via clause resolution
 * (no FFI trusted axioms) and produce correct results identical to FFI.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine');
const { explore } = require('../../lib/engine/explore');
const { run } = require('../../lib/engine/forward');
const { countNodes, getAllLeaves } = require('../../lib/engine/tree-utils');
const { classifyLeaf } = require('../../lib/engine/show');
const { toObject } = require('../../lib/engine/fact-set');
const { guidedTerm } = require('../../lib/prover/guided-term');
const { rightFocusTerm } = require('../../lib/prover/bridge');
const { rTensor } = require('../../lib/kernel/ast');

describe('noFFI e2e: solc multisig (clause-only resolution)', { timeout: 120000 }, () => {
  let treeNoFFI, treeFFI;

  before(async () => {
    // Run with FFI (benchmark baseline)
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));
    treeFFI = explore(state, calc.forwardRules, {
      maxDepth: 2000,
      calc: calc._calcContext,
      dangerouslyUseFFI: true
    });

    // Run without FFI (adversarially sound — default)
    Store.clear();
    const calc2 = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state2 = mde.decomposeQuery(calc2.queries.get('symex'));
    treeNoFFI = explore(state2, calc2.forwardRules, {
      maxDepth: 2000,
      calc: calc2._calcContext
      // no dangerouslyUseFFI — noFFI is default
    });
  });

  it('noFFI produces same tree shape as FFI', () => {
    assert.strictEqual(countNodes(treeNoFFI), countNodes(treeFFI),
      `noFFI: ${countNodes(treeNoFFI)} nodes vs FFI: ${countNodes(treeFFI)}`);
  });

  it('noFFI produces same leaf count', () => {
    assert.strictEqual(getAllLeaves(treeNoFFI).length, getAllLeaves(treeFFI).length);
  });

  it('noFFI leaf is STOP (successful termination)', () => {
    const leaves = getAllLeaves(treeNoFFI);
    assert.strictEqual(leaves.length, 1, 'Expected 1 leaf');
    assert.strictEqual(classifyLeaf(leaves[0].state), 'STOP');
  });
});

describe('noFFI e2e: forward.run with evidence', { timeout: 60000 }, () => {
  let result;

  before(async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));
    result = run(state, calc.forwardRules, {
      maxSteps: 2000,
      calc: calc._calcContext,
      trace: true,
      evidence: true
      // no dangerouslyUseFFI — noFFI is default
    });
  });

  it('reaches quiescence', () => {
    assert.strictEqual(result.quiescent, true);
  });

  it('reaches quiescence within budget', () => {
    assert(result.steps > 0 && result.steps < 2000,
      `Expected steps in (0, 2000), got ${result.steps}`);
  });

  it('all persistent evidence is clause-based (no FFI)', () => {
    let ffiCount = 0;
    let clauseCount = 0;
    let stateCount = 0;
    for (const t of result.trace) {
      if (t.persistentEvidence) {
        for (const ev of t.persistentEvidence) {
          if (ev.method === 'ffi') ffiCount++;
          else if (ev.method === 'clause') clauseCount++;
          else if (ev.method === 'state') stateCount++;
        }
      }
    }
    assert.strictEqual(ffiCount, 0, `Expected 0 FFI evidence, got ${ffiCount}`);
    assert(clauseCount > 0, `Expected clause evidence, got ${clauseCount}`);
  });

  it('clause evidence includes proof terms', () => {
    let termsPresent = 0;
    let termsMissing = 0;
    for (const t of result.trace) {
      if (t.persistentEvidence) {
        for (const ev of t.persistentEvidence) {
          if (ev.method === 'clause') {
            if (ev.term) termsPresent++;
            else termsMissing++;
          }
        }
      }
    }
    assert.strictEqual(termsMissing, 0,
      `${termsMissing} clause evidence entries missing proof terms`);
    assert(termsPresent > 0, 'Expected clause evidence with proof terms');
  });
});

describe('noFFI e2e: dangerouslyUseFFI flag resets correctly', () => {
  it('flag resets after forward.run', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    // Run with FFI
    run(state, calc.forwardRules, {
      maxSteps: 10,
      calc: calc._calcContext,
      dangerouslyUseFFI: true
    });

    // Run again without flag — should default to noFFI
    Store.clear();
    const calc2 = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state2 = mde.decomposeQuery(calc2.queries.get('symex'));
    const result = run(state2, calc2.forwardRules, {
      maxSteps: 10,
      calc: calc2._calcContext,
      trace: true,
      evidence: true
    });

    // Should have no FFI evidence (noFFI is default after reset)
    let ffiCount = 0;
    for (const t of result.trace) {
      if (t.persistentEvidence) {
        for (const ev of t.persistentEvidence) {
          if (ev.method === 'ffi') ffiCount++;
        }
      }
    }
    assert.strictEqual(ffiCount, 0, 'Flag should reset — no FFI after dangerouslyUseFFI run');
  });
});

// ─── Symbolic Explore: Full Guided Term Pipeline ────────────────────

const ILL_ROLES = {
  product: 'tensor', unit: 'one', exponential: 'bang',
  implication: 'loli', 'external-choice': 'with',
  'internal-choice': 'oplus', computation: 'monad'
};

describe('noFFI e2e: symbolic explore → guided terms', { timeout: 600000 }, () => {
  let leaves, tree;

  before(async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));
    tree = explore(state, calc.forwardRules, {
      maxDepth: 2000,
      calc: calc._calcContext,
      evidence: true
    });
    leaves = getAllLeaves(tree);
  });

  it('explore produces expected tree shape', () => {
    assert.strictEqual(countNodes(tree), 1987);
    assert.strictEqual(leaves.length, 31);
  });

  it('all leaves have evidence traces', () => {
    for (let i = 0; i < leaves.length; i++) {
      assert.ok(leaves[i].trace, `Leaf ${i} missing trace`);
      assert.ok(leaves[i].trace.length > 0, `Leaf ${i} has empty trace`);
    }
  });

  it('all leaves classify as STOP or REVERT', () => {
    for (let i = 0; i < leaves.length; i++) {
      const type = classifyLeaf(leaves[i].state);
      assert.ok(type === 'STOP' || type === 'REVERT',
        `Leaf ${i}: expected STOP or REVERT, got ${type}`);
    }
  });

  it('rightFocusTerm succeeds for all leaves', () => {
    for (let i = 0; i < leaves.length; i++) {
      const plain = toObject(leaves[i].state);
      const hashes = [];
      for (const [h, count] of Object.entries(plain.linear)) {
        for (let j = 0; j < count; j++) hashes.push(Number(h));
      }
      const succFormula = rTensor(hashes);
      const rf = rightFocusTerm(plain.linear, plain.persistent, succFormula, ILL_ROLES);
      assert.ok(rf, `Leaf ${i}: rightFocusTerm returned null`);
    }
  });

  it('guidedTerm succeeds for all leaves', () => {
    for (let i = 0; i < leaves.length; i++) {
      const plain = toObject(leaves[i].state);
      const hashes = [];
      for (const [h, count] of Object.entries(plain.linear)) {
        for (let j = 0; j < count; j++) hashes.push(Number(h));
      }
      const succFormula = rTensor(hashes);
      const rf = rightFocusTerm(plain.linear, plain.persistent, succFormula, ILL_ROLES);
      const term = guidedTerm(leaves[i].trace, rf.term);
      assert.ok(term, `Leaf ${i}: guidedTerm returned null`);
      assert.ok(term.rule, `Leaf ${i}: guided term has no rule`);
    }
  });
});
