/**
 * E2E tests for noFFI adversarial soundness.
 *
 * Verifies that all persistent goals are provable via clause resolution
 * (no FFI trusted axioms) and produce correct results identical to FFI.
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import fs from 'fs';
import os from 'os';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import { countNodes, getAllLeaves } from '../../lib/engine/tree-utils.js';
import { classifyLeaf } from '../../lib/engine/show.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { guidedTerm } from '../../calculus/ill/lib/guided-term.js';
import { rightFocusTerm } from '../../lib/prover/bridge.js';
import { rTensor } from '../../lib/kernel/ast.js';
describe('noFFI e2e: solc multisig (clause-only resolution)', { timeout: 120000 }, () => {
  let treeNoFFI, treeFFI;

  before(async () => {
    // Run with FFI (benchmark baseline)
    Store.clear();
    const calc = await mde.load(
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    treeFFI = calc.explore(state, {
      maxDepth: 2000,
      dangerouslyUseFFI: true
    });

    // Run without FFI (adversarially sound — default)
    Store.clear();
    const calc2 = await mde.load(
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state2 = mde.normalizeQuery(calc2.queries.get('symex'));
    treeNoFFI = calc2.explore(state2, { maxDepth: 2000 });
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
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    result = calc.exec(state, {
      maxSteps: 2000,
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
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.normalizeQuery(calc.queries.get('symex'));

    // Run with FFI
    calc.exec(state, {
      maxSteps: 10,
      dangerouslyUseFFI: true
    });

    // Run again without flag — should default to noFFI
    Store.clear();
    const calc2 = await mde.load(
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state2 = mde.normalizeQuery(calc2.queries.get('symex'));
    const result = calc2.exec(state2, {
      maxSteps: 10,
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
  implication: 'loli', externalChoice: 'with',
  internalChoice: 'oplus', computation: { tag: 'monad', bodyIdx: 0, gradeIdx: null }
};

describe('noFFI e2e: symbolic explore → guided terms', { timeout: 600000 }, () => {
  let leaves, tree;

  before(async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
    );
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    tree = calc.explore(state, {
      maxDepth: 2000,
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

// ─── Clause-Only Arithmetic: plus and mul ─────────────────────────────────────
//
// Tests that the backward clause definitions for `plus` and `mul` (in bin.ill)
// compute correct results when FFI is disabled. These predicates each have an
// FFI implementation (arithmetic.plus / arithmetic.mul) but MUST also be provable
// via clause resolution (FFI is optimization, clauses are the semantics).
//
// sha3_compute is excluded: its clause (sha3_compute/eval) returns the symbolic
// constructor sha3(Bytes) rather than a concrete keccak256 hash, so FFI and
// clause resolution intentionally produce different output types. Testing sha3
// in isolation requires a concrete memory state which is not expressible as a
// simple #goal predicate with the current harness.

const BIN_ILL = path.join(import.meta.dirname, '../../calculus/ill/programs/bin.ill');

describe('noFFI e2e: clause-only arithmetic (plus, mul)', { timeout: 30000 }, () => {
  let calc;
  let tmpDir;

  before(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'noffi-arith-'));
    const tmpFile = path.join(tmpDir, 'arith_goals.ill');
    // Each #<name> directive stores a ground arithmetic goal as a named query.
    // The backchainer proves these goals via clause resolution when useFFI:false.
    fs.writeFileSync(tmpFile,
      `#import(${BIN_ILL})\n` +
      '#plus_correct plus 0x2 0x3 0x5.\n' +
      '#plus_wrong   plus 0x2 0x3 0x6.\n' +
      '#mul_correct  mul 0x3 0x4 0xc.\n' +
      '#mul_wrong    mul 0x3 0x4 0xd.\n' +
      '#plus_ffi     plus 0x7 0x8 0xf.\n' +
      '#mul_ffi      mul 0x6 0x7 0x2a.\n'
    );
    Store.clear();
    calc = mde.load(tmpFile, { cache: false });
  });

  after(() => {
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  });

  it('plus 2+3=5 succeeds via clause resolution (noFFI)', () => {
    const goal = calc.queries.get('plus_correct');
    const result = calc.prove(goal, { useFFI: false });
    assert.ok(result.success, 'plus 0x2 0x3 0x5 should succeed via clause resolution');
  });

  it('plus 2+3=6 fails via clause resolution (correct rejection)', () => {
    const goal = calc.queries.get('plus_wrong');
    const result = calc.prove(goal, { useFFI: false });
    assert.strictEqual(result.success, false,
      'plus 0x2 0x3 0x6 should fail: clause resolution correctly rejects 2+3 != 6');
  });

  it('mul 3*4=12 succeeds via clause resolution (noFFI)', () => {
    const goal = calc.queries.get('mul_correct');
    const result = calc.prove(goal, { useFFI: false });
    assert.ok(result.success, 'mul 0x3 0x4 0xc should succeed via clause resolution');
  });

  it('mul 3*4=13 fails via clause resolution (correct rejection)', () => {
    const goal = calc.queries.get('mul_wrong');
    const result = calc.prove(goal, { useFFI: false });
    assert.strictEqual(result.success, false,
      'mul 0x3 0x4 0xd should fail: clause resolution correctly rejects 3*4 != 13');
  });

  it('clause-only plus agrees with FFI plus (plus 7+8=15)', () => {
    const goal = calc.queries.get('plus_ffi');
    const clauseResult = calc.prove(goal, { useFFI: false });
    const ffiResult = calc.prove(goal, { useFFI: true });
    assert.strictEqual(clauseResult.success, ffiResult.success,
      'clause and FFI must agree on plus 0x7 0x8 0xf');
  });

  it('clause-only mul agrees with FFI mul (mul 6*7=42)', () => {
    const goal = calc.queries.get('mul_ffi');
    const clauseResult = calc.prove(goal, { useFFI: false });
    const ffiResult = calc.prove(goal, { useFFI: true });
    assert.strictEqual(clauseResult.success, ffiResult.success,
      'clause and FFI must agree on mul 0x6 0x7 0x2a');
  });
});

// ─── Existential-Compile Path: noFFI fallback ────────────────────────────────
//
// The existential-compile fast path (opt/existential-compile.js) calls per-goal
// FFI steps to resolve ∃-quantified consequent variables without going through
// the full provePersistent machinery. When FFI is off, that fast path is bypassed
// (useCompiledSteps=false in _buildMatchOpts) and provePersistent falls through
// to _proveNaive (pure clause resolution) via resolveEx in lnl/existential.js.
//
// This test exercises that fallback path with a minimal program whose single
// forward rule has an existential slot R (present only in the consequent):
//
//   step: go -o { exists R. (!plus 1 2 R * done R) }.
//
// R is not in the antecedent; resolveEx must compute it via !plus clause.
// FFI path:    plus 1 2 R via arithmetic.plus FFI → R = 3
// noFFI path:  plus 1 2 R via plus/s3 / plus/z5 clauses  → R = 3
// Both paths must produce the same 1-node STOP tree.

describe('noFFI e2e: existential-slot resolution via clause (exists R. !plus 1 2 R)', { timeout: 30000 }, () => {
  let treeFFI, treeNoFFI;
  let tmpDir;

  before(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'noffi-ex-'));
    const tmpFile = path.join(tmpDir, 'ex_plus.ill');
    fs.writeFileSync(tmpFile,
      `#import(${BIN_ILL})\n` +
      '\n' +
      'stop: type.\n' +
      'go: type.\n' +
      'done: (n: bin) -> type.\n' +
      '\n' +
      '% step has R as an existential slot: R is in the consequent but NOT the antecedent.\n' +
      '% resolveEx binds R via !plus 1 2 R (clause-only under noFFI), then produces done R * stop.\n' +
      'step: go -o {\n' +
      '  exists R. (!plus 1 2 R * done R * stop)\n' +
      '}.\n' +
      '\n' +
      '#symex\n' +
      '  go\n' +
      '  .\n'
    );

    Store.clear();
    const calcFFI = mde.load(tmpFile, { cache: false });
    const stateFFI = mde.normalizeQuery(calcFFI.queries.get('symex'));
    treeFFI = calcFFI.explore(stateFFI, { maxDepth: 50, dangerouslyUseFFI: true });

    Store.clear();
    const calcNoFFI = mde.load(tmpFile, { cache: false });
    const stateNoFFI = mde.normalizeQuery(calcNoFFI.queries.get('symex'));
    treeNoFFI = calcNoFFI.explore(stateNoFFI, { maxDepth: 50 });
  });

  after(() => {
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  });

  it('noFFI existential explore has same node count as FFI', () => {
    assert.strictEqual(countNodes(treeNoFFI), countNodes(treeFFI),
      `noFFI: ${countNodes(treeNoFFI)} nodes vs FFI: ${countNodes(treeFFI)}`);
  });

  it('noFFI existential explore produces exactly 1 leaf', () => {
    assert.strictEqual(getAllLeaves(treeNoFFI).length, 1,
      'exists R resolved correctly → one execution path (no backtracking)');
  });

  it('noFFI existential leaf is STOP (exists R resolved, no stuck state)', () => {
    const leaves = getAllLeaves(treeNoFFI);
    assert.strictEqual(classifyLeaf(leaves[0].state), 'STOP',
      'exists R. (!plus 1 2 R * done R) must reach STOP via clause resolution');
  });
});
