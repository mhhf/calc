/**
 * ZK symbolic solc: 31-path witness generation + fixture export.
 *
 * Runs exhaustive symbolic exploration of MultisigNoCall.sol,
 * produces one STARK witness fixture per leaf path (31 total),
 * each with custom chip optimization (fact_axiom replaces clause proofs).
 *
 * Fixtures are consumed by:
 *   - Rust test: p6_symbolic_e2e.rs (sequential verification)
 *   - Rust binary: prove_symbolic (parallel proving)
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');

const mde = require('../lib/engine');
const { getAllLeaves } = require('../lib/engine/tree-utils');
const { classifyLeaf } = require('../lib/engine/show');
const Store = require('../lib/kernel/store');
const Seq = require('../lib/kernel/sequent');
const calculus = require('../lib/calculus');
const { guidedTerm } = require('../lib/prover/guided-term');
const { rightFocusTerm } = require('../lib/prover/bridge');
const { generateWitness } = require('../lib/zk/witness');
const { toObject } = require('../lib/engine/fact-set');

const FIXTURE_DIR = path.join(__dirname, '..', 'zk', 'sequent-certifier', 'tests', 'fixtures');

function ensureFixtureDir() {
  if (!fs.existsSync(FIXTURE_DIR)) {
    fs.mkdirSync(FIXTURE_DIR, { recursive: true });
  }
}

function saveFixture(name, data) {
  ensureFixtureDir();
  const filepath = path.join(FIXTURE_DIR, `${name}.json`);
  fs.writeFileSync(filepath, JSON.stringify(data, null, 2));
  return filepath;
}

function buildSuccedentFromState(finalState) {
  const hashes = [];
  for (const [h, count] of Object.entries(finalState.linear || {})) {
    for (let i = 0; i < Number(count); i++) hashes.push(Number(h));
  }
  if (hashes.length === 0) return Store.put('one', []);
  if (hashes.length === 1) return hashes[0];
  let acc = hashes[hashes.length - 1];
  for (let i = hashes.length - 2; i >= 0; i--) {
    acc = Store.put('tensor', [hashes[i], acc]);
  }
  return acc;
}

const ALL_CUSTOM_CHIPS = new Set([
  'arr_get', 'arr_set', 'inc', 'plus', 'mul', 'neq', 'mem_read', 'mem_expand'
]);

describe('ZK symbolic solc: 31-path witness generation', { timeout: 1800000 }, () => {
  let engineCalc, illCalc, initialState, tree, leaves;
  const witnesses = [];

  before(async () => {
    Store.clear();
    engineCalc = await mde.load(
      path.join(__dirname, '../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
    );
    illCalc = await calculus.loadILL();
    initialState = mde.decomposeQuery(engineCalc.queries.get('symex'));
  });

  it('explores with evidence → 31 leaves', () => {
    const t0 = performance.now();
    tree = engineCalc.explore(initialState, {
      maxDepth: 500,
      evidence: true,
      dangerouslyUseFFI: true,
      // FFI is safe here: custom chips discard clause proof subtrees anyway.
      // fact_axiom intercepts ALL copy(loli(_, monad(_))) — the subtree content
      // (clause proofs vs ffi stubs) is never walked.
    });
    const dt = performance.now() - t0;

    leaves = getAllLeaves(tree);
    const classes = {};
    for (const leaf of leaves) {
      const cl = classifyLeaf(leaf.state);
      classes[cl] = (classes[cl] || 0) + 1;
    }

    console.log(`  exploration: ${leaves.length} leaves, ${dt.toFixed(0)}ms`);
    for (const [cl, n] of Object.entries(classes)) {
      console.log(`    ${cl}: ${n}`);
    }
    assert.strictEqual(leaves.length, 31, `Expected 31 leaves, got ${leaves.length}`);
  });

  it('generates 31 witness fixtures with custom chips', () => {
    // Build sequent context from initial state (shared across all paths)
    const linearCtx = [];
    for (const [h, count] of Object.entries(initialState.linear || {})) {
      for (let i = 0; i < Number(count); i++) linearCtx.push(Number(h));
    }
    const cartesianCtx = [];
    for (const h of Object.keys(initialState.persistent || {})) {
      cartesianCtx.push(Number(h));
    }

    let totalSize = 0;
    for (let i = 0; i < leaves.length; i++) {
      const leaf = leaves[i];
      const cl = classifyLeaf(leaf.state);
      assert.ok(leaf.trace, `leaf ${i} must have trace (evidence mode)`);

      // Convert engine FactSet state to plain {linear: {hash→count}, persistent: {hash→true}}
      const plainState = toObject(leaf.state);

      // Build succedent from this leaf's final state
      const succFormula = buildSuccedentFromState(plainState);
      const linear = plainState.linear || {};
      const persistent = plainState.persistent || {};
      const rfResult = rightFocusTerm(linear, persistent, succFormula, illCalc.roles);
      assert.ok(rfResult, `rightFocusTerm should succeed for leaf ${i}`);

      // Build guided proof term
      const innerTerm = guidedTerm(leaf.trace, rfResult.term);
      const gTerm = {
        rule: 'monad_r',
        principal: null,
        subterms: [innerTerm]
      };

      // Build sequent and generate witness
      const monadSucc = Store.put('monad', [succFormula]);
      const sequent = Seq.fromArrays(linearCtx, cartesianCtx, monadSucc);
      const witness = generateWitness(gTerm, sequent, {
        calculus: illCalc,
        customChips: ALL_CUSTOM_CHIPS,
      });

      // Save fixture
      const name = `solc_symbolic_${String(i).padStart(3, '0')}`;
      const filepath = saveFixture(name, witness);
      const size = fs.statSync(filepath).size;
      totalSize += size;

      // Summary
      let totalActive = 0;
      for (const rows of Object.values(witness.chips)) {
        totalActive += rows.filter(r => r[0] === 1).length;
      }
      const faRows = (witness.chips.fact_axiom || []).filter(r => r[0] === 1).length;
      console.log(`  [${String(i).padStart(2)}] ${cl.padEnd(7)} ${leaf.trace.length} steps, ${totalActive} rows, ${faRows} fact_axiom, ${(size/1024).toFixed(0)}KB`);

      witnesses.push(witness);
    }

    console.log(`  --- total: ${witnesses.length} fixtures, ${(totalSize/1024/1024).toFixed(1)}MB`);
    assert.strictEqual(witnesses.length, 31);
  });
});
