/**
 * ZK Benchmark — generates witness fixtures for real-world programs.
 *
 * Runs forward execution with evidence collection, builds a guided
 * proof term (copy → loli_l → tensor_r → monad_l chains), generates
 * ZK witness traces, and saves them as Rust test fixtures.
 *
 * Uses the non-symbolic solc variant (deterministic, 1 STOP leaf,
 * ~280 forward steps) for Phase 3 benchmarking.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');

const mde = require('../lib/engine');
const Store = require('../lib/kernel/store');
const Seq = require('../lib/kernel/sequent');
const calculus = require('../lib/calculus');
const { guidedTerm } = require('../lib/prover/guided-term');
const { rightFocusTerm } = require('../lib/prover/bridge');
const { generateWitness } = require('../lib/zk/witness');

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

/**
 * Build a succedent formula from a forward engine's final state.
 *
 * Constructs a tensor tree of all remaining linear facts, suitable for
 * rightFocusTerm decomposition. The formula is: f1 * f2 * ... * fN
 * (right-associated tensor spine), or `I` (one) if no linear facts remain.
 */
function buildSuccedentFromState(finalState) {
  const hashes = [];
  for (const [h, count] of Object.entries(finalState.linear || {})) {
    for (let i = 0; i < Number(count); i++) hashes.push(Number(h));
  }
  if (hashes.length === 0) return Store.put('one', []);
  if (hashes.length === 1) return hashes[0];
  // Right-associated: f1 * (f2 * (... * fN))
  let acc = hashes[hashes.length - 1];
  for (let i = hashes.length - 2; i >= 0; i--) {
    acc = Store.put('tensor', [hashes[i], acc]);
  }
  return acc;
}

describe('ZK benchmark: solc forward execution', { timeout: 60000 }, () => {
  let engineCalc, illCalc, state, forwardResult, gTerm, witness;

  before(async () => {
    Store.clear();
    engineCalc = await mde.load(
      path.join(__dirname, '../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    illCalc = await calculus.loadILL();
    state = mde.decomposeQuery(engineCalc.queries.get('symex'));
  });

  it('runs forward execution with evidence', () => {
    const t0 = performance.now();
    forwardResult = engineCalc.exec(state, {
      maxSteps: 2000,
      trace: true,
      evidence: true,
      dangerouslyUseFFI: true,  // FFI mode: ~6K rows, 840KB fixture (noFFI: ~5M rows, 440MB)
    });
    const dt = performance.now() - t0;

    console.log(`  forward.run: ${forwardResult.steps} steps, quiescent=${forwardResult.quiescent}, ${dt.toFixed(0)}ms`);
    if (!forwardResult.quiescent) {
      console.log(`  WARNING: hit maxSteps limit`);
    }
    assert.ok(forwardResult.trace.length > 0, 'should have trace entries');
    // Print trace rule names
    console.log(`  trace rules: ${forwardResult.trace.map(t => t.rule?.name || '?').join(', ')}`);
  });

  it('builds guided proof term', () => {
    // Build succedent formula from final state
    const succFormula = buildSuccedentFromState(forwardResult.state);

    // Decompose final state against succedent
    const linear = forwardResult.state.linear || {};
    const persistent = forwardResult.state.persistent || {};
    const rfResult = rightFocusTerm(linear, persistent, succFormula, illCalc.roles);
    assert.ok(rfResult, 'rightFocusTerm should succeed');

    // Build guided term from trace + rf decomposition
    const innerTerm = guidedTerm(forwardResult.trace, rfResult.term);

    // Wrap in monad_r
    gTerm = {
      rule: 'monad_r',
      principal: null,
      subterms: [innerTerm]
    };

    // Count term nodes
    let nodeCount = 0;
    function countNodes(t) {
      if (!t) return;
      nodeCount++;
      if (t.subterms) t.subterms.forEach(countNodes);
    }
    countNodes(gTerm);
    console.log(`  proof term: ${nodeCount} nodes`);
  });

  it('generates ZK witness', () => {
    // Build sequent: initial_linear ⊢ { final_state_formula }
    const linearCtx = [];
    for (const [h, count] of Object.entries(state.linear || {})) {
      for (let i = 0; i < Number(count); i++) linearCtx.push(Number(h));
    }
    const cartesianCtx = [];
    for (const h of Object.keys(state.persistent || {})) {
      cartesianCtx.push(Number(h));
    }

    const succFormula = buildSuccedentFromState(forwardResult.state);
    const monadSucc = Store.put('monad', [succFormula]);
    const sequent = Seq.fromArrays(linearCtx, cartesianCtx, monadSucc);

    const t0 = performance.now();
    witness = generateWitness(gTerm, sequent, { calculus: illCalc });
    const dt = performance.now() - t0;

    // Summary stats
    let totalRows = 0;
    for (const [name, rows] of Object.entries(witness.chips)) {
      if (rows.length > 0) {
        console.log(`  chip ${name}: ${rows.length} rows`);
        totalRows += rows.length;
      }
    }
    console.log(`  formula_rom: ${witness.formula_rom.length} entries`);
    console.log(`  gamma_rom: ${witness.gamma_rom.length} entries`);
    console.log(`  total chip rows: ${totalRows}`);
    console.log(`  witness generation: ${dt.toFixed(0)}ms`);
  });

  it('saves fixture for Rust e2e test', () => {
    assert.ok(witness, 'witness should exist');
    const filepath = saveFixture('solc_forward', witness);
    const size = fs.statSync(filepath).size;
    console.log(`  fixture saved: ${(size / 1024).toFixed(0)}KB`);
  });
});
