/**
 * ZK Custom Chip — Phase 6-4: solc with custom chips (arr_get, inc, plus, etc.)
 *
 * Validates that:
 * 1. noFFI forward execution produces clause proofs for all persistent goals
 * 2. Custom chips collapse clause proof subtrees to fact_axiom rows
 * 3. Row count drops dramatically (expected: ~1.74M → ~6.5K)
 * 4. The resulting witness passes Rust STARK verification
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');

const mde = require('../lib/engine');
const Store = require('../lib/kernel/store');
const Seq = require('../lib/kernel/sequent');
const calculus = require('../lib/calculus');
const { DEFAULT_ROLES } = require('../lib/engine/compile');
const { buildGuidedTerm } = require('../lib/prover/guided-term');
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

// All EVM predicates that have clause definitions
const ALL_CUSTOM_CHIPS = new Set([
  'arr_get', 'arr_set', 'inc', 'plus', 'mul', 'neq', 'mem_read', 'mem_expand'
]);

describe('ZK custom chip: solc with all predicates', { timeout: 600000 }, () => {
  let engineCalc, illCalc, state, forwardResult, guidedTerm;
  let witnessCustom;
  const roles = DEFAULT_ROLES;

  before(async () => {
    Store.clear();
    engineCalc = await mde.load(
      path.join(__dirname, '../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    illCalc = await calculus.loadILL();
    state = mde.decomposeQuery(engineCalc.queries.get('symex'));
  });

  it('runs noFFI forward execution with evidence', () => {
    const t0 = performance.now();
    forwardResult = engineCalc.exec(state, {
      maxSteps: 2000,
      trace: true,
      evidence: true,
      // NO dangerouslyUseFFI — clause proofs for all persistent goals
    });
    const dt = performance.now() - t0;

    console.log(`  forward.run: ${forwardResult.steps} steps, quiescent=${forwardResult.quiescent}, ${dt.toFixed(0)}ms`);
    assert.ok(forwardResult.quiescent, 'should reach quiescence');
    assert.ok(forwardResult.trace.length > 0, 'should have trace entries');
  });

  it('builds guided proof term from noFFI trace', () => {
    const succFormula = buildSuccedentFromState(forwardResult.state);
    const linear = forwardResult.state.linear || {};
    const persistent = forwardResult.state.persistent || {};
    const rfResult = rightFocusTerm(linear, persistent, succFormula, roles);
    assert.ok(rfResult, 'rightFocusTerm should succeed');

    const t0 = performance.now();
    const innerTerm = buildGuidedTerm(forwardResult.trace, rfResult.term);
    const dt = performance.now() - t0;

    guidedTerm = {
      rule: 'monad_r',
      principal: null,
      subterms: [innerTerm]
    };

    // Count nodes iteratively (tree is ~1.74M deep, recursion overflows)
    let nodeCount = 0;
    const stack = [guidedTerm];
    while (stack.length > 0) {
      const t = stack.pop();
      if (!t) continue;
      nodeCount++;
      if (t.subterms) for (const s of t.subterms) stack.push(s);
    }
    console.log(`  proof term: ${nodeCount} nodes (${dt.toFixed(0)}ms)`);
    console.log(`  expected ~1.74M nodes for noFFI solc`);
  });

  it('generates custom chip witness (all EVM predicates)', () => {
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
    witnessCustom = generateWitness(guidedTerm, sequent, {
      calculus: illCalc,
      customChips: ALL_CUSTOM_CHIPS,
    });
    const dt = performance.now() - t0;

    // Summary stats
    let totalActive = 0;
    for (const [name, rows] of Object.entries(witnessCustom.chips)) {
      const active = rows.filter(r => r[0] === 1).length;
      if (active > 0) {
        console.log(`  chip ${name}: ${active} active rows`);
        totalActive += active;
      }
    }

    const factAxiomActive = (witnessCustom.chips.fact_axiom || []).filter(r => r[0] === 1).length;
    console.log(`  --- summary ---`);
    console.log(`  total active chip rows: ${totalActive}`);
    console.log(`  fact_axiom rows: ${factAxiomActive} (replaced clause proofs)`);
    console.log(`  fact_rom entries: ${witnessCustom.fact_rom.length}`);
    console.log(`  formula_rom: ${witnessCustom.formula_rom.length} entries`);
    console.log(`  gamma_rom: ${witnessCustom.gamma_rom.length} entries`);
    console.log(`  witness generation: ${dt.toFixed(0)}ms`);

    // Custom chips should have produced fact_axiom rows
    assert.ok(factAxiomActive > 0, `Expected fact_axiom rows, got ${factAxiomActive}`);
    assert.ok(witnessCustom.fact_rom.length > 0, 'fact_rom must be populated');

    // Row count should be MUCH less than ~1.74M (noFFI without custom chips)
    // Expected: ~6.5K (similar to FFI mode)
    console.log(`  expected ~6.5K rows (vs ~1.74M without custom chips)`);
    assert.ok(totalActive < 20000, `Expected <20K active rows with custom chips, got ${totalActive}`);
  });

  it('saves fixture for Rust e2e test', () => {
    assert.ok(witnessCustom, 'witness should exist');
    const filepath = saveFixture('solc_custom_chips', witnessCustom);
    const size = fs.statSync(filepath).size;
    console.log(`  fixture saved: ${(size / 1024).toFixed(1)}KB at ${filepath}`);
  });
});
