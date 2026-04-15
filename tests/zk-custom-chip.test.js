/**
 * ZK Custom Chip — Phase 6-4: fact_axiom chip replaces clause proof subtrees.
 *
 * Validates that:
 * 1. Custom chip detection correctly identifies clause proof subtrees
 * 2. fact_axiom rows replace full clause proofs (massive row reduction)
 * 3. fact_rom is populated with verified predicate hashes
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

function countNodes(t) {
  if (!t) return 0;
  let n = 1;
  if (t.subterms) for (const s of t.subterms) n += countNodes(s);
  return n;
}

function countRule(t, ruleName) {
  if (!t) return 0;
  let n = (t.rule === ruleName) ? 1 : 0;
  if (t.subterms) for (const s of t.subterms) n += countRule(s, ruleName);
  return n;
}

describe('ZK custom chip: fact_axiom replaces clause proofs', { timeout: 30000 }, () => {
  let calc, illCalc, state, forwardResult, gTerm;
  let witnessBaseline, witnessCustom;

  before(async () => {
    Store.clear();
    calc = await mde.load(
      path.join(__dirname, '../calculus/ill/programs/noffi_tiny.ill')
    );
    illCalc = await calculus.loadILL();
    state = mde.decomposeQuery(calc.queries.get('symex'));
  });

  it('runs forward execution and builds guided term', () => {
    forwardResult = calc.exec(state, {
      maxSteps: 10,
      trace: true,
      evidence: true
    });

    assert.strictEqual(forwardResult.quiescent, true);
    assert.strictEqual(forwardResult.steps, 2);

    const succFormula = buildSuccedentFromState(forwardResult.state);
    const linear = forwardResult.state.linear || {};
    const persistent = forwardResult.state.persistent || {};
    const rfResult = rightFocusTerm(linear, persistent, succFormula, illCalc.roles);
    assert.ok(rfResult, 'rightFocusTerm should succeed');

    const innerTerm = guidedTerm(forwardResult.trace, rfResult.term);
    gTerm = {
      rule: 'monad_r',
      principal: null,
      subterms: [innerTerm]
    };

    // Verify proof term has copy nodes (clause proofs)
    const copyCount = countRule(gTerm, 'copy');
    assert.ok(copyCount > 0, `Expected copy nodes in proof term, got ${copyCount}`);
    console.log(`  proof term: ${countNodes(gTerm)} nodes, ${copyCount} copy nodes`);
  });

  it('generates baseline witness WITHOUT custom chips', () => {
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

    witnessBaseline = generateWitness(gTerm, sequent, { calculus: illCalc });

    // Baseline: should have copy/loli_l/id rows for clause proofs
    const copyRows = (witnessBaseline.chips.copy || []).filter(r => r[0] === 1).length;
    const loliLRows = (witnessBaseline.chips.loli_l || []).filter(r => r[0] === 1).length;
    assert.ok(copyRows > 0, 'baseline must have copy rows');
    assert.ok(loliLRows > 0, 'baseline must have loli_l rows');
    // No fact_axiom in baseline
    const factAxiomRows = (witnessBaseline.chips.fact_axiom || []).length;
    assert.strictEqual(factAxiomRows, 0, 'baseline must have 0 fact_axiom rows');
    // No fact_rom in baseline
    assert.strictEqual(witnessBaseline.fact_rom.length, 0, 'baseline must have empty fact_rom');

    let totalBaseline = 0;
    for (const [name, rows] of Object.entries(witnessBaseline.chips)) {
      const active = rows.filter(r => r[0] === 1).length;
      if (active > 0) totalBaseline += active;
    }
    console.log(`  baseline: ${totalBaseline} active chip rows`);
  });

  it('generates custom chip witness WITH inc optimization', () => {
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

    witnessCustom = generateWitness(gTerm, sequent, {
      calculus: illCalc,
      customChips: new Set(['inc'])
    });

    // Custom: should have fact_axiom rows instead of clause proof rows
    const factAxiomRows = (witnessCustom.chips.fact_axiom || []).filter(r => r[0] === 1).length;
    assert.ok(factAxiomRows > 0, `Expected fact_axiom rows, got ${factAxiomRows}`);
    console.log(`  fact_axiom rows: ${factAxiomRows}`);

    // fact_rom should be populated
    assert.ok(witnessCustom.fact_rom.length > 0, 'fact_rom must be populated');
    console.log(`  fact_rom entries: ${witnessCustom.fact_rom.length}`);

    // Each fact_rom entry: [goal_hash, is_active=1, num_lookups]
    for (const entry of witnessCustom.fact_rom) {
      assert.strictEqual(entry.length, 3, 'fact_rom entry must have 3 columns');
      assert.strictEqual(entry[1], 1, 'fact_rom is_active must be 1');
      assert.ok(entry[2] >= 1, 'fact_rom num_lookups must be >= 1');
    }

    // Row count should be LESS than baseline
    let totalCustom = 0;
    for (const [name, rows] of Object.entries(witnessCustom.chips)) {
      const active = rows.filter(r => r[0] === 1).length;
      if (active > 0) {
        console.log(`  chip ${name}: ${active} active rows`);
        totalCustom += active;
      }
    }

    let totalBaseline = 0;
    for (const rows of Object.values(witnessBaseline.chips)) {
      totalBaseline += rows.filter(r => r[0] === 1).length;
    }

    console.log(`  baseline: ${totalBaseline} → custom: ${totalCustom} (${((1 - totalCustom/totalBaseline) * 100).toFixed(1)}% reduction)`);
    assert.ok(totalCustom < totalBaseline, `Custom (${totalCustom}) must have fewer rows than baseline (${totalBaseline})`);

    // fact_axiom rows: [active, goal, nonce_in, lax, goal_out, nonce_out,
    //   c0..c5, ca0..ca5, p0..p5, pa0..pa5, pred_hash, pred_active]
    for (const row of witnessCustom.chips.fact_axiom) {
      assert.strictEqual(row.length, 32, 'fact_axiom row must have 32 columns');
      assert.strictEqual(row[0], 1, 'fact_axiom active must be 1');
      assert.ok(row[1] > 0, 'fact_axiom goal_hash must be nonzero');
      assert.ok(row[4] > 0, 'fact_axiom goal_out must be nonzero');
      assert.ok(row[5] > 0, 'fact_axiom nonce_out must be nonzero');
      assert.ok(row[30] > 0, 'fact_axiom pred_hash must be nonzero');
      assert.strictEqual(row[31], 1, 'fact_axiom pred_active must be 1');
    }

    // Phase 6-6c/d: pred_rom must have entries for verified predicates
    assert.ok(witnessCustom.pred_rom.length > 0, 'pred_rom must have entries');
    for (const entry of witnessCustom.pred_rom) {
      assert.strictEqual(entry.length, 14, 'pred_rom entry must have 14 columns');
      assert.ok(entry[0] > 0, 'pred_rom pred_hash must be nonzero');
      assert.strictEqual(entry[1], 1, 'pred_rom is_active must be 1');
      assert.ok(entry[2] > 0, 'pred_rom num_lookups must be > 0');
      // At least one selector must be set
      // [3]=is_plus [4]=is_mul [5]=is_inc [6]=is_arr_get [7]=is_arr_set [8]=is_mem_read [9]=is_mem_expand
      const hasSelector = entry[3] + entry[4] + entry[5] + entry[6] + entry[7] + entry[8] + entry[9] > 0;
      assert.ok(hasSelector, 'pred_rom must have a predicate selector');
    }

    // rule_specs should include fact_axiom with fact_lookup=true
    assert.ok(witnessCustom.rule_specs.fact_axiom, 'rule_specs must include fact_axiom');
    assert.strictEqual(witnessCustom.rule_specs.fact_axiom.fact_lookup, true);
    assert.strictEqual(witnessCustom.rule_specs.fact_axiom.oblig_receive, true);
  });

  it('saves fixture for Rust e2e test', () => {
    assert.ok(witnessCustom, 'witness should exist');
    const filepath = saveFixture('custom_chip_inc', witnessCustom);
    const size = fs.statSync(filepath).size;
    console.log(`  fixture saved: ${(size / 1024).toFixed(1)}KB at ${filepath}`);
  });
});
