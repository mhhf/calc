/**
 * Tests for flat rewriting certificates.
 *
 * Validates buildRewriteTrace (forward trace → flat certificate) and
 * checkRewriteTrace (resource accounting verification), plus
 * generateFlatWitness (flat certificate → ZK witness).
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');

const mde = require('../lib/engine');
const Store = require('../lib/kernel/store');
const Seq = require('../lib/kernel/sequent');
const calculus = require('../lib/calculus');
const { buildRewriteTrace, checkRewriteTrace } = require('../lib/prover/rewrite-trace');
const { generateFlatWitness, MAX_CONSUMED, MAX_PRODUCED } = require('../lib/zk/flat-witness');

const FIXTURE_DIR = path.join(__dirname, '..', 'zk', 'sequent-certifier', 'tests', 'fixtures');

function saveFixture(name, data) {
  if (!fs.existsSync(FIXTURE_DIR)) fs.mkdirSync(FIXTURE_DIR, { recursive: true });
  const filepath = path.join(FIXTURE_DIR, `${name}.json`);
  fs.writeFileSync(filepath, JSON.stringify(data));
  return filepath;
}

describe('rewrite-trace: unit tests', () => {
  it('buildRewriteTrace extracts consumed/produced from mock trace', () => {
    Store.clear();
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);

    const mockTrace = [{
      rule: {
        name: 'test_rule',
        hash: 999,
        consequent: { linear: [b] },
      },
      consumed: { [a]: 1 },
      theta: [],
      slots: {},
      persistentEvidence: [],
      loliHash: null,
    }];

    const flat = buildRewriteTrace(mockTrace);
    assert.strictEqual(flat.length, 1);
    assert.deepStrictEqual(flat[0].consumed, [a]);
    assert.deepStrictEqual(flat[0].produced, [b]);
    assert.strictEqual(flat[0].ruleHash, 999);
    assert.strictEqual(flat[0].loliHash, null);
    assert.strictEqual(flat[0].name, 'test_rule');
  });

  it('buildRewriteTrace preserves consumed multiplicity', () => {
    Store.clear();
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);

    // Rule: a * a -o { b } — consumes 2 copies of a
    const mockTrace = [{
      rule: {
        name: 'dup_consume',
        hash: 999,
        consequent: { linear: [b] },
      },
      consumed: { [a]: 2 },
      theta: [],
      slots: {},
      persistentEvidence: [],
      loliHash: null,
    }];

    const flat = buildRewriteTrace(mockTrace);
    assert.deepStrictEqual(flat[0].consumed, [a, a],
      'should expand count=2 to two entries');
  });

  it('checkRewriteTrace verifies resource accounting', () => {
    Store.clear();
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);
    const c = Store.put('atom', ['c']);

    const delta0 = new Map([[a, 1], [b, 1]]);
    const trace = [
      { consumed: [a], produced: [c], name: 'step0' },
    ];
    const result = checkRewriteTrace(delta0, trace);
    assert.ok(result.valid);
    assert.strictEqual(result.remaining.get(b), 1);
    assert.strictEqual(result.remaining.get(c), 1);
    assert.strictEqual(result.remaining.has(a), false);
  });

  it('checkRewriteTrace rejects missing consumed fact', () => {
    Store.clear();
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);

    const delta0 = new Map([[a, 1]]);
    const trace = [
      { consumed: [b], produced: [], name: 'bad_step' },
    ];
    const result = checkRewriteTrace(delta0, trace);
    assert.strictEqual(result.valid, false);
    assert.ok(result.error.includes('bad_step'));
  });

  it('checkRewriteTrace handles multi-step traces', () => {
    Store.clear();
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);
    const c = Store.put('atom', ['c']);

    const delta0 = new Map([[a, 1]]);
    const trace = [
      { consumed: [a], produced: [b], name: 's0' },
      { consumed: [b], produced: [c], name: 's1' },
    ];
    const result = checkRewriteTrace(delta0, trace);
    assert.ok(result.valid);
    assert.strictEqual(result.remaining.get(c), 1);
    assert.strictEqual(result.remaining.size, 1);
  });
});

describe('rewrite-trace: solc forward integration', { timeout: 60000 }, () => {
  let engineCalc, illCalc, state, forwardResult, flatTrace;

  before(async () => {
    Store.clear();
    engineCalc = await mde.load(
      path.join(__dirname, '../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    illCalc = await calculus.loadILL();
    state = mde.decomposeQuery(engineCalc.queries.get('symex'));

    forwardResult = engineCalc.exec(state, {
      maxSteps: 2000,
      trace: true,
      evidence: true,
    });
  });

  it('builds flat trace from 279-step forward execution', () => {
    flatTrace = buildRewriteTrace(forwardResult.trace);
    assert.strictEqual(flatTrace.length, forwardResult.trace.length);
    console.log(`  flat trace: ${flatTrace.length} steps`);

    // Every step should have consumed and produced arrays
    for (let i = 0; i < flatTrace.length; i++) {
      assert.ok(Array.isArray(flatTrace[i].consumed), `step ${i} consumed`);
      assert.ok(Array.isArray(flatTrace[i].produced), `step ${i} produced`);
    }

    // Check arities fit within MAX bounds
    for (const step of flatTrace) {
      assert.ok(step.consumed.length <= MAX_CONSUMED,
        `${step.name}: consumed ${step.consumed.length} > MAX_CONSUMED ${MAX_CONSUMED}`);
      assert.ok(step.produced.length <= MAX_PRODUCED,
        `${step.name}: produced ${step.produced.length} > MAX_PRODUCED ${MAX_PRODUCED}`);
    }

    // Count loli matches vs compiled rules
    const loliCount = flatTrace.filter(s => s.loliHash != null).length;
    const compiledCount = flatTrace.filter(s => s.ruleHash != null).length;
    console.log(`  compiled rules: ${compiledCount}, loli matches: ${loliCount}`);
  });

  it('checkRewriteTrace verifies the full trace', () => {
    // Build initial delta from state
    const delta0 = new Map();
    for (const [h, count] of Object.entries(state.linear || {})) {
      delta0.set(Number(h), Number(count));
    }

    const result = checkRewriteTrace(delta0, flatTrace);
    assert.ok(result.valid, `trace verification failed: ${result.error}`);
    console.log(`  remaining context: ${result.remaining.size} unique facts`);
  });

  it('generates flat ZK witness', () => {
    // Build sequent for witness generation
    const linearCtx = [];
    for (const [h, count] of Object.entries(state.linear || {})) {
      for (let i = 0; i < Number(count); i++) linearCtx.push(Number(h));
    }
    const cartesianCtx = [];
    for (const h of Object.keys(state.persistent || {})) {
      cartesianCtx.push(Number(h));
    }

    // Build succedent from final state
    const hashes = [];
    for (const [h, count] of Object.entries(forwardResult.state.linear || {})) {
      for (let i = 0; i < Number(count); i++) hashes.push(Number(h));
    }
    let succHash;
    if (hashes.length === 0) succHash = Store.put('one', []);
    else if (hashes.length === 1) succHash = hashes[0];
    else {
      succHash = hashes[hashes.length - 1];
      for (let i = hashes.length - 2; i >= 0; i--) {
        succHash = Store.put('tensor', [hashes[i], succHash]);
      }
    }
    const monadSucc = Store.put('monad', [succHash]);
    const sequent = Seq.fromArrays(linearCtx, cartesianCtx, monadSucc);

    const t0 = performance.now();
    const witness = generateFlatWitness(flatTrace, sequent, { calculus: illCalc });
    const dt = performance.now() - t0;

    assert.strictEqual(witness.format, 'flat');
    assert.ok(witness.chips.flat_init.length > 0, 'should have flat_init rows');
    assert.ok(witness.chips.flat_step.length > 0, 'should have flat_step rows');

    // Verify row widths
    for (const row of witness.chips.flat_init) {
      assert.strictEqual(row.length, 2, 'flat_init width');
    }
    // Width 43: 3 header + 2*MAX_CONSUMED + 2*MAX_PRODUCED + spine columns + 1 compiled aux + 3 (ground_ant, ground_cons, subst_id) + 1 canon_cons
    const stepWidth = 3 + 2 * MAX_CONSUMED + 2 * MAX_PRODUCED + 1 + (MAX_CONSUMED - 2) + 1 + (MAX_PRODUCED - 2) + 1 + 1 + 3 + 1;
    for (const row of witness.chips.flat_step) {
      assert.strictEqual(row.length, stepWidth, 'flat_step width');
    }
    for (const row of witness.chips.flat_final) {
      assert.strictEqual(row.length, 2, 'flat_final width');
    }

    // Verify formula_rom is present (Phase 3b: tensor spine verification)
    assert.ok(witness.formula_rom.length > 0, 'should have formula_rom entries');
    for (const row of witness.formula_rom) {
      assert.strictEqual(row.length, 6, 'formula_rom width');
    }

    // Verify canon_cons_rom (Phase 4a-5: extracted from flat_step_prep)
    // May be empty for pure static-rule traces (no loli match steps)
    assert.ok(witness.canon_cons_rom, 'should have canon_cons_rom');
    for (const row of witness.canon_cons_rom) {
      assert.strictEqual(row.length, 4, 'canon_cons_rom row width [cons_hash, canon_cons, is_active, num_lookups]');
    }

    // Verify tags and constants are present
    assert.ok(witness.tags, 'should have tags');
    assert.ok(witness.tags.loli, 'should have loli tag');
    assert.ok(witness.tags.monad, 'should have monad tag');
    assert.ok(witness.tags.tensor, 'should have tensor tag');
    assert.ok(witness.constants, 'should have constants');
    assert.ok(witness.constants.one_hash, 'should have one_hash constant');

    // Verify SubstChip rows (present when loli matches exist)
    if (witness.chips.subst) {
      assert.ok(witness.chips.subst.length > 0, 'subst rows should be non-empty when present');
      for (const row of witness.chips.subst) {
        assert.strictEqual(row.length, 16, 'subst row width');
      }
      console.log(`  subst: ${witness.chips.subst.length} rows`);
    }

    // Verify freevar_rom
    if (witness.freevar_rom.length > 0) {
      for (const row of witness.freevar_rom) {
        assert.strictEqual(row.length, 5, 'freevar_rom width');
      }
      console.log(`  freevar_rom: ${witness.freevar_rom.length} entries`);
    }

    // Summary
    const totalRows = witness.chips.flat_init.length +
      witness.chips.flat_step.length +
      witness.chips.flat_final.length +
      (witness.chips.subst ? witness.chips.subst.length : 0);
    console.log(`  flat_init: ${witness.chips.flat_init.length} rows`);
    console.log(`  flat_step: ${witness.chips.flat_step.length} rows`);
    console.log(`  flat_final: ${witness.chips.flat_final.length} rows`);
    console.log(`  formula_rom: ${witness.formula_rom.length} entries`);
    console.log(`  gamma_rom: ${witness.gamma_rom.length} entries`);
    console.log(`  total rows: ${totalRows} (vs ~6267 tree-based)`);
    console.log(`  witness generation: ${dt.toFixed(0)}ms`);

    // Save fixture for Rust e2e
    const filepath = saveFixture('solc_flat', witness);
    const size = fs.statSync(filepath).size;
    console.log(`  fixture saved: ${(size / 1024).toFixed(0)}KB`);
  });
});
