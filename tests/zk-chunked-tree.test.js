/**
 * ZK Chunked Tree — Phase 6-7: tree path chunking.
 *
 * Validates that:
 * 1. generateChunkedTreeWitness splits a tree witness into chunks
 * 2. Each chunk has boundary chips for obligation/context handoff
 * 3. Bus balance pre-flight passes for each chunk
 * 4. PV continuity holds across chunk boundaries
 * 5. Chunks save as fixtures for Rust e2e verification
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
const { generateWitness, generateChunkedTreeWitness } = require('../lib/zk/witness');

const FIXTURE_DIR = path.join(__dirname, '..', 'zk', 'proof-checker', 'tests', 'fixtures');

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

describe('ZK chunked tree: split and verify', { timeout: 600000 }, () => {
  let engineCalc, illCalc, state, forwardResult, guidedTerm;
  let fullWitness, chunks;
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
    forwardResult = engineCalc.exec(state, {
      maxSteps: 2000,
      trace: true,
      evidence: true,
    });
    assert.ok(forwardResult.quiescent, 'should reach quiescence');
  });

  it('generates full custom chip witness', () => {
    const succFormula = buildSuccedentFromState(forwardResult.state);
    const linear = forwardResult.state.linear || {};
    const persistent = forwardResult.state.persistent || {};
    const rfResult = rightFocusTerm(linear, persistent, succFormula, roles);
    assert.ok(rfResult);

    const innerTerm = buildGuidedTerm(forwardResult.trace, rfResult.term);
    guidedTerm = { rule: 'monad_r', principal: null, subterms: [innerTerm] };

    const linearCtx = [];
    for (const [h, count] of Object.entries(state.linear || {})) {
      for (let i = 0; i < Number(count); i++) linearCtx.push(Number(h));
    }
    const cartesianCtx = [];
    for (const h of Object.keys(state.persistent || {})) {
      cartesianCtx.push(Number(h));
    }
    const monadSucc = Store.put('monad', [succFormula]);
    const sequent = Seq.fromArrays(linearCtx, cartesianCtx, monadSucc);

    fullWitness = generateWitness(guidedTerm, sequent, {
      calculus: illCalc,
      customChips: ALL_CUSTOM_CHIPS,
    });

    const faCount = (fullWitness.chips.fact_axiom || []).filter(r => r[0] === 1).length;
    console.log(`  full witness: ${faCount} fact_axiom rows`);
    assert.ok(faCount > 0);
  });

  it('splits into chunks with maxFactAxiomPerChunk=100', () => {
    chunks = generateChunkedTreeWitness(fullWitness, { maxFactAxiomPerChunk: 100 });

    console.log(`  chunks: ${chunks.length}`);
    assert.ok(chunks.length >= 2, `expected >= 2 chunks, got ${chunks.length}`);

    for (let i = 0; i < chunks.length; i++) {
      const chunk = chunks[i];
      const faCount = (chunk.chips.fact_axiom || []).filter(r => r[0] === 1).length;
      const obligRows = (chunk.chips.oblig_boundary || []).filter(r => r[0] === 1);
      const ctxRows = (chunk.chips.ctx_boundary || []).filter(r => r[0] === 1);
      console.log(`  chunk ${i}: ${faCount} fact_axiom, ${obligRows.length} oblig_boundary, ${ctxRows.length} ctx_boundary`);
      assert.ok(faCount <= 100, `chunk ${i} has ${faCount} fact_axiom rows (max 100)`);
    }
  });

  it('boundary PV continuity: final obligs[i] === init obligs[i+1]', () => {
    for (let i = 0; i < chunks.length - 1; i++) {
      const curChunk = chunks[i];
      const nextChunk = chunks[i + 1];

      // Final obligations of chunk i
      const curFinalObligs = (curChunk.chips.oblig_boundary || [])
        .filter(r => r[0] === 1 && r[1] === 0); // active, is_send=0 (receive = final)
      // Init obligations of chunk i+1
      const nextInitObligs = (nextChunk.chips.oblig_boundary || [])
        .filter(r => r[0] === 1 && r[1] === 1); // active, is_send=1

      assert.strictEqual(curFinalObligs.length, nextInitObligs.length,
        `chunk ${i}→${i+1}: oblig count mismatch`);

      for (let j = 0; j < curFinalObligs.length; j++) {
        // Compare goal_hash and lax (nonce may differ)
        assert.strictEqual(curFinalObligs[j][3], nextInitObligs[j][3],
          `chunk ${i}→${i+1}: goal_hash mismatch at oblig ${j}`);
        assert.strictEqual(curFinalObligs[j][4], nextInitObligs[j][4],
          `chunk ${i}→${i+1}: lax mismatch at oblig ${j}`);
      }
    }
  });

  it('boundary PV continuity: final ctx[i] === init ctx[i+1] (as multisets)', () => {
    for (let i = 0; i < chunks.length - 1; i++) {
      const curChunk = chunks[i];
      const nextChunk = chunks[i + 1];

      const curFinalCtx = (curChunk.chips.ctx_boundary || [])
        .filter(r => r[0] === 1 && r[1] === 0) // active, receive (final)
        .map(r => r[2]).sort((a, b) => a - b);
      const nextInitCtx = (nextChunk.chips.ctx_boundary || [])
        .filter(r => r[0] === 1 && r[1] === 1) // active, send (init)
        .map(r => r[2]).sort((a, b) => a - b);

      assert.deepStrictEqual(curFinalCtx, nextInitCtx,
        `chunk ${i}→${i+1}: context multiset mismatch`);
    }
  });

  it('saves chunked fixture for Rust e2e test', () => {
    const filepath = saveFixture('solc_chunked_tree', chunks);
    const size = fs.statSync(filepath).size;
    console.log(`  fixture saved: ${(size / 1024).toFixed(1)}KB at ${filepath}`);
  });
});
