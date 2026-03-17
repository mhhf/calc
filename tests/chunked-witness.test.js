/**
 * Tests for chunked flat witness generation (Phase 4a-3).
 *
 * Validates that generateChunkedFlatWitness correctly splits long traces
 * into multiple chunk witnesses with proper context continuity.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');

const Store = require('../lib/kernel/store');
const Seq = require('../lib/kernel/sequent');
const { generateFlatWitness, generateChunkedFlatWitness } = require('../lib/zk/flat-witness');

// ---------------------------------------------------------------------------
// Unit tests with mock traces
// ---------------------------------------------------------------------------

describe('chunked flat witness: unit', () => {
  let a, b, c, d, e;

  before(() => {
    Store.clear();
    a = Store.put('atom', ['a']);
    b = Store.put('atom', ['b']);
    c = Store.put('atom', ['c']);
    d = Store.put('atom', ['d']);
    e = Store.put('atom', ['e']);
  });

  /** Build a mock compiled-rule step: consumes [src], produces [dst]. */
  function mockStep(src, dst, name = 'test_rule') {
    return {
      consumed: [src],
      produced: [dst],
      ruleHash: 999,
      loliHash: null,
      name,
    };
  }

  function makeSequent(linear) {
    const monadSucc = Store.put('monad', [Store.put('one', [])]);
    return Seq.fromArrays(linear, [], monadSucc);
  }

  it('returns single-element array when all steps fit in one chunk', () => {
    const trace = [mockStep(a, b)];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 100,
    });
    assert.strictEqual(chunks.length, 1);
    assert.strictEqual(chunks[0].format, 'flat');
    assert.ok(chunks[0].chips.flat_step.length === 1);
  });

  it('single chunk matches generateFlatWitness output', () => {
    const trace = [mockStep(a, b)];
    const seq = makeSequent([a]);
    const single = generateFlatWitness(trace, seq, {});
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 100,
    });
    assert.strictEqual(chunks.length, 1);
    assert.deepStrictEqual(chunks[0].chips.flat_init, single.chips.flat_init);
    assert.deepStrictEqual(chunks[0].chips.flat_step, single.chips.flat_step);
    assert.deepStrictEqual(chunks[0].chips.flat_final, single.chips.flat_final);
    assert.deepStrictEqual(chunks[0].canon_cons_rom, single.canon_cons_rom);
  });

  it('splits 3-step trace into 2 chunks at maxRowsPerChunk=2', () => {
    // a → b → c → d (3 steps, chunk at 2)
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
      mockStep(c, d),
    ];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 2,
    });
    assert.strictEqual(chunks.length, 2);
    assert.strictEqual(chunks[0].chips.flat_step.length, 2);
    assert.strictEqual(chunks[1].chips.flat_step.length, 1);
  });

  it('chunk context continuity: final[i] hashes == init[i+1] hashes', () => {
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
      mockStep(c, d),
    ];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 2,
    });

    // Extract hash sets from init/final rows
    const finalHashes0 = chunks[0].chips.flat_final.map(r => r[1]).sort();
    const initHashes1 = chunks[1].chips.flat_init.map(r => r[1]).sort();
    assert.deepStrictEqual(finalHashes0, initHashes1,
      'chunk 0 final context should equal chunk 1 init context');
  });

  it('first chunk init matches original sequent context', () => {
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
    ];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 1,
    });
    assert.strictEqual(chunks.length, 2);
    // First chunk init should be [a]
    assert.deepStrictEqual(
      chunks[0].chips.flat_init.map(r => r[1]),
      [a],
    );
  });

  it('last chunk final matches overall final context', () => {
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
    ];
    const seq = makeSequent([a]);
    const chunked = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 1,
    });
    const single = generateFlatWitness(trace, seq, {});

    const chunkedFinal = chunked[chunked.length - 1].chips.flat_final.map(r => r[1]).sort();
    const singleFinal = single.chips.flat_final.map(r => r[1]).sort();
    assert.deepStrictEqual(chunkedFinal, singleFinal,
      'last chunk final should match unchunked final');
  });

  it('preserves untouched context across chunks', () => {
    // Init: [a, e]. Steps: a→b, b→c. e is never consumed.
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
    ];
    const seq = makeSequent([a, e]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 1,
    });
    assert.strictEqual(chunks.length, 2);

    // Chunk 0 final should have [b, e] (a consumed, b produced, e untouched)
    const final0 = chunks[0].chips.flat_final.map(r => r[1]).sort();
    assert.deepStrictEqual(final0, [b, e].sort());

    // Chunk 1 init should have [b, e]
    const init1 = chunks[1].chips.flat_init.map(r => r[1]).sort();
    assert.deepStrictEqual(init1, [b, e].sort());

    // Chunk 1 final should have [c, e]
    const final1 = chunks[1].chips.flat_final.map(r => r[1]).sort();
    assert.deepStrictEqual(final1, [c, e].sort());
  });

  it('all chunks have identical formula ROM preprocessed entries', () => {
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
      mockStep(c, d),
    ];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 2,
    });
    assert.ok(chunks[0].formula_rom.length > 0, 'should have formula ROM entries');
    // Preprocessed part (without num_lookups) must be identical across chunks
    const prep0 = chunks[0].formula_rom.map(r => JSON.stringify(r.slice(0, 5)));
    const prep1 = chunks[1].formula_rom.map(r => JSON.stringify(r.slice(0, 5)));
    assert.deepStrictEqual(prep0, prep1,
      'formula ROM preprocessed entries should be identical across chunks');
    // Union should be >= any individual chunk's original entry count
    assert.strictEqual(chunks[0].formula_rom.length, chunks[1].formula_rom.length);
  });

  it('all chunks have identical gamma ROM preprocessed entries', () => {
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
      mockStep(c, d),
    ];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 2,
    });
    assert.ok(chunks[0].gamma_rom.length > 0, 'should have gamma ROM entries');
    const prep0 = chunks[0].gamma_rom.map(r => JSON.stringify(r.slice(0, 2)));
    const prep1 = chunks[1].gamma_rom.map(r => JSON.stringify(r.slice(0, 2)));
    assert.deepStrictEqual(prep0, prep1,
      'gamma ROM preprocessed entries should be identical across chunks');
  });

  it('union ROM has lookups=0 for entries not used by a chunk', () => {
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
      mockStep(c, d),
    ];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 2,
    });
    // Some formula ROM entries should have lookups=0 in at least one chunk
    // (since chunk 0 uses formulas that chunk 1 doesn't, and vice versa)
    const hasZeroLookups0 = chunks[0].formula_rom.some(r => r[5] === 0);
    const hasZeroLookups1 = chunks[1].formula_rom.some(r => r[5] === 0);
    assert.ok(hasZeroLookups0 || hasZeroLookups1,
      'at least one chunk should have formula ROM entries with 0 lookups');
  });

  it('all chunks have identical canon_cons_rom preprocessed entries', () => {
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
      mockStep(c, d),
    ];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 2,
    });
    // For compiled steps, canon_cons_rom is empty (no loli matches)
    // but the arrays should still be identical across chunks
    const prep0 = chunks[0].canon_cons_rom.map(r => JSON.stringify(r.slice(0, 3)));
    const prep1 = chunks[1].canon_cons_rom.map(r => JSON.stringify(r.slice(0, 3)));
    assert.deepStrictEqual(prep0, prep1,
      'canon_cons_rom preprocessed entries should be identical across chunks');
  });

  it('step rows include canon_cons column (width 43)', () => {
    const trace = [mockStep(a, b)];
    const seq = makeSequent([a]);
    const w = generateFlatWitness(trace, seq, {});
    // Each step row should be width 43 (42 + canon_cons)
    assert.strictEqual(w.chips.flat_step[0].length, 43,
      'step row should have 43 columns');
    // For compiled steps, canon_cons (last column) should be 0
    assert.strictEqual(w.chips.flat_step[0][42], 0,
      'compiled step canon_cons should be 0');
  });

  it('all chunks have same max_ctx_size (PV normalization)', () => {
    // Context grows: a→b→c→d across 2 chunks. Init/final sizes differ
    // but max_ctx_size must be uniform for constant VK.
    const trace = [
      mockStep(a, b),
      mockStep(b, c),
      mockStep(c, d),
    ];
    const seq = makeSequent([a, e]); // init has 2 facts
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 2,
    });
    assert.strictEqual(chunks.length, 2);

    // All chunks must have the same max_ctx_size
    const sizes = chunks.map(c => c.max_ctx_size);
    assert.ok(sizes.every(s => s === sizes[0]),
      `all chunks should have same max_ctx_size, got ${sizes}`);

    // max_ctx_size must be >= every chunk's init and final row count
    for (let i = 0; i < chunks.length; i++) {
      assert.ok(chunks[i].max_ctx_size >= chunks[i].chips.flat_init.length,
        `chunk ${i}: max_ctx_size should >= init row count`);
      assert.ok(chunks[i].max_ctx_size >= chunks[i].chips.flat_final.length,
        `chunk ${i}: max_ctx_size should >= final row count`);
    }
  });

  it('single chunk has max_ctx_size field', () => {
    const trace = [mockStep(a, b)];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 100,
    });
    assert.strictEqual(chunks.length, 1);
    assert.ok(chunks[0].max_ctx_size != null, 'single chunk should have max_ctx_size');
    assert.strictEqual(chunks[0].max_ctx_size,
      Math.max(chunks[0].chips.flat_init.length, chunks[0].chips.flat_final.length));
  });

  it('each chunk has tags and constants', () => {
    const trace = [mockStep(a, b), mockStep(b, c)];
    const seq = makeSequent([a]);
    const chunks = generateChunkedFlatWitness(trace, seq, {
      maxRowsPerChunk: 1,
    });
    for (const chunk of chunks) {
      assert.ok(chunk.tags, 'chunk should have tags');
      assert.ok(chunk.constants, 'chunk should have constants');
      assert.ok(chunk.constants.one_hash, 'chunk should have one_hash');
    }
  });
});

// ---------------------------------------------------------------------------
// Integration: chunked solc witness
// ---------------------------------------------------------------------------

describe('chunked flat witness: solc integration', { timeout: 60000 }, () => {
  let flatTrace, sequent, illCalc;

  before(async () => {
    Store.clear();
    const mde = require('../lib/engine');
    const calculus = require('../lib/calculus');
    const { buildRewriteTrace } = require('../lib/prover/rewrite-trace');

    const engineCalc = await mde.load(
      path.join(__dirname, '../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    illCalc = await calculus.loadILL();
    const state = mde.decomposeQuery(engineCalc.queries.get('symex'));

    const forwardResult = engineCalc.exec(state, {
      maxSteps: 2000, trace: true, evidence: true,
    });
    flatTrace = buildRewriteTrace(forwardResult.trace);

    // Build sequent
    const linearCtx = [];
    for (const [h, count] of Object.entries(state.linear || {})) {
      for (let i = 0; i < Number(count); i++) linearCtx.push(Number(h));
    }
    const cartesianCtx = [];
    for (const h of Object.keys(state.persistent || {})) {
      cartesianCtx.push(Number(h));
    }
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
    sequent = Seq.fromArrays(linearCtx, cartesianCtx, monadSucc);
  });

  it('chunks 279-step solc trace with maxRowsPerChunk=100', () => {
    const chunks = generateChunkedFlatWitness(flatTrace, sequent, {
      calculus: illCalc,
      maxRowsPerChunk: 100,
    });

    assert.ok(chunks.length >= 3, `expected >= 3 chunks, got ${chunks.length}`);
    console.log(`  ${flatTrace.length} steps → ${chunks.length} chunks`);

    // Total step count across chunks should equal original
    const totalSteps = chunks.reduce((s, c) => s + c.chips.flat_step.length, 0);
    assert.strictEqual(totalSteps, flatTrace.length,
      'total steps across chunks should equal original trace length');

    // Context continuity across all chunk boundaries
    for (let i = 0; i < chunks.length - 1; i++) {
      const finalHashes = chunks[i].chips.flat_final.map(r => r[1]).sort();
      const initHashes = chunks[i + 1].chips.flat_init.map(r => r[1]).sort();
      assert.deepStrictEqual(finalHashes, initHashes,
        `chunk ${i} final should equal chunk ${i + 1} init`);
    }

    // Each chunk should have valid structure
    for (let i = 0; i < chunks.length; i++) {
      const chunk = chunks[i];
      assert.strictEqual(chunk.format, 'flat', `chunk ${i} format`);
      assert.ok(chunk.chips.flat_init.length > 0, `chunk ${i} should have init rows`);
      assert.ok(chunk.chips.flat_step.length > 0, `chunk ${i} should have step rows`);
      assert.ok(chunk.chips.flat_step.length <= 100, `chunk ${i} should have <= 100 steps`);
      assert.ok(chunk.formula_rom.length > 0, `chunk ${i} should have formula ROM`);
      assert.ok(chunk.gamma_rom.length > 0, `chunk ${i} should have gamma ROM`);
      assert.ok(chunk.canon_cons_rom, `chunk ${i} should have canon_cons_rom`);

      console.log(`  chunk ${i}: ${chunk.chips.flat_step.length} steps, ` +
        `${chunk.chips.flat_init.length} init, ${chunk.chips.flat_final.length} final, ` +
        `${chunk.formula_rom.length} formula, ${chunk.gamma_rom.length} gamma, ` +
        `${chunk.canon_cons_rom.length} canon_cons` +
        (chunk.chips.subst ? `, ${chunk.chips.subst.length} subst` : ''));
    }
  });

  it('first chunk init matches unchunked init', () => {
    const single = generateFlatWitness(flatTrace, sequent, { calculus: illCalc });
    const chunks = generateChunkedFlatWitness(flatTrace, sequent, {
      calculus: illCalc,
      maxRowsPerChunk: 100,
    });

    assert.deepStrictEqual(
      chunks[0].chips.flat_init.map(r => r[1]).sort(),
      single.chips.flat_init.map(r => r[1]).sort(),
      'first chunk init should match unchunked init',
    );
  });

  it('last chunk final matches unchunked final', () => {
    const single = generateFlatWitness(flatTrace, sequent, { calculus: illCalc });
    const chunks = generateChunkedFlatWitness(flatTrace, sequent, {
      calculus: illCalc,
      maxRowsPerChunk: 100,
    });

    const lastFinal = chunks[chunks.length - 1].chips.flat_final.map(r => r[1]).sort();
    const singleFinal = single.chips.flat_final.map(r => r[1]).sort();
    assert.deepStrictEqual(lastFinal, singleFinal,
      'last chunk final should match unchunked final',
    );
  });

  it('saves chunked fixture for Rust e2e', () => {
    const chunks = generateChunkedFlatWitness(flatTrace, sequent, {
      calculus: illCalc,
      maxRowsPerChunk: 100,
    });

    const FIXTURE_DIR = path.join(__dirname, '..', 'zk', 'sequent-certifier', 'tests', 'fixtures');
    if (!fs.existsSync(FIXTURE_DIR)) fs.mkdirSync(FIXTURE_DIR, { recursive: true });
    const filepath = path.join(FIXTURE_DIR, 'multisig_chunked.json');
    fs.writeFileSync(filepath, JSON.stringify(chunks));
    const size = fs.statSync(filepath).size;
    console.log(`  chunked fixture: ${chunks.length} chunks, ${(size / 1024).toFixed(0)}KB`);
    assert.ok(chunks.length >= 3);
  });
});
