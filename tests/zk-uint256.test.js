/**
 * ZK Phase 6-6b: 256-bit arithmetic integration tests.
 *
 * Tests the JS-side uint256 predicate extraction and witness generation.
 * The Rust side (Uint256ArithChip + ByteCheckRomAir) is tested standalone
 * in zk/proof-checker/tests/p6_uint256.rs.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');

const Store = require('../lib/kernel/store');
const {
  extractUint256PredMeta,
  bigintToLimbs,
  computeAdditionCarries,
  computeIncrementCarries,
} = require('../lib/zk/witness');

const FIXTURE_DIR = path.join(__dirname, '..', 'zk', 'proof-checker', 'tests', 'fixtures');

function ensureFixtureDir() {
  if (!fs.existsSync(FIXTURE_DIR)) {
    fs.mkdirSync(FIXTURE_DIR, { recursive: true });
  }
}

// ---------------------------------------------------------------------------
// Unit tests: limb decomposition helpers
// ---------------------------------------------------------------------------

describe('bigintToLimbs', () => {
  it('decomposes 0 to all-zero limbs', () => {
    const limbs = bigintToLimbs(0n);
    assert.strictEqual(limbs.length, 32);
    assert.ok(limbs.every(l => l === 0));
  });

  it('decomposes small value into first limb', () => {
    const limbs = bigintToLimbs(42n);
    assert.strictEqual(limbs[0], 42);
    assert.ok(limbs.slice(1).every(l => l === 0));
  });

  it('decomposes 256 into two limbs', () => {
    const limbs = bigintToLimbs(256n);
    assert.strictEqual(limbs[0], 0);
    assert.strictEqual(limbs[1], 1);
  });

  it('decomposes value > BabyBear', () => {
    // 3000000000 = 0xB2D05E00
    const limbs = bigintToLimbs(3000000000n);
    assert.strictEqual(limbs[0], 0x00);
    assert.strictEqual(limbs[1], 0x5E);
    assert.strictEqual(limbs[2], 0xD0);
    assert.strictEqual(limbs[3], 0xB2);
    assert.ok(limbs.slice(4).every(l => l === 0));
  });

  it('decomposes max uint256', () => {
    const max = (1n << 256n) - 1n;
    const limbs = bigintToLimbs(max);
    assert.ok(limbs.every(l => l === 255));
  });
});

// ---------------------------------------------------------------------------
// Unit tests: carry computation
// ---------------------------------------------------------------------------

describe('computeAdditionCarries', () => {
  it('no carry for small addition', () => {
    const a = bigintToLimbs(3n);
    const b = bigintToLimbs(5n);
    const carries = computeAdditionCarries(a, b);
    assert.ok(carries.every(c => c === 0));
  });

  it('carry from limb 0 when sum >= 256', () => {
    const a = bigintToLimbs(200n);
    const b = bigintToLimbs(100n);
    const carries = computeAdditionCarries(a, b);
    assert.strictEqual(carries[0], 1); // 200+100=300 → carry
    assert.strictEqual(carries[1], 0);
  });

  it('carry chain for 0xFF + 0x01', () => {
    const a = bigintToLimbs(255n);
    const b = bigintToLimbs(1n);
    const carries = computeAdditionCarries(a, b);
    assert.strictEqual(carries[0], 1);
    assert.strictEqual(carries[1], 0);
  });
});

describe('computeIncrementCarries', () => {
  it('no carry for small increment', () => {
    const a = bigintToLimbs(5n);
    const carries = computeIncrementCarries(a);
    assert.ok(carries.every(c => c === 0));
  });

  it('carry when limb 0 is 255', () => {
    const a = bigintToLimbs(255n);
    const carries = computeIncrementCarries(a);
    assert.strictEqual(carries[0], 1);
    assert.strictEqual(carries[1], 0);
  });
});

// ---------------------------------------------------------------------------
// Unit tests: extractUint256PredMeta
// ---------------------------------------------------------------------------

describe('extractUint256PredMeta', () => {
  before(() => {
    Store.clear();
  });

  it('returns null for small-value plus (handled by pred_rom)', () => {
    const a = Store.put('binlit', [3n]);
    const b = Store.put('binlit', [5n]);
    const c = Store.put('binlit', [8n]);
    const pred = Store.put('plus', [a, b, c]);
    assert.strictEqual(extractUint256PredMeta(pred), null);
  });

  it('returns metadata for large-value plus', () => {
    const bigA = 3000000000n; // > BabyBear prime (2013265921)
    const bigB = 1n;
    const bigC = 3000000001n;
    const a = Store.put('binlit', [bigA]);
    const b = Store.put('binlit', [bigB]);
    const c = Store.put('binlit', [bigC]);
    const pred = Store.put('plus', [a, b, c]);

    const meta = extractUint256PredMeta(pred);
    assert.ok(meta, 'should return metadata for large-value plus');
    assert.strictEqual(meta.is_plus_256, 1);
    assert.strictEqual(meta.is_inc_256, 0);
    assert.strictEqual(meta.a_limbs.length, 32);
    assert.strictEqual(meta.b_limbs.length, 32);
    assert.strictEqual(meta.c_limbs.length, 32);
    assert.strictEqual(meta.carries.length, 32);

    // Verify limbs match
    assert.deepStrictEqual(meta.a_limbs, bigintToLimbs(bigA));
    assert.deepStrictEqual(meta.c_limbs, bigintToLimbs(bigC));
  });

  it('returns metadata for large-value inc', () => {
    const bigA = 2013265920n; // BabyBear - 1 (fits in BabyBear but result doesn't)
    const bigB = 2013265921n; // = BabyBear prime (doesn't fit)
    const a = Store.put('binlit', [bigA]);
    const b = Store.put('binlit', [bigB]);
    const pred = Store.put('inc', [a, b]);

    const meta = extractUint256PredMeta(pred);
    assert.ok(meta, 'should return metadata for large-value inc');
    assert.strictEqual(meta.is_plus_256, 0);
    assert.strictEqual(meta.is_inc_256, 1);
  });

  it('returns null for non-arithmetic predicates', () => {
    const a = Store.put('binlit', [3000000000n]);
    const pred = Store.put('arr_get', [a, a, a]);
    assert.strictEqual(extractUint256PredMeta(pred), null);
  });

  it('returns null for unrecognized tags', () => {
    const a = Store.put('binlit', [3000000000n]);
    const pred = Store.put('neq', [a, a]);
    assert.strictEqual(extractUint256PredMeta(pred), null);
  });
});

// ---------------------------------------------------------------------------
// Integration: generate fixture with uint256 entries for Rust E2E
// ---------------------------------------------------------------------------

describe('uint256 fixture generation', { timeout: 30000 }, () => {
  it('generates a fixture with uint256_arith entries from a modified witness', () => {
    Store.clear();

    // Load the base fixture (custom_chip_inc — a valid proven witness)
    const basePath = path.join(FIXTURE_DIR, 'custom_chip_inc.json');
    if (!fs.existsSync(basePath)) {
      // Skip if base fixture doesn't exist (requires running zk-custom-chip.test.js first)
      return;
    }
    const base = JSON.parse(fs.readFileSync(basePath, 'utf8'));

    // Create uint256_arith entries with num_lookups=0.
    // This doesn't affect PRED_BUS balance (0 supply contribution)
    // but tests that the Rust bridge correctly constructs the chips.
    const bigA = 3000000000n;
    const bigB = 1n;
    const bigC = 3000000001n;
    const aLimbs = bigintToLimbs(bigA);
    const bLimbs = bigintToLimbs(bigB);
    const cLimbs = bigintToLimbs(bigC);
    const carries = computeAdditionCarries(aLimbs, bLimbs);

    // Build uint256_arith row: [prep (100 cols), main (33 cols)]
    const row = [
      999999, // pred_hash (synthetic — not in fact_axiom, so num_lookups=0)
      1,      // is_active
      1,      // is_plus_256
      0,      // is_inc_256
      ...aLimbs, ...bLimbs, ...cLimbs,
      0,      // num_lookups = 0 (no PRED_BUS connection)
      ...carries,
    ];
    assert.strictEqual(row.length, 133, 'uint256_arith row should be 133 cols');

    // Compute byte_check_rom counts
    const byteCounts = new Array(256).fill(0);
    for (let i = 0; i < 32; i++) {
      byteCounts[aLimbs[i]]++;
      byteCounts[bLimbs[i]]++;
      byteCounts[cLimbs[i]]++;
    }

    // Add to base fixture
    base.uint256_arith = [row];
    base.byte_check_rom = byteCounts;

    // Save fixture for Rust E2E test
    ensureFixtureDir();
    const outPath = path.join(FIXTURE_DIR, 'uint256_e2e.json');
    fs.writeFileSync(outPath, JSON.stringify(base, null, 2));

    // Verify the saved fixture has the right structure
    const saved = JSON.parse(fs.readFileSync(outPath, 'utf8'));
    assert.strictEqual(saved.uint256_arith.length, 1);
    assert.strictEqual(saved.uint256_arith[0].length, 133);
    assert.strictEqual(saved.byte_check_rom.length, 256);
  });
});
