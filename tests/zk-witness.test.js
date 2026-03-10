/**
 * ZK Witness Generator — unit tests.
 *
 * Validates that generateWitness produces correct per-chip traces
 * for known proof terms. These traces are also saved as fixtures
 * for Rust integration tests (p1f_e2e).
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');

const calculus = require('../lib/calculus');
const { createSequentParser } = require('../lib/parser/sequent-parser');
const { createProver } = require('../lib/prover/focused');
const { buildRuleSpecs } = require('../lib/prover/rule-interpreter');
const { extractTerm } = require('../lib/prover/generic-term');
const { createChecker } = require('../lib/prover/check-term');
const { generateWitness, ZK_TAGS } = require('../lib/zk/witness');

let calc;
let seqParser;
let prover;
let checker;
let ruleSpecs;
let alternatives;

const FIXTURE_DIR = path.join(__dirname, '..', 'zk', 'ill-checker', 'tests', 'fixtures');

function ensureFixtureDir() {
  if (!fs.existsSync(FIXTURE_DIR)) {
    fs.mkdirSync(FIXTURE_DIR, { recursive: true });
  }
}

function saveFixture(name, data) {
  ensureFixtureDir();
  fs.writeFileSync(
    path.join(FIXTURE_DIR, `${name}.json`),
    JSON.stringify(data, null, 2),
  );
}

function proveAndWitness(sequentStr, name) {
  const seq = seqParser.parseSequent(sequentStr);
  const result = prover.prove(seq, { rules: ruleSpecs, alternatives });
  assert.strictEqual(result.success, true, `proof should succeed: ${sequentStr}`);

  const term = extractTerm(result.proofTree, calc);
  assert.ok(term, 'term extraction should succeed');

  // Verify the term with the checker
  const checkResult = checker.check(term, seq);
  assert.strictEqual(checkResult.valid, true,
    `term should be valid: ${checkResult.error || ''}`);

  // Generate witness
  const witness = generateWitness(term, seq);

  // Save fixture for Rust integration tests
  if (name) saveFixture(name, witness);

  return { term, witness, seq };
}

before(async () => {
  calc = await calculus.loadILL();
  seqParser = createSequentParser(calc);
  prover = createProver(calc);
  checker = createChecker(calc);
  const built = buildRuleSpecs(calc);
  ruleSpecs = built.specs;
  alternatives = built.alternatives;
});

describe('ZK Witness Generator', () => {

  describe('basic structure', () => {
    it('A |- A (identity)', () => {
      const { witness } = proveAndWitness('A |- A', 'identity');

      // Should have init rows and id rows
      assert.ok(witness.chips.init.length >= 1, 'should have init rows');
      assert.ok(witness.chips.id.length >= 1, 'should have id rows');

      // Init: [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax]
      const initRow = witness.chips.init[0];
      assert.strictEqual(initRow[1], 1, 'ctx_active');
      assert.strictEqual(initRow[3], 1, 'oblig_active');
      assert.strictEqual(initRow[4], 0, 'nonce=0');
      assert.strictEqual(initRow[5], 0, 'lax=0');
      // ctx_hash === oblig_hash (A |- A)
      assert.strictEqual(initRow[0], initRow[2], 'ctx and oblig hash should match');

      // id: [active, hash, nonce_in, lax]
      const idRow = witness.chips.id[0];
      assert.strictEqual(idRow[0], 1, 'active');
      assert.strictEqual(idRow[2], 0, 'nonce_in=0');
      assert.strictEqual(idRow[3], 0, 'lax=0');

      // No formula ROM needed (id doesn't do formula lookup)
      assert.strictEqual(witness.formula_rom.length, 0, 'no formula ROM');
      assert.strictEqual(witness.gamma_rom.length, 0, 'no gamma ROM');
    });
  });

  describe('tensor', () => {
    it('A, B |- A * B (tensor_r)', () => {
      const { witness } = proveAndWitness('A, B |- A * B', 'tensor_r');

      assert.ok(witness.chips.init.length >= 2, 'should have 2+ init rows');
      assert.ok(witness.chips.tensor_r, 'should have tensor_r rows');
      assert.strictEqual(witness.chips.tensor_r.length, 1, '1 tensor_r row');
      assert.ok(witness.chips.id.length >= 2, 'should have 2 id rows');
      assert.strictEqual(witness.formula_rom.length, 1, '1 formula ROM entry');

      // Formula ROM: [hash, tag, c0, c1, is_active, num_lookups]
      const rom = witness.formula_rom[0];
      assert.strictEqual(rom[1], ZK_TAGS.tensor, 'tag=TENSOR');
      assert.strictEqual(rom[4], 1, 'is_active');
      assert.strictEqual(rom[5], 1, 'num_lookups=1');
    });

    it('A * B |- B * A (tensor swap)', () => {
      const { witness } = proveAndWitness('A * B |- B * A', 'tensor_swap');

      assert.ok(witness.chips.tensor_l, 'should have tensor_l rows');
      assert.ok(witness.chips.tensor_r, 'should have tensor_r rows');
      assert.ok(witness.chips.id.length >= 2, 'should have 2 id rows');
      // Formula ROM: A*B (tensor_l lookup) + B*A (tensor_r lookup)
      assert.strictEqual(witness.formula_rom.length, 2, '2 formula ROM entries');
    });
  });

  describe('loli', () => {
    it('|- A -o A (loli_r)', () => {
      const { witness } = proveAndWitness('|- A -o A', 'loli_r');

      assert.ok(witness.chips.loli_r, 'should have loli_r rows');
      assert.strictEqual(witness.chips.loli_r.length, 1, '1 loli_r row');
      assert.ok(witness.chips.id.length >= 1, 'should have id row');
      assert.strictEqual(witness.formula_rom.length, 1, '1 formula ROM entry');
    });
  });

  describe('with', () => {
    it('A |- A & A (with_r + dup)', () => {
      const { witness } = proveAndWitness('A |- A & A', 'with_r');

      assert.ok(witness.chips.with_r, 'should have with_r rows');
      assert.ok(witness.chips.dup.length >= 1, 'should have dup rows');
      assert.ok(witness.chips.id.length >= 2, 'should have 2 id rows');
    });
  });

  describe('unit', () => {
    it('|- I (one_r)', () => {
      const { witness } = proveAndWitness('|- I', 'one_r');

      assert.ok(witness.chips.one_r, 'should have one_r rows');
      assert.strictEqual(witness.chips.one_r.length, 1, '1 one_r row');
      // No context in the sequent
      assert.strictEqual(witness.chips.init[0][1], 0, 'no ctx_active');
    });
  });

  describe('fixture generation', () => {
    it('saves all fixtures', () => {
      // Just verify the fixtures directory was created and files exist
      ensureFixtureDir();
      const files = fs.readdirSync(FIXTURE_DIR).filter(f => f.endsWith('.json'));
      assert.ok(files.length >= 5, `should have >= 5 fixtures, got ${files.length}`);
    });
  });
});
