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
const Seq = require('../lib/kernel/sequent');
const { createSequentParser } = require('../lib/parser/sequent-parser');
const { createProver } = require('../lib/prover/focused');
const { buildRuleSpecs } = require('../lib/prover/rule-interpreter');
const { extractTerm } = require('../lib/prover/generic-term');
const { createChecker } = require('../lib/prover/check-term');
const { generateWitness, deriveZkTags } = require('../lib/zk/witness');

let calc;
let seqParser;
let prover;
let checker;
let ruleSpecs;
let alternatives;
let ZK_TAGS;

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
  const witness = generateWitness(term, seq, { calculus: calc });

  // Save fixture for Rust integration tests
  if (name) saveFixture(name, witness);

  return { term, witness, seq };
}

function proveAndWitnessCart(linear, cartesian, succ, name) {
  const lf = linear.map(f => typeof f === 'string' ? calc.parse(f) : f);
  const cf = cartesian.map(f => typeof f === 'string' ? calc.parse(f) : f);
  const sf = typeof succ === 'string' ? calc.parse(succ) : succ;
  const seq = Seq.fromArrays(lf, cf, sf);
  const result = prover.prove(seq, { rules: ruleSpecs, alternatives });
  assert.strictEqual(result.success, true, `proof should succeed`);
  const term = extractTerm(result.proofTree, calc);
  assert.ok(term, 'term extraction should succeed');
  const checkResult = checker.check(term, seq);
  assert.strictEqual(checkResult.valid, true,
    `term should be valid: ${checkResult.error || ''}`);
  const witness = generateWitness(term, seq, { calculus: calc });
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
  ZK_TAGS = deriveZkTags(calc);
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

  describe('loli_l', () => {
    it('P, P -o Q |- Q (modus ponens)', () => {
      const { witness } = proveAndWitness('P, P -o Q |- Q', 'loli_l');

      assert.ok(witness.chips.loli_l, 'should have loli_l rows');
      assert.strictEqual(witness.chips.loli_l.length, 1, '1 loli_l row');
      assert.ok(witness.chips.id.length >= 2, 'should have 2 id rows');
      assert.strictEqual(witness.formula_rom.length, 1, '1 formula ROM entry (P-oQ)');

      const rom = witness.formula_rom[0];
      assert.strictEqual(rom[1], ZK_TAGS.loli, 'tag=LOLI');
    });
  });

  describe('oplus', () => {
    it('A |- A + B (oplus_r1)', () => {
      const { witness } = proveAndWitness('A |- A + B', 'oplus_r1');

      assert.ok(witness.chips.oplus_r1, 'should have oplus_r1 rows');
      assert.strictEqual(witness.chips.oplus_r1.length, 1, '1 oplus_r1 row');
      assert.ok(witness.chips.id.length >= 1, 'should have id row');
      assert.strictEqual(witness.formula_rom.length, 1, '1 formula ROM entry');

      const rom = witness.formula_rom[0];
      assert.strictEqual(rom[1], ZK_TAGS.oplus, 'tag=OPLUS');
    });
  });

  describe('with_l', () => {
    it('A & B |- A (with_l1)', () => {
      const { witness } = proveAndWitness('A & B |- A', 'with_l1');

      assert.ok(witness.chips.with_l1, 'should have with_l1 rows');
      assert.strictEqual(witness.chips.with_l1.length, 1, '1 with_l1 row');
      assert.ok(witness.chips.id.length >= 1, 'should have id row');
      assert.strictEqual(witness.formula_rom.length, 1, '1 formula ROM entry');

      const rom = witness.formula_rom[0];
      assert.strictEqual(rom[1], ZK_TAGS.with, 'tag=WITH');
    });
  });

  describe('one_l', () => {
    it('I, A |- A (one_l)', () => {
      const { witness } = proveAndWitness('I, A |- A', 'one_l');

      assert.ok(witness.chips.one_l, 'should have one_l rows');
      assert.strictEqual(witness.chips.one_l.length, 1, '1 one_l row');
      assert.ok(witness.chips.id.length >= 1, 'should have id row');
    });
  });

  describe('zero_l', () => {
    it('zero |- C (ex falso)', () => {
      const { witness } = proveAndWitness('zero |- C', 'zero_l');

      assert.ok(witness.chips.zero_l.length >= 1, 'should have zero_l rows');
      // zero_l consumes the obligation — no id rows needed
      assert.strictEqual(witness.formula_rom.length, 1, '1 formula ROM entry');

      const rom = witness.formula_rom[0];
      assert.strictEqual(rom[1], ZK_TAGS.zero, 'tag=ZERO');
    });
  });

  describe('bang', () => {
    it('!A |- A (dereliction)', () => {
      const { witness } = proveAndWitness('!A |- A', 'bang_dereliction');

      assert.ok(witness.chips.bang_l, 'should have bang_l rows');
      assert.strictEqual(witness.chips.bang_l.length, 1, '1 bang_l row');
      assert.ok(witness.chips.id.length >= 1, 'should have id row');
      assert.strictEqual(witness.formula_rom.length, 1, '1 formula ROM entry');

      const rom = witness.formula_rom[0];
      assert.strictEqual(rom[1], ZK_TAGS.bang, 'tag=BANG');
    });
  });

  describe('copy (cartesian)', () => {
    it('; A |- A (copy from gamma)', () => {
      const { witness } = proveAndWitnessCart([], ['A'], 'A', 'copy');

      assert.ok(witness.chips.copy, 'should have copy rows');
      assert.strictEqual(witness.chips.copy.length, 1, '1 copy row');
      assert.ok(witness.chips.id.length >= 1, 'should have id row');
      assert.strictEqual(witness.formula_rom.length, 0, 'no formula ROM');
      assert.strictEqual(witness.gamma_rom.length, 1, '1 gamma ROM entry');
    });
  });

  describe('nested', () => {
    it('(A * B) -o C, A, B |- C (loli_l + tensor_r)', () => {
      const { witness } = proveAndWitness('(A * B) -o C, A, B |- C', 'nested_loli_tensor');

      assert.ok(witness.chips.loli_l, 'should have loli_l rows');
      assert.ok(witness.chips.tensor_r, 'should have tensor_r rows');
      assert.ok(witness.chips.id.length >= 2, 'should have 2+ id rows');
      assert.strictEqual(witness.formula_rom.length, 2, '2 formula ROM entries');
    });
  });

  describe('fixture generation', () => {
    it('saves all fixtures', () => {
      ensureFixtureDir();
      const files = fs.readdirSync(FIXTURE_DIR).filter(f => f.endsWith('.json'));
      assert.ok(files.length >= 13, `should have >= 13 fixtures, got ${files.length}`);
    });
  });
});
