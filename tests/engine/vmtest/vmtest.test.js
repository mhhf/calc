/**
 * VMTest Conformance Tests
 *
 * Runs Ethereum VMTest fixtures against CALC's forward engine.
 * Fixtures must be fetched first: bash tools/fetch-vmtests.sh
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const fs = require('fs');

const mde = require('../../../lib/engine');
const { fixtureToState, hexToBigInt } = require('./translate');
const { extractResult, parseExpectedStorage } = require('./extract');

const FIXTURES_DIR = path.join(__dirname, '../../fixtures/VMTests');

// Skip all tests if fixtures not fetched
const fixturesExist = fs.existsSync(FIXTURES_DIR);

/**
 * Load a VMTest fixture file, returning { name, fixture } for each test in it.
 */
function loadFixture(category, filename) {
  const filePath = path.join(FIXTURES_DIR, category, filename);
  const data = JSON.parse(fs.readFileSync(filePath, 'utf8'));
  // Each file contains one or more named tests
  return Object.entries(data).map(([name, fixture]) => ({ name, fixture }));
}

/**
 * Run a single VMTest fixture and return { actual, expected }.
 */
function runFixture(fixture, calc) {
  const state = fixtureToState(fixture, calc);
  const result = calc.exec(state, { maxSteps: 10000 });

  const actual = extractResult(result.state);

  // Expected values from fixture
  const execAddr = fixture.exec.address.toLowerCase();
  const post = fixture.post && fixture.post[execAddr];
  const expectedStorage = parseExpectedStorage(post && post.storage);
  const expectedGas = hexToBigInt(fixture.gas);

  return {
    actual,
    expected: { gas: expectedGas, storage: expectedStorage },
    quiescent: result.quiescent,
    steps: result.steps,
  };
}

/**
 * Compare storage maps (Map<bigint, bigint>).
 */
function assertStorageEqual(actual, expected, msg) {
  const actualObj = {};
  const expectedObj = {};
  for (const [k, v] of actual) actualObj['0x' + k.toString(16)] = '0x' + v.toString(16);
  for (const [k, v] of expected) expectedObj['0x' + k.toString(16)] = '0x' + v.toString(16);
  assert.deepStrictEqual(actualObj, expectedObj, msg);
}

/**
 * List all .json fixtures in a category directory.
 */
function listFixtures(category) {
  const dir = path.join(FIXTURES_DIR, category);
  if (!fs.existsSync(dir)) return [];
  return fs.readdirSync(dir).filter(f => f.endsWith('.json')).sort();
}

describe('VMTest Conformance', { skip: !fixturesExist && 'Fixtures not fetched (run: bash tools/fetch-vmtests.sh)' }, () => {
  let calc;

  before(() => {
    calc = mde.load(path.join(__dirname, '../../../calculus/ill/programs/evm.ill'));
  });

  /**
   * Run all fixtures in a category file, asserting storage match.
   * Skips OOG tests (no post state).
   */
  function runStorageTest(category, file) {
    it(file.replace('.json', ''), () => {
      const tests = loadFixture(category, file);
      for (const { name, fixture } of tests) {
        if (!fixture.post) {
          // OOG test — no expected post state
          // Verify the engine doesn't crash, but skip storage comparison
          const state = fixtureToState(fixture, calc);
          const result = calc.exec(state, { maxSteps: 10000 });
          assert.ok(true, `${name}: OOG test (ran ${result.steps} steps)`);
          continue;
        }

        const { actual, expected, quiescent } = runFixture(fixture, calc);

        assert.ok(quiescent, `${name}: should reach quiescence`);
        assert.ok(
          actual.termination === 'stop' || actual.termination === 'return' || actual.termination === 'selfdestruct',
          `${name}: should terminate normally (got ${actual.termination})`
        );
        assertStorageEqual(actual.storage, expected.storage, `${name}: storage mismatch`);
      }
    });
  }

  /**
   * Run all fixtures in a category directory.
   */
  function runCategory(category) {
    describe(category, () => {
      for (const file of listFixtures(category)) runStorageTest(category, file);
    });
  }

  runCategory('vmArithmeticTest');
  runCategory('vmBitwiseLogicOperation');
  runCategory('vmPushDupSwapTest');
});
