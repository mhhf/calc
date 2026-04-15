/**
 * ZK noFFI Witness — generates tree-path witness fixtures from
 * noFFI forward execution (clause-resolved persistent goals).
 *
 * Phase 6-1: validates the full noFFI → guided term → witness pipeline.
 * Phase 6-3: soundness validation — zero-FFI assertion, pure linear baseline.
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
const { createChecker } = require('../lib/prover/check-term');
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

/** Collect all rule names from a proof term tree. */
function collectRules(t, rules = new Set()) {
  if (!t) return rules;
  if (t.rule) rules.add(t.rule);
  if (t.subterms) for (const s of t.subterms) collectRules(s, rules);
  return rules;
}

/** Count occurrences of a specific rule in a proof term tree. */
function countRule(t, ruleName) {
  if (!t) return 0;
  let n = (t.rule === ruleName) ? 1 : 0;
  if (t.subterms) for (const s of t.subterms) n += countRule(s, ruleName);
  return n;
}

describe('ZK noFFI witness: noffi_tiny (2-step clause resolution)', { timeout: 30000 }, () => {
  let calc, illCalc, state, forwardResult, guidedTerm, witness;

  before(async () => {
    Store.clear();
    calc = await mde.load(
      path.join(__dirname, '../calculus/ill/programs/noffi_tiny.ill')
    );
    illCalc = await calculus.loadILL();
    state = mde.decomposeQuery(calc.queries.get('symex'));
  });

  it('runs forward execution with noFFI evidence', () => {
    forwardResult = calc.exec(state, {
      maxSteps: 10,
      trace: true,
      evidence: true,
      useFFI: false  // disable FFI in backward chainer for ZK-verifiable proof terms
    });

    assert.strictEqual(forwardResult.quiescent, true);
    assert.strictEqual(forwardResult.steps, 2);
    assert.strictEqual(forwardResult.trace.length, 2);

    // All evidence must be non-FFI (state lookup or clause resolution)
    for (const t of forwardResult.trace) {
      for (const ev of (t.persistentEvidence || [])) {
        assert.notStrictEqual(ev.method, 'ffi', `FFI evidence not allowed in noFFI mode`);
        if (ev.method === 'clause') assert.ok(ev.term, 'Clause evidence must include proof term');
      }
    }
    console.log(`  forward: ${forwardResult.steps} steps, all clause-resolved`);
  });

  it('builds guided proof term with ZERO ffi nodes', () => {
    const succFormula = buildSuccedentFromState(forwardResult.state);
    const linear = forwardResult.state.linear || {};
    const persistent = forwardResult.state.persistent || {};
    const rfResult = rightFocusTerm(linear, persistent, succFormula, illCalc.roles);
    assert.ok(rfResult, 'rightFocusTerm should succeed');

    const innerTerm = guidedTerm(forwardResult.trace, rfResult.term);
    guidedTerm = {
      rule: 'monad_r',
      principal: null,
      evidence: innerTerm,   // monad_r checker uses .evidence, not .subterms[0]
      subterms: [innerTerm]
    };

    const nodes = countNodes(guidedTerm);
    console.log(`  proof term: ${nodes} nodes`);
    // Should have clause proof nodes (copy/loli_l/monad_l chains)
    assert.ok(nodes > 10, `Expected >10 nodes (clause proofs), got ${nodes}`);

    // Phase 6-3: ZERO ffi nodes in the entire proof term tree
    const ffiCount = countRule(guidedTerm, 'ffi');
    assert.strictEqual(ffiCount, 0,
      `SOUNDNESS: proof term must have 0 ffi nodes, found ${ffiCount}`);

    // Verify expected clause-proof rules are present
    const rules = collectRules(guidedTerm);
    assert.ok(rules.has('copy'), 'clause proofs must use copy');
    assert.ok(rules.has('loli_l'), 'clause proofs must use loli_l');
    assert.ok(rules.has('monad_l'), 'clause proofs must use monad_l');
    assert.ok(!rules.has('ffi'), 'no ffi rule in proof term');
    console.log(`  rules used: ${[...rules].sort().join(', ')}`);
  });

  it('checkTerm validates the proof term', () => {
    // Build sequent with gamma = copy principals collected from proof term.
    // Forward rule lolis + clause lolis are ground instances synthesized at
    // proof-term-build time — not in initial state.persistent. We must walk
    // the proof term to discover them.
    const linearCtx = [];
    for (const [h, count] of Object.entries(state.linear || {})) {
      for (let i = 0; i < Number(count); i++) linearCtx.push(Number(h));
    }
    const cartesianCtx = new Set();
    function collectGamma(t) {
      if (t == null) return;
      if (t.rule === 'copy') cartesianCtx.add(t.principal);
      if (t.subterms) for (const s of t.subterms) collectGamma(s);
    }
    collectGamma(guidedTerm);

    const succFormula = buildSuccedentFromState(forwardResult.state);
    const monadSucc = Store.put('monad', [succFormula]);
    const sequent = Seq.fromArrays(linearCtx, [...cartesianCtx], monadSucc);

    const checker = createChecker(illCalc);
    const result = checker.check(guidedTerm, sequent);
    assert.strictEqual(result.valid, true,
      `checkTerm failed: ${result.error || JSON.stringify(result)}`);
    console.log('  checkTerm: valid');
  });

  it('generates ZK witness with no ffi rows', () => {
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

    witness = generateWitness(guidedTerm, sequent, { calculus: illCalc });

    // No FFI rows
    const ffiRows = (witness.chips.ffi || []).filter(r => r[0] === 1);
    assert.strictEqual(ffiRows.length, 0, `Expected 0 active ffi rows, got ${ffiRows.length}`);

    // Must have clause proof chip rows
    const copyRows = (witness.chips.copy || []).filter(r => r[0] === 1).length;
    const loliLRows = (witness.chips.loli_l || []).filter(r => r[0] === 1).length;
    const monadLRows = (witness.chips.monad_l || []).filter(r => r[0] === 1).length;

    console.log(`  copy: ${copyRows}, loli_l: ${loliLRows}, monad_l: ${monadLRows}`);
    assert.ok(copyRows > 0, 'Must have copy rows (clause proofs copy from gamma)');
    assert.ok(loliLRows > 0, 'Must have loli_l rows (clause elimination)');
    assert.ok(monadLRows > 0, 'Must have monad_l rows (clause head decomposition)');

    // Print all chip row counts
    let totalRows = 0;
    for (const [name, rows] of Object.entries(witness.chips)) {
      const active = rows.filter(r => r[0] === 1).length;
      if (active > 0) {
        console.log(`  chip ${name}: ${active} active rows`);
        totalRows += active;
      }
    }
    console.log(`  formula_rom: ${witness.formula_rom.length}, gamma_rom: ${witness.gamma_rom.length}`);
    console.log(`  total active chip rows: ${totalRows}`);
  });

  it('saves fixture for Rust e2e test', () => {
    assert.ok(witness, 'witness should exist');
    const filepath = saveFixture('clause_copy_loli', witness);
    const size = fs.statSync(filepath).size;
    console.log(`  fixture saved: ${(size / 1024).toFixed(1)}KB at ${filepath}`);
  });
});

// ─── Phase 6-3: Pure linear baseline (no persistent/clause proofs) ───────────

describe('ZK noFFI witness: pure_linear (no clause resolution)', { timeout: 30000 }, () => {
  let calc, illCalc, state, forwardResult, guidedTerm, witness;

  before(async () => {
    Store.clear();
    calc = await mde.load(
      path.join(__dirname, '../calculus/ill/programs/pure_linear.ill')
    );
    illCalc = await calculus.loadILL();
    state = mde.decomposeQuery(calc.queries.get('symex'));
  });

  it('runs forward execution with zero persistent evidence', () => {
    forwardResult = calc.exec(state, {
      maxSteps: 10,
      trace: true,
      evidence: true
    });

    assert.strictEqual(forwardResult.quiescent, true);
    assert.strictEqual(forwardResult.steps, 2);

    // No persistent evidence at all (no ! in program)
    for (const t of forwardResult.trace) {
      const persEvidence = t.persistentEvidence || [];
      assert.strictEqual(persEvidence.length, 0,
        `Pure linear step should have 0 persistent evidence, got ${persEvidence.length}`);
    }
    console.log(`  forward: ${forwardResult.steps} steps, 0 persistent evidence`);
  });

  it('builds guided proof term with zero ffi nodes', () => {
    const succFormula = buildSuccedentFromState(forwardResult.state);
    const linear = forwardResult.state.linear || {};
    const persistent = forwardResult.state.persistent || {};
    const rfResult = rightFocusTerm(linear, persistent, succFormula, illCalc.roles);
    assert.ok(rfResult, 'rightFocusTerm should succeed');

    const innerTerm = guidedTerm(forwardResult.trace, rfResult.term);
    guidedTerm = {
      rule: 'monad_r',
      principal: null,
      subterms: [innerTerm]
    };

    // Zero ffi nodes — the critical soundness assertion
    const ffiCount = countRule(guidedTerm, 'ffi');
    assert.strictEqual(ffiCount, 0, 'pure linear: 0 ffi nodes');

    const rules = collectRules(guidedTerm);
    assert.ok(!rules.has('ffi'), 'no ffi');
    // copy nodes ARE expected (for using rules from gamma) — just no clause RESOLUTION
    console.log(`  nodes: ${countNodes(guidedTerm)}, rules: ${[...rules].sort().join(', ')}`);
  });

  it('generates ZK witness with zero clause-resolution evidence', () => {
    const linearCtx = [];
    for (const [h, count] of Object.entries(state.linear || {})) {
      for (let i = 0; i < Number(count); i++) linearCtx.push(Number(h));
    }
    // Rules used from gamma (copy nodes exist for rule applications)
    const cartesianCtx = [];
    for (const h of Object.keys(state.persistent || {})) {
      cartesianCtx.push(Number(h));
    }
    const succFormula = buildSuccedentFromState(forwardResult.state);
    const monadSucc = Store.put('monad', [succFormula]);
    const sequent = Seq.fromArrays(linearCtx, cartesianCtx, monadSucc);

    witness = generateWitness(guidedTerm, sequent, { calculus: illCalc });

    // Key soundness property: zero persistent evidence means no clause proofs
    // were needed. The proof term uses copy/loli_l/monad_l for rule APPLICATION
    // (every forward step copies a rule from gamma and applies it), but there
    // are no additional clause resolution chains for persistent preconditions.
    for (const t of forwardResult.trace) {
      const persEvidence = t.persistentEvidence || [];
      assert.strictEqual(persEvidence.length, 0,
        'pure linear: no persistent evidence (no clause resolution)');
    }

    // Print summary
    let totalRows = 0;
    for (const [name, rows] of Object.entries(witness.chips)) {
      const active = rows.filter(r => r[0] === 1).length;
      if (active > 0) {
        console.log(`  chip ${name}: ${active} active rows`);
        totalRows += active;
      }
    }
    const activeGamma = witness.gamma_rom.filter(r => r[1] === 1).length;
    console.log(`  formula_rom: ${witness.formula_rom.length}, gamma_rom active: ${activeGamma}`);
    console.log(`  total active chip rows: ${totalRows}`);
  });

  it('saves fixture for Rust e2e test', () => {
    assert.ok(witness, 'witness should exist');
    const filepath = saveFixture('pure_linear', witness);
    const size = fs.statSync(filepath).size;
    console.log(`  fixture saved: ${(size / 1024).toFixed(1)}KB at ${filepath}`);
  });
});
