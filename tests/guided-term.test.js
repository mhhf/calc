/**
 * Tests for guided proof term construction (TODO_0068 §10.5).
 *
 * Tests the guided execution profile pipeline:
 *   forward.run(evidence:true) → buildGuidedTerm → check-term
 *
 * Phase 1: Unit tests with mock traces (builder logic)
 * Phase 2: Integration tests with real forward execution
 */

const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../lib/kernel/store');
const forward = require('../lib/engine/forward');
const { buildGuidedTerm, getLoliFromRule } = require('../lib/prover/guided-term');
const { rightFocusTerm, executeModeSwitch } = require('../lib/prover/bridge');

describe('Guided Proof Terms (TODO_0068 §10.5)', () => {

  beforeEach(() => { Store.clear(); });

  // ─── Phase 1: Builder Unit Tests ──────────────────────────────────

  describe('getLoliFromRule', () => {
    it('returns loli directly', () => {
      const A = Store.put('atom', ['a']);
      const B = Store.put('monad', [Store.put('atom', ['b'])]);
      const loli = Store.put('loli', [A, B]);
      assert.strictEqual(getLoliFromRule(loli), loli);
    });

    it('peels bang wrapper', () => {
      const A = Store.put('atom', ['a']);
      const B = Store.put('monad', [Store.put('atom', ['b'])]);
      const loli = Store.put('loli', [A, B]);
      const banged = Store.put('bang', [loli]);
      assert.strictEqual(getLoliFromRule(banged), loli);
    });

    it('peels forall wrapper', () => {
      const X = Store.put('metavar', ['X']);
      const body = Store.put('monad', [X]);
      const loli = Store.put('loli', [X, body]);
      const fa = Store.put('forall', [loli]);
      assert.strictEqual(getLoliFromRule(fa), loli);
    });

    it('returns null for non-loli', () => {
      const atom = Store.put('atom', ['a']);
      assert.strictEqual(getLoliFromRule(atom), null);
    });
  });

  describe('buildGuidedTerm with mock traces', () => {
    it('builds copy → loli_l → monad_l chain for single step', () => {
      // Rule: a -o { b }
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const monadB = Store.put('monad', [b]);
      const loli = Store.put('loli', [a, monadB]);

      const rfTerm = { rule: 'id', principal: b, subterms: [] };

      const trace = [{
        rule: { name: 'test', hash: loli, antecedent: { linear: [a], persistent: [] }, consequent: { linear: [b] } },
        consumed: { [a]: 1 },
        theta: [],
        slots: {},
        persistentEvidence: [],
        loliHash: null
      }];

      const term = buildGuidedTerm(trace, rfTerm);

      assert.strictEqual(term.rule, 'copy');
      assert.strictEqual(term.principal, loli);
      assert.strictEqual(term.subterms.length, 1);

      const loliL = term.subterms[0];
      assert.strictEqual(loliL.rule, 'loli_l');
      assert.strictEqual(loliL.principal, loli);
      assert.strictEqual(loliL.subterms.length, 2);

      // Antecedent proof: id(a)
      const antProof = loliL.subterms[0];
      assert.strictEqual(antProof.rule, 'id');
      assert.strictEqual(antProof.principal, a);

      // Continuation: monad_l(monadB, id(b))
      const monadL = loliL.subterms[1];
      assert.strictEqual(monadL.rule, 'monad_l');
      assert.strictEqual(monadL.principal, monadB);
      assert.strictEqual(monadL.subterms[0].rule, 'id');
      assert.strictEqual(monadL.subterms[0].principal, b);
    });

    it('builds tensor_r for multi-linear antecedent', () => {
      // Rule: a * b -o { c }
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const c = Store.put('atom', ['c']);
      const tensor = Store.put('tensor', [a, b]);
      const monadC = Store.put('monad', [c]);
      const loli = Store.put('loli', [tensor, monadC]);

      const rfTerm = { rule: 'id', principal: c, subterms: [] };

      const trace = [{
        rule: { name: 'test', hash: loli, consequent: { linear: [c] } },
        consumed: { [a]: 1, [b]: 1 },
        theta: [],
        slots: {},
        persistentEvidence: [],
        loliHash: null
      }];

      const term = buildGuidedTerm(trace, rfTerm);

      // copy → loli_l
      const loliL = term.subterms[0];
      const antProof = loliL.subterms[0];
      assert.strictEqual(antProof.rule, 'tensor_r');
      assert.strictEqual(antProof.subterms.length, 2);
      assert.strictEqual(antProof.subterms[0].rule, 'id');
      assert.strictEqual(antProof.subterms[0].principal, a);
      assert.strictEqual(antProof.subterms[1].rule, 'id');
      assert.strictEqual(antProof.subterms[1].principal, b);
    });

    it('builds promotion for persistent antecedent', () => {
      // Rule: !p -o { q }
      const p = Store.put('atom', ['p']);
      const q = Store.put('atom', ['q']);
      const bangP = Store.put('bang', [p]);
      const monadQ = Store.put('monad', [q]);
      const loli = Store.put('loli', [bangP, monadQ]);

      const rfTerm = { rule: 'id', principal: q, subterms: [] };

      const trace = [{
        rule: { name: 'test', hash: loli, consequent: { linear: [q] } },
        consumed: {},
        theta: [],
        slots: {},
        persistentEvidence: [{ goal: p, method: 'state', fact: p }],
        loliHash: null
      }];

      const term = buildGuidedTerm(trace, rfTerm);

      const loliL = term.subterms[0];
      const antProof = loliL.subterms[0];
      assert.strictEqual(antProof.rule, 'promotion');
      assert.strictEqual(antProof.subterms[0].rule, 'id');
      assert.strictEqual(antProof.subterms[0].principal, p);
    });

    it('builds tensor_r + promotion for mixed antecedent', () => {
      // Rule: a * !p -o { b }
      const a = Store.put('atom', ['a']);
      const p = Store.put('atom', ['p']);
      const b = Store.put('atom', ['b']);
      const bangP = Store.put('bang', [p]);
      const tensor = Store.put('tensor', [a, bangP]);
      const monadB = Store.put('monad', [b]);
      const loli = Store.put('loli', [tensor, monadB]);

      const rfTerm = { rule: 'id', principal: b, subterms: [] };

      const trace = [{
        rule: { name: 'test', hash: loli, consequent: { linear: [b] } },
        consumed: { [a]: 1 },
        theta: [],
        slots: {},
        persistentEvidence: [{ goal: p, method: 'state', fact: p }],
        loliHash: null
      }];

      const term = buildGuidedTerm(trace, rfTerm);

      const loliL = term.subterms[0];
      const antProof = loliL.subterms[0];
      assert.strictEqual(antProof.rule, 'tensor_r');
      assert.strictEqual(antProof.subterms[0].rule, 'id');
      assert.strictEqual(antProof.subterms[0].principal, a);
      assert.strictEqual(antProof.subterms[1].rule, 'promotion');
      assert.strictEqual(antProof.subterms[1].subterms[0].principal, p);
    });

    it('builds tensor_l for multi-fact consequent', () => {
      // Rule: a -o { b * c }
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const c = Store.put('atom', ['c']);
      const tensorBC = Store.put('tensor', [b, c]);
      const monadBC = Store.put('monad', [tensorBC]);
      const loli = Store.put('loli', [a, monadBC]);

      const rfTerm = { rule: 'one_r', principal: null, subterms: [] };

      const trace = [{
        rule: { name: 'test', hash: loli, consequent: { linear: [b, c] } },
        consumed: { [a]: 1 },
        theta: [],
        slots: {},
        persistentEvidence: [],
        loliHash: null
      }];

      const term = buildGuidedTerm(trace, rfTerm);

      const loliL = term.subterms[0];
      const monadL = loliL.subterms[1];
      assert.strictEqual(monadL.rule, 'monad_l');

      // Consequent decomposition: tensor_l
      const tensorL = monadL.subterms[0];
      assert.strictEqual(tensorL.rule, 'tensor_l');
      assert.strictEqual(tensorL.principal, tensorBC);
    });

    it('builds loli_match for linear loli consumption', () => {
      // Loli fact: a -o { b } (linear, consumed from context — no copy)
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const monadB = Store.put('monad', [b]);
      const loli = Store.put('loli', [a, monadB]);

      const rfTerm = { rule: 'id', principal: b, subterms: [] };

      const trace = [{
        rule: { name: 'loli:a', hash: null, consequent: { linear: [b] } },
        consumed: { [loli]: 1, [a]: 1 },
        theta: [],
        slots: {},
        persistentEvidence: [],
        loliHash: loli
      }];

      const term = buildGuidedTerm(trace, rfTerm);

      // Linear loli → loli_match (not copy+loli_l, since it's consumed not copied)
      assert.strictEqual(term.rule, 'loli_match');
      assert.strictEqual(term.principal, loli);
      assert.strictEqual(term.subterms.length, 2);
      assert.strictEqual(term.subterms[0].rule, 'id');
      assert.strictEqual(term.subterms[0].principal, a);
    });

    it('chains multiple steps correctly', () => {
      // Step 1: a -o { b }
      // Step 2: b -o { c }
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const c = Store.put('atom', ['c']);
      const monadB = Store.put('monad', [b]);
      const monadC = Store.put('monad', [c]);
      const loli1 = Store.put('loli', [a, monadB]);
      const loli2 = Store.put('loli', [b, monadC]);

      const rfTerm = { rule: 'id', principal: c, subterms: [] };

      const trace = [
        {
          rule: { name: 'step1', hash: loli1, consequent: { linear: [b] } },
          consumed: { [a]: 1 }, theta: [], slots: {},
          persistentEvidence: [], loliHash: null
        },
        {
          rule: { name: 'step2', hash: loli2, consequent: { linear: [c] } },
          consumed: { [b]: 1 }, theta: [], slots: {},
          persistentEvidence: [], loliHash: null
        }
      ];

      const term = buildGuidedTerm(trace, rfTerm);

      // Step 1: copy(loli1, ...)
      assert.strictEqual(term.rule, 'copy');
      assert.strictEqual(term.principal, loli1);

      // Inside step 1's monad_l, the continuation is step 2
      const loliL1 = term.subterms[0];
      const monadL1 = loliL1.subterms[1];
      const step2 = monadL1.subterms[0];
      assert.strictEqual(step2.rule, 'copy');
      assert.strictEqual(step2.principal, loli2);
    });

    it('handles metavar substitution in antecedent', () => {
      // Rule: data(X) -o { result(X) }
      const X = Store.put('metavar', ['X']);
      const dataX = Store.put('data', [X]);
      const resultX = Store.put('result', [X]);
      const monad = Store.put('monad', [resultX]);
      const loli = Store.put('loli', [dataX, monad]);

      const val = Store.put('binlit', [42n]);
      const dataVal = Store.put('data', [val]);
      const resultVal = Store.put('result', [val]);

      const rfTerm = { rule: 'id', principal: resultVal, subterms: [] };

      const trace = [{
        rule: { name: 'test', hash: loli, consequent: { linear: [resultX] } },
        consumed: { [dataVal]: 1 },
        theta: [val],     // slot 0 = val
        slots: { [X]: 0 },
        persistentEvidence: [],
        loliHash: null
      }];

      const term = buildGuidedTerm(trace, rfTerm);

      const loliL = term.subterms[0];
      // Antecedent proof: id(dataVal) — subApplyIdx(data(X), [val], {X:0}) = data(val)
      assert.strictEqual(loliL.subterms[0].rule, 'id');
      assert.strictEqual(loliL.subterms[0].principal, dataVal);
    });
  });

  // ─── Phase 2: Integration Tests ───────────────────────────────────

  describe('forward.run with evidence', () => {
    it('produces enriched trace entries', () => {
      const a = Store.put('atom', ['trigger']);
      const b = Store.put('atom', ['result']);
      const monadB = Store.put('monad', [b]);
      const loli = Store.put('loli', [a, monadB]);

      const rules = [forward.compileRule({ name: 'r1', hash: loli, antecedent: a, consequent: monadB })];

      const result = forward.run(
        { linear: { [a]: 1 }, persistent: {} },
        rules,
        { trace: true, evidence: true }
      );

      assert(result.trace, 'should have trace');
      assert.strictEqual(result.trace.length, 1);

      const entry = result.trace[0];
      assert(entry.rule, 'should have rule object');
      assert(entry.consumed, 'should have consumed');
      assert(Array.isArray(entry.theta), 'theta should be array');
      assert(entry.slots, 'should have slots');
      assert(Array.isArray(entry.persistentEvidence), 'should have persistentEvidence');
    });

    it('enriched trace feeds buildGuidedTerm', () => {
      const a = Store.put('atom', ['go']);
      const b = Store.put('atom', ['done']);
      const monadB = Store.put('monad', [b]);
      const loli = Store.put('loli', [a, monadB]);

      const rules = [forward.compileRule({ name: 'r1', hash: loli, antecedent: a, consequent: monadB })];

      const result = forward.run(
        { linear: { [a]: 1 }, persistent: {} },
        rules,
        { trace: true, evidence: true }
      );

      const rfResult = rightFocusTerm(
        result.state.linear, result.state.persistent, b, {}
      );
      assert(rfResult, 'rightFocusTerm should succeed');

      const term = buildGuidedTerm(result.trace, rfResult.term);
      assert(term, 'buildGuidedTerm should produce a term');
      assert.strictEqual(term.rule, 'copy');

      const loliL = term.subterms[0];
      assert.strictEqual(loliL.rule, 'loli_l');
      assert.strictEqual(loliL.subterms.length, 2);
    });
  });

  describe('executeModeSwitch guided', () => {
    it('produces guided monadic term via bridge', () => {
      const a = Store.put('atom', ['go']);
      const b = Store.put('atom', ['done']);
      const monadB = Store.put('monad', [b]);
      const loli = Store.put('loli', [a, monadB]);

      const rules = [forward.compileRule({ name: 'r1', hash: loli, antecedent: a, consequent: monadB })];
      const Seq = require('../lib/kernel/sequent');
      const seq = Seq.fromArrays([a], [], monadB);

      const result = executeModeSwitch(seq, {
        forwardRules: rules,
        roles: { product: 'tensor', unit: 'one', exponential: 'bang', implication: 'loli', computation: 'monad' }
      }, { forward: 'guided' });

      assert(result, 'mode switch should succeed');
      assert(result.proofNode, 'should have proofNode');
      assert.strictEqual(result.proofNode.rule, 'monad_r');
      assert(result.proofNode.state.guided, 'should be marked guided');

      const monadicTerm = result.proofNode.state.monadicTerm;
      assert(monadicTerm, 'should have monadicTerm');
      assert.strictEqual(monadicTerm.rule, 'copy');
    });
  });

  describe('check-term focused loli_l', () => {
    it('verifies 2-subterm loli_l with sequential context split', () => {
      const { createChecker } = require('../lib/prover/check-term');
      const calculus = require('../lib/index').loadILL();
      const { check } = createChecker(calculus);

      // Build: x:A⊸B in delta, a in delta, prove b
      // loli_l(x, id(a), id(b))
      //   first subterm proves A=a from delta
      //   second subterm proves C=b with B=b in delta
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const loli = Store.put('loli', [a, b]);

      const Seq = require('../lib/kernel/sequent');
      const seq = Seq.fromArrays([loli, a], [], b);

      const term = {
        rule: 'loli_l',
        principal: loli,
        subterms: [
          { rule: 'id', principal: a, subterms: [] },
          { rule: 'id', principal: b, subterms: [] }
        ]
      };

      const result = check(term, seq);
      assert(result.valid, `should be valid: ${result.error}`);
    });

    it('verifies 1-subterm loli_l (backward compat)', () => {
      const { createChecker } = require('../lib/prover/check-term');
      const calculus = require('../lib/index').loadILL();
      const { check } = createChecker(calculus);

      // Build: x:A⊸B in delta, prove B (invertible: adds A and B to delta)
      // loli_l(x, id(b))  — 1 subterm, A is added but unused (for this simple test)
      const a = Store.put('atom', ['a2']);
      const b = Store.put('atom', ['b2']);
      const loli = Store.put('loli', [a, b]);

      const Seq = require('../lib/kernel/sequent');
      const seq = Seq.fromArrays([loli], [], b);

      const term = {
        rule: 'loli_l',
        principal: loli,
        subterms: [
          { rule: 'id', principal: b, subterms: [] }
        ]
      };

      const result = check(term, seq);
      // Invertible loli_l adds both A and B to delta.
      // id(b) consumes B. A remains leftover → should fail with leftover resources.
      // (This is expected behavior — invertible loli_l leaves A in delta.)
      // In practice, the backward prover would consume A too.
      assert(!result.valid || result.unverified, 'invertible loli_l with leftover is expected');
    });
  });
});
