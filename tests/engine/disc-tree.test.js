/**
 * Tests for discrimination tree rule indexing
 */

const { describe, it, before, beforeEach } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { isMetavar } = require('../../lib/kernel/unify');
const {
  createNode, insert, flattenPattern, flattenFact,
  subtreeSize, queryFlat, collectAll, makeDiscTreeLayer, WILDCARD
} = require('../../lib/prover/strategy/disc-tree');
const {
  explore, countNodes, countLeaves, maxDepth, getAllLeaves,
  buildStrategyStack, makeDiscTreeLayer: makeDiscTreeLayerFromSymexec
} = require('../../lib/prover/strategy/symexec');
const forward = require('../../lib/prover/strategy/forward');
const mde = require('../../lib/engine');

describe('disc-tree', () => {
  beforeEach(() => Store.clear());

  describe('flattenPattern', () => {
    it('flattens ground term to tag sequence', () => {
      const e = Store.put('atom', ['e']);
      const i_e = Store.put('i', [e]);
      const code = Store.put('code', [i_e, e]);
      const len = flattenPattern(code);
      // code(i(e_atom), e_atom) → [code, i, atom, atom]
      assert.strictEqual(len, 4);
    });

    it('flattens metavar to WILDCARD', () => {
      const mv = Store.put('freevar', ['_X']);
      const code = Store.put('code', [mv, mv]);
      const len = flattenPattern(code);
      // code(_X, _X) → [code, WILDCARD, WILDCARD]
      assert.strictEqual(len, 3);
    });

    it('handles mixed ground and metavar', () => {
      const mv = Store.put('freevar', ['_X']);
      const e = Store.put('atom', ['e']);
      const code = Store.put('code', [mv, e]);
      const len = flattenPattern(code);
      // code(_X, e_atom) → [code, WILDCARD, atom]
      assert.strictEqual(len, 3);
    });
  });

  describe('flattenFact', () => {
    it('flattens ground fact with arity metadata', () => {
      const e = Store.put('atom', ['e']);
      const i_e = Store.put('i', [e]);
      const code = Store.put('code', [i_e, e]);
      const len = flattenFact(code);
      assert.strictEqual(len, 4);
    });
  });

  describe('subtreeSize', () => {
    it('computes size of leaf node (arity 0)', () => {
      // Atom has arity 1 (string child) but Store.arity returns count of term children
      // For a simple atom like 'e', arity=1 (the string). But in our flattened representation,
      // atom nodes have arity from Store.arity which includes the string child.
      const e = Store.put('atom', ['e']);
      const len = flattenFact(e);
      // atom 'e' is just 1 position (leaf in preorder)
      assert.strictEqual(len, 1);
      assert.strictEqual(subtreeSize(0, len), 1);
    });

    it('computes size of unary node', () => {
      const e = Store.put('atom', ['e']);
      const i_e = Store.put('i', [e]);
      const len = flattenFact(i_e);
      // i(atom) → [i, atom] → size at pos 0 = 2
      assert.strictEqual(subtreeSize(0, len), 2);
      assert.strictEqual(subtreeSize(1, len), 1);
    });

    it('computes size of binary node', () => {
      const e = Store.put('atom', ['e']);
      const code = Store.put('code', [e, e]);
      const len = flattenFact(code);
      // code(atom, atom) → [code, atom, atom] → size at 0 = 3
      assert.strictEqual(subtreeSize(0, len), 3);
      assert.strictEqual(subtreeSize(1, len), 1);
      assert.strictEqual(subtreeSize(2, len), 1);
    });
  });

  describe('insert + query', () => {
    it('exact match: ground pattern matches same ground fact', () => {
      const root = createNode();
      const e = Store.put('atom', ['e']);
      const code = Store.put('code', [e, e]);

      const rule = { name: 'test', antecedent: { linear: [code] }, triggerPreds: ['code'] };
      insert(root, code, rule);

      const results = [];
      const len = flattenFact(code);
      queryFlat(root, len, results);
      assert.strictEqual(results.length, 1);
      assert.strictEqual(results[0], rule);
    });

    it('wildcard pattern matches any fact with same head', () => {
      const root = createNode();
      const mv = Store.put('freevar', ['_X']);
      const e = Store.put('atom', ['e']);
      const pattern = Store.put('code', [mv, e]);
      const fact = Store.put('code', [e, e]);

      const rule = { name: 'wild', antecedent: { linear: [pattern] }, triggerPreds: ['code'] };
      insert(root, pattern, rule);

      const results = [];
      const len = flattenFact(fact);
      queryFlat(root, len, results);
      assert.strictEqual(results.length, 1);
      assert.strictEqual(results[0], rule);
    });

    it('wildcard skips deep subtrees', () => {
      const root = createNode();
      const mv = Store.put('freevar', ['_X']);
      const e = Store.put('atom', ['e']);
      // Pattern: code(_X, e) — _X matches any subtree
      const pattern = Store.put('code', [mv, e]);

      // Fact: code(i(i(e)), e) — deep subtree at first child
      const deep = Store.put('i', [Store.put('i', [e])]);
      const fact = Store.put('code', [deep, e]);

      const rule = { name: 'deep', antecedent: { linear: [pattern] }, triggerPreds: ['code'] };
      insert(root, pattern, rule);

      const results = [];
      const len = flattenFact(fact);
      queryFlat(root, len, results);
      assert.strictEqual(results.length, 1);
    });

    it('returns empty for non-matching head', () => {
      const root = createNode();
      const e = Store.put('atom', ['e']);
      const codePattern = Store.put('code', [e, e]);
      const pcFact = Store.put('pc', [e]);

      const rule = { name: 'test', antecedent: { linear: [codePattern] }, triggerPreds: ['code'] };
      insert(root, codePattern, rule);

      const results = [];
      const len = flattenFact(pcFact);
      queryFlat(root, len, results);
      assert.strictEqual(results.length, 0);
    });

    it('multiple rules with different patterns', () => {
      const root = createNode();
      const e = Store.put('atom', ['e']);
      const mv = Store.put('freevar', ['_X']);
      const i_e = Store.put('i', [e]);

      // Rule 1: code(i(e), _X)
      const p1 = Store.put('code', [i_e, mv]);
      const r1 = { name: 'r1', antecedent: { linear: [p1] }, triggerPreds: ['code'] };
      insert(root, p1, r1);

      // Rule 2: code(_X, _X)
      const mv2 = Store.put('freevar', ['_Y']);
      const p2 = Store.put('code', [mv, mv2]);
      const r2 = { name: 'r2', antecedent: { linear: [p2] }, triggerPreds: ['code'] };
      insert(root, p2, r2);

      // Fact: code(i(e), e) — matches both
      const fact = Store.put('code', [i_e, e]);
      const results = [];
      const len = flattenFact(fact);
      queryFlat(root, len, results);
      assert.strictEqual(results.length, 2);
      assert(results.includes(r1));
      assert(results.includes(r2));
    });

    it('all-wildcard pattern matches everything with same arity', () => {
      const root = createNode();
      const mv1 = Store.put('freevar', ['_A']);
      const mv2 = Store.put('freevar', ['_B']);
      const pattern = Store.put('code', [mv1, mv2]);
      const rule = { name: 'any', antecedent: { linear: [pattern] }, triggerPreds: ['code'] };
      insert(root, pattern, rule);

      const e = Store.put('atom', ['e']);
      const fact = Store.put('code', [e, e]);
      const results = [];
      const len = flattenFact(fact);
      queryFlat(root, len, results);
      assert.strictEqual(results.length, 1);
    });
  });

  describe('collectAll', () => {
    it('collects rules from entire subtree', () => {
      const root = createNode();
      const e = Store.put('atom', ['e']);
      const mv = Store.put('freevar', ['_X']);

      // Insert two rules at different depths
      const p1 = Store.put('code', [e, e]);
      const r1 = { name: 'r1' };
      insert(root, p1, r1);

      const p2 = Store.put('code', [mv, e]);
      const r2 = { name: 'r2' };
      insert(root, p2, r2);

      const results = [];
      collectAll(root, results);
      assert.strictEqual(results.length, 2);
    });
  });

  describe('makeDiscTreeLayer', () => {
    it('claims all rules', () => {
      const layer = makeDiscTreeLayer();
      assert.strictEqual(layer.claims({}), true);
      assert.strictEqual(layer.claims({ discriminator: { pred: 'code' } }), true);
    });

    it('builds and queries correctly', () => {
      const e = Store.put('atom', ['e']);
      const mv = Store.put('freevar', ['_X']);
      const pattern = Store.put('code', [mv, e]);
      const rule = {
        name: 'test',
        antecedent: { linear: [pattern] },
        triggerPreds: ['code']
      };

      const layer = makeDiscTreeLayer();
      const built = layer.build([rule]);

      const fact = Store.put('code', [e, e]);
      const stateIndex = { code: [fact] };
      const candidates = built.getCandidateRules({}, stateIndex);
      assert.strictEqual(candidates.length, 1);
      assert.strictEqual(candidates[0], rule);
    });

    it('filters by trigger predicates', () => {
      const e = Store.put('atom', ['e']);
      const mv = Store.put('freevar', ['_X']);
      const pattern = Store.put('code', [mv, e]);
      const rule = {
        name: 'test',
        antecedent: { linear: [pattern] },
        triggerPreds: ['code', 'pc']  // needs both code AND pc
      };

      const layer = makeDiscTreeLayer();
      const built = layer.build([rule]);

      // Only code in state, no pc → filtered out
      const fact = Store.put('code', [e, e]);
      const stateIndex = { code: [fact] };
      const candidates = built.getCandidateRules({}, stateIndex);
      assert.strictEqual(candidates.length, 0);

      // Both present → included
      const pcFact = Store.put('pc', [e]);
      stateIndex.pc = [pcFact];
      const candidates2 = built.getCandidateRules({}, stateIndex);
      assert.strictEqual(candidates2.length, 1);
    });

    it('deduplicates results from multiple facts', () => {
      const e = Store.put('atom', ['e']);
      const mv = Store.put('freevar', ['_X']);
      const pattern = Store.put('code', [mv, e]);
      const rule = {
        name: 'test',
        antecedent: { linear: [pattern] },
        triggerPreds: ['code']
      };

      const layer = makeDiscTreeLayer();
      const built = layer.build([rule]);

      // Two different code facts — rule should appear only once
      const fact1 = Store.put('code', [e, e]);
      const i_e = Store.put('i', [e]);
      const fact2 = Store.put('code', [i_e, e]);
      const stateIndex = { code: [fact1, fact2] };
      const candidates = built.getCandidateRules({}, stateIndex);
      assert.strictEqual(candidates.length, 1);
    });
  });

  describe('integration with explore', { timeout: 15000 }, () => {
    it('produces same tree as predicate layer (EVM multisig)', async () => {
      Store.clear();
      const fs = require('fs');
      const calc = await mde.load([
        path.join(__dirname, '../../calculus/ill/programs/bin.ill'),
        path.join(__dirname, '../../calculus/ill/programs/evm.ill'),
        path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'),
      ]);

      // Set up state same as benchmark
      const state = { linear: {}, persistent: {} };
      for (const f of ['pc N_75', 'sh ee', 'gas N_ffff', 'caller sender_addr', 'sender member01']) {
        state.linear[await mde.parseExpr(f)] = 1;
      }
      const codeFile = fs.readFileSync(
        path.join(__dirname, '../../calculus/ill/programs/multisig_code.ill'), 'utf8'
      );
      for (const line of codeFile.split('\n')) {
        const trimmed = line.split('%')[0].trim();
        if (!trimmed || !trimmed.startsWith('code')) continue;
        const parts = trimmed.replace(/\*.*$/, '').trim();
        if (parts) state.linear[await mde.parseExpr(parts)] = 1;
      }

      // disc-tree strategy (default via detectStrategy)
      const tree = explore(state, calc.forwardRules, {
        maxDepth: 200,
        calc: { clauses: calc.clauses, types: calc.types }
      });

      assert.strictEqual(countNodes(tree), 63);
      assert.strictEqual(countLeaves(tree), 7);
      assert.strictEqual(maxDepth(tree), 38);
      const leaves = getAllLeaves(tree);
      assert(leaves.every(l => l.type === 'leaf'));
    });
  });
});
