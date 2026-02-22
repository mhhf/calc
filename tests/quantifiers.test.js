/**
 * Integration tests for ∃/∀ quantifiers — Store, parser, prover, forward engine.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const Store = require('../lib/kernel/store');
const { debruijnSubst } = require('../lib/kernel/substitute');
const { freshEvar, resetFresh } = require('../lib/kernel/fresh');
const calculus = require('../lib/calculus');
const { createProver, buildRuleSpecs } = require('../lib/prover/focused');
const Seq = require('../lib/kernel/sequent');
const { parseExpr } = require('../lib/engine/convert');
const { compileRule, expandItem } = require('../lib/engine/compile');
const { resolveExistentials } = require('../lib/engine/forward');

describe('Quantifier Store operations', () => {
  it('exists(body) creates arity-1 node', () => {
    const p = Store.put('atom', ['p']);
    const ex = Store.put('exists', [p]);
    assert.strictEqual(Store.tag(ex), 'exists');
    assert.strictEqual(Store.arity(ex), 1);
    assert.strictEqual(Store.child(ex, 0), p);
  });

  it('forall(body) creates arity-1 node', () => {
    const p = Store.put('atom', ['p']);
    const fa = Store.put('forall', [p]);
    assert.strictEqual(Store.tag(fa), 'forall');
    assert.strictEqual(Store.child(fa, 0), p);
  });

  it('bound(N) uses BigInt children', () => {
    const b0 = Store.put('bound', [0n]);
    assert.strictEqual(Store.tag(b0), 'bound');
    assert.strictEqual(Store.child(b0, 0), 0n);
  });

  it('evar(N) uses BigInt children', () => {
    const e = Store.put('evar', [99n]);
    assert.strictEqual(Store.tag(e), 'evar');
    assert.strictEqual(Store.child(e, 0), 99n);
  });

  it('alpha-equivalence via content addressing', () => {
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const ex1 = Store.put('exists', [pb]);
    const ex2 = Store.put('exists', [pb]);
    assert.strictEqual(ex1, ex2);
  });
});

describe('debruijnSubst', () => {
  it('replaces bound(0) with replacement', () => {
    const b0 = Store.put('bound', [0n]);
    const a = Store.put('atom', ['a']);
    const body = Store.put('p', [b0]);
    const result = debruijnSubst(body, 0n, a);
    assert.strictEqual(result, Store.put('p', [a]));
  });

  it('respects binder depth (nested exists)', () => {
    const b0 = Store.put('bound', [0n]);
    const b1 = Store.put('bound', [1n]);
    const inner = Store.put('p', [b0, b1]);
    const body = Store.put('exists', [inner]);
    const a = Store.put('atom', ['a']);
    const result = debruijnSubst(body, 0n, a);
    // b0 inside exists refers to the inner binder → stays
    // b1 inside exists matches outer depth → replaced
    const expectedInner = Store.put('p', [b0, a]);
    assert.strictEqual(result, Store.put('exists', [expectedInner]));
  });

  it('locally nameless: replacement is not captured', () => {
    const b0 = Store.put('bound', [0n]);
    const q = Store.put('atom', ['q']);
    const replacement = Store.put('app', [q, b0]); // q(bound(0))
    const body = Store.put('p', [b0]);
    const result = debruijnSubst(body, 0n, replacement);
    // Result: p(q(bound(0))) — the bound(0) in replacement is NOT shifted
    assert.strictEqual(result, Store.put('p', [replacement]));
  });
});

describe('Quantifier parsing', () => {
  it('parses exists X. p X', async () => {
    const h = await parseExpr('exists X. p X');
    assert.strictEqual(Store.tag(h), 'exists');
    const body = Store.child(h, 0);
    assert.strictEqual(Store.tag(body), 'p');
    const arg = Store.child(body, 0);
    assert.strictEqual(Store.tag(arg), 'bound');
    assert.strictEqual(Store.child(arg, 0), 0n);
  });

  it('parses forall Y. exists X. p X Y with correct de Bruijn', async () => {
    const h = await parseExpr('forall Y. exists X. p X Y');
    assert.strictEqual(Store.tag(h), 'forall');
    const forallBody = Store.child(h, 0);
    assert.strictEqual(Store.tag(forallBody), 'exists');
    const existsBody = Store.child(forallBody, 0);
    const argX = Store.child(existsBody, 0); // bound(0) — inner
    const argY = Store.child(existsBody, 1); // bound(1) — outer
    assert.strictEqual(Store.child(argX, 0), 0n);
    assert.strictEqual(Store.child(argY, 0), 1n);
  });

  it('binder scopes over tensor: exists X. a * b', async () => {
    const h = await parseExpr('exists X. a * b');
    assert.strictEqual(Store.tag(h), 'exists');
    const body = Store.child(h, 0);
    assert.strictEqual(Store.tag(body), 'tensor');
  });
});

describe('Backward prover with quantifiers', () => {
  let calc, prover, specs, alternatives;

  before(async () => {
    resetFresh();
    calc = await calculus.loadILL();
    prover = createProver(calc);
    const built = buildRuleSpecs(calc);
    specs = built.specs;
    alternatives = built.alternatives;
  });

  it('identity: exists X. p(X) |- exists X. p(X)', () => {
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const ex = Store.put('exists', [pb]);
    const seq = Seq.fromArrays([ex], [], ex);
    const result = prover.prove(seq, { rules: specs, alternatives });
    assert.strictEqual(result.success, true);
  });

  it('exists introduction: p(a) |- exists X. p(X)', () => {
    const a = Store.put('atom', ['a']);
    const pa = Store.put('p', [a]);
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const ex = Store.put('exists', [pb]);
    const seq = Seq.fromArrays([pa], [], ex);
    const result = prover.prove(seq, { rules: specs, alternatives });
    assert.strictEqual(result.success, true);
    assert.strictEqual(result.proofTree.rule, 'exists_r');
  });

  it('forall elimination: forall X. p(X) |- exists X. p(X)', () => {
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const fa = Store.put('forall', [pb]);
    const ex = Store.put('exists', [pb]);
    const seq = Seq.fromArrays([fa], [], ex);
    const result = prover.prove(seq, { rules: specs, alternatives });
    assert.strictEqual(result.success, true);
  });

  it('invertibility: exists_l is invertible (positive left)', () => {
    const { createGenericProver } = require('../lib/prover/generic');
    const gen = createGenericProver(calc);
    assert.strictEqual(gen.ruleIsInvertible('exists', 'l'), true);
    assert.strictEqual(gen.ruleIsInvertible('exists', 'r'), false);
  });

  it('invertibility: forall_r is invertible (negative right)', () => {
    const { createGenericProver } = require('../lib/prover/generic');
    const gen = createGenericProver(calc);
    assert.strictEqual(gen.ruleIsInvertible('forall', 'r'), true);
    assert.strictEqual(gen.ruleIsInvertible('forall', 'l'), false);
  });
});

describe('Forward engine with exists', () => {
  it('expandItem opens exists binder', () => {
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const ex = Store.put('exists', [pb]);

    const alts = expandItem(ex);
    assert.strictEqual(alts.length, 1);
    // Body should have a freevar (metavar) instead of bound(0)
    const linearFact = alts[0].linear[0];
    assert.strictEqual(Store.tag(linearFact), 'p');
    const arg = Store.child(linearFact, 0);
    assert.strictEqual(Store.tag(arg), 'freevar');
  });

  it('expandItem handles exists inside tensor', () => {
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const ex = Store.put('exists', [pb]);
    const q = Store.put('atom', ['q']);
    const tensor = Store.put('tensor', [ex, q]);

    const alts = expandItem(tensor);
    assert.strictEqual(alts.length, 1);
    assert.strictEqual(alts[0].linear.length, 2);
  });

  it('compileRule detects existential slots in consequent', () => {
    // Create a simple rule: a -o { exists X. p(X) }
    const a = Store.put('atom', ['a']);
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const ex = Store.put('exists', [pb]);
    const monad = Store.put('monad', [ex]);
    const loli = Store.put('loli', [a, monad]);

    const rule = { name: 'test', hash: loli, antecedent: a, consequent: monad };
    const compiled = compileRule(rule);

    assert.ok(compiled.existentialSlots.length > 0, 'should have existential slots');
  });
});

describe('Polarity', () => {
  let calc;

  before(async () => {
    calc = await calculus.loadILL();
  });

  it('exists is positive', () => {
    assert.strictEqual(calc.isPositive('exists'), true);
    assert.strictEqual(calc.isNegative('exists'), false);
  });

  it('forall is negative', () => {
    assert.strictEqual(calc.isPositive('forall'), false);
    assert.strictEqual(calc.isNegative('forall'), true);
  });
});
