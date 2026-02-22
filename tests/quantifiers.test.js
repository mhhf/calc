/**
 * Integration tests for ∃/∀ quantifiers — Store, parser, prover, forward engine.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const Store = require('../lib/kernel/store');
const { debruijnSubst } = require('../lib/kernel/substitute');
const { freshEvar, resetFresh, getFreshCounter, resetMetavar } = require('../lib/kernel/fresh');
const calculus = require('../lib/calculus');
const { createProver, buildRuleSpecs } = require('../lib/prover/focused');
const Seq = require('../lib/kernel/sequent');
const { parseExpr } = require('../lib/engine/convert');
const { compileRule, expandItem } = require('../lib/engine/compile');
const { resolveExistentials, tryMatch, createState } = require('../lib/engine/forward');

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

  it('no-change: bound(1) untouched at index=0', () => {
    const p = Store.put('atom', ['p']);
    const b1 = Store.put('bound', [1n]);
    const body = Store.put('app', [p, b1]);
    const a = Store.put('atom', ['a']);
    const result = debruijnSubst(body, 0n, a);
    assert.strictEqual(result, body);
  });

  it('nested forall binder', () => {
    const p = Store.put('atom', ['p']);
    const b0 = Store.put('bound', [0n]);
    const b1 = Store.put('bound', [1n]);
    const inner = Store.put('app', [p, b0, b1]);
    const body = Store.put('forall', [inner]);
    const a = Store.put('atom', ['a']);
    const result = debruijnSubst(body, 0n, a);
    const expectedInner = Store.put('app', [p, b0, a]);
    const expected = Store.put('forall', [expectedInner]);
    assert.strictEqual(result, expected);
  });
});

describe('freshEvar', () => {
  it('monotonic counter', () => {
    resetFresh(10n);
    assert.strictEqual(getFreshCounter(), 10n);
    const e1 = freshEvar();
    const e2 = freshEvar();
    assert.strictEqual(Store.child(e1, 0), 10n);
    assert.strictEqual(Store.child(e2, 0), 11n);
    assert.strictEqual(getFreshCounter(), 12n);
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

describe('Loli variables are NOT existential slots', () => {
  it('compileRule excludes loli-trigger variables from existentialSlots', () => {
    // Simulate sha3-like rule: a -o { b * (c Z -o { d Z }) }
    // Z only appears in the loli — it should NOT be an existential slot.
    const z = Store.put('freevar', ['_Z']);
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);
    const cz = Store.put('c', [z]);
    const dz = Store.put('d', [z]);
    const monadBody = Store.put('monad', [dz]);
    const loli = Store.put('loli', [cz, monadBody]);
    const body = Store.put('tensor', [b, loli]);
    const monad = Store.put('monad', [body]);

    const rule = { name: 'test_loli', hash: Store.put('loli', [a, monad]), antecedent: a, consequent: monad };
    const compiled = compileRule(rule);

    // Z should NOT be in existentialSlots — it's a loli pattern variable
    assert.strictEqual(compiled.existentialSlots.length, 0,
      'loli-only variable Z should not be treated as existential');
  });

  it('mixed: exists X in body + Z in loli → only X is existential', () => {
    // a -o { exists X. (p X * (q Z -o { r Z })) }
    const x = Store.put('freevar', ['_ex0']);
    const z = Store.put('freevar', ['_Z']);
    const a = Store.put('atom', ['a']);
    const px = Store.put('p', [x]);
    const qz = Store.put('q', [z]);
    const rz = Store.put('r', [z]);
    const loliBody = Store.put('monad', [rz]);
    const loli = Store.put('loli', [qz, loliBody]);
    const tensor = Store.put('tensor', [px, loli]);
    // exists wraps the tensor — after expandItem, X becomes a fresh metavar
    const ex = Store.put('exists', [tensor]);
    const monad = Store.put('monad', [ex]);

    const rule = { name: 'test_mixed', hash: Store.put('loli', [a, monad]), antecedent: a, consequent: monad };
    const compiled = compileRule(rule);

    // Should have exactly 1 existential slot (for the exists-opened X), not 2
    assert.strictEqual(compiled.existentialSlots.length, 1,
      'only exists-opened var should be existential, not loli var Z');
  });
});

describe('resolveExistentials three-level fallback', () => {
  it('always returns true (exists never blocks)', () => {
    // Rule with existential slot but no goals — gets freshEvar
    resetFresh();
    const a = Store.put('atom', ['a']);
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const ex = Store.put('exists', [pb]);
    const monad = Store.put('monad', [ex]);

    resetMetavar();
    const rule = { name: 'test', hash: Store.put('loli', [a, monad]), antecedent: a, consequent: monad };
    const compiled = compileRule(rule);

    const theta = new Array(compiled.metavarCount);
    const state = createState();
    const result = resolveExistentials(theta, compiled.metavarSlots, compiled, state, null);

    assert.strictEqual(result, true, 'resolveExistentials always returns true');
    // The existential slot should be bound to a freshEvar
    const slot = compiled.existentialSlots[0];
    assert.notStrictEqual(theta[slot], undefined, 'existential slot should be bound');
    assert.strictEqual(Store.tag(theta[slot]), 'evar', 'unresolvable slot gets freshEvar');
  });

  it('resolves via FFI when inputs are ground', async () => {
    // Rule: a X Y -o { exists Z. (b Z * !plus X Y Z) }
    // After matching a(3,4): X=3, Y=4 → FFI resolves Z=7
    const { parseExpr } = require('../lib/engine/convert');
    resetMetavar();
    const ruleH = await parseExpr('a X Y -o { exists Z. (b Z * !plus X Y Z) }');
    const [ante, conseq] = Store.children(ruleH);
    const compiled = compileRule({ name: 'test_ffi', hash: ruleH, antecedent: ante, consequent: conseq });

    assert.ok(compiled.existentialSlots.length > 0, 'should have existential slots');

    // Build state with a(3, 4)
    const three = Store.put('binlit', [3n]);
    const four = Store.put('binlit', [4n]);
    const aFact = Store.put('a', [three, four]);
    const state = createState({ [aFact]: 1 }, {});

    const match = tryMatch(compiled, state, null);
    assert.notStrictEqual(match, null, 'tryMatch should succeed');

    // Check that the existential slot was resolved to 7
    const seven = Store.put('binlit', [7n]);
    let foundSeven = false;
    for (const slot of compiled.existentialSlots) {
      if (match.theta[slot] === seven) foundSeven = true;
    }
    assert.ok(foundSeven, 'existential Z should be resolved to 7 via FFI');
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
