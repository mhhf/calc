/**
 * Tests for Curry-Howard proof terms (TODO_0068)
 *
 * Phase 1: Generic term signatures match the §2.7 catalog.
 * Phase 2: Backward term extraction from proof trees.
 * Phase 3: Forward term builders (rightFocusTerm, monadicTerm, exploreTerm).
 * Phase 4: Type checker (expand, round-trip, invalid terms).
 * Phase 5: Bridge integration (monad_r term construction, kernel verification).
 * Phase 6: End-to-end bridge term construction, zero-overhead.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const calculus = require('../lib/calculus');
const { sigMap, formatSignature, flattenedArity, extractTerm,
        monadicTerm, exploreTerm } = require('../lib/prover/generic-term');
const { createProver } = require('../lib/prover/focused');
const { buildRuleSpecs } = require('../lib/prover/rule-interpreter');
const { rightFocusTerm, modeSwitch } = require('../lib/prover/bridge');
const { compileRule } = require('../lib/engine/compile');
const { ILL_CONNECTIVES } = require('../lib/engine/ill/connectives');
const { createChecker, expand } = require('../lib/prover/check-term');
const { createKernel } = require('../lib/prover/kernel');
const Seq = require('../lib/kernel/sequent');
const Store = require('../lib/kernel/store');
const { GRADE_W } = require('../lib/engine/grades');

describe('Generic Term Signatures', () => {
  let calc, sigs;

  before(async () => {
    calc = await calculus.loadILL();
    sigs = sigMap(calc.rules);
  });

  // Expected catalog from TODO_0068 §2.7
  const expected = {
    id:          { notation: 'id(x)',                               arity: 1 },
    tensor_r:    { notation: 'tensor_r(u0, u1)',                    arity: 2 },
    tensor_l:    { notation: 'tensor_l(z, x0 x1 -> u0)',           arity: 2 },
    one_r:       { notation: 'one_r()',                             arity: 0 },
    one_l:       { notation: 'one_l(z, u0)',                        arity: 2 },
    loli_r:      { notation: 'loli_r(x0 -> u0)',                   arity: 1 },
    loli_l:      { notation: 'loli_l(z, u0, x1 -> u1)',            arity: 3 },
    with_r:      { notation: 'with_r(u0, u1)',                      arity: 2 },
    with_l1:     { notation: 'with_l1(z, x0 -> u0)',               arity: 2 },
    with_l2:     { notation: 'with_l2(z, x1 -> u0)',               arity: 2 },
    oplus_r1:    { notation: 'oplus_r1(u0)',                        arity: 1 },
    oplus_r2:    { notation: 'oplus_r2(u0)',                        arity: 1 },
    oplus_l:     { notation: 'oplus_l(z, x0 -> u0, x1 -> u1)',     arity: 3 },
    zero_l:      { notation: 'zero_l(z)',                           arity: 1 },
    promotion:   { notation: 'promotion(u0)',                       arity: 1 },
    absorption:  { notation: 'absorption(z, y1 -> u0)',             arity: 2 },
    dereliction: { notation: 'dereliction(z, x1 -> u0)',           arity: 2 },
    copy:        { notation: 'copy(u, x0 -> u0)',                   arity: 2 },
    monad_r:     { notation: 'monad_r()',                           arity: 0 },
    monad_l:     { notation: 'monad_l(z, x0 -> u0)',               arity: 2 },
    exists_r:    { notation: 'exists_r(s, u0)',                     arity: 2 },
    exists_l:    { notation: 'exists_l(z, a, x0 -> u0)',           arity: 3 },
    forall_r:    { notation: 'forall_r(a, u0)',                     arity: 2 },
    forall_l:    { notation: 'forall_l(z, s, x0 -> u0)',           arity: 3 },
  };

  it('produces signatures for all ILL rules', () => {
    for (const name of Object.keys(expected)) {
      assert.ok(sigs[name], `missing signature for ${name}`);
    }
  });

  it('all rule names in calculus.rules have signatures', () => {
    for (const name of Object.keys(calc.rules)) {
      assert.ok(sigs[name], `missing signature for rule ${name}`);
    }
  });

  for (const [name, exp] of Object.entries(expected)) {
    it(`${name}: notation matches`, () => {
      const sig = sigs[name];
      assert.ok(sig, `missing signature for ${name}`);
      assert.strictEqual(formatSignature(sig), exp.notation);
    });

    it(`${name}: flattened arity = ${exp.arity}`, () => {
      const sig = sigs[name];
      assert.ok(sig, `missing signature for ${name}`);
      assert.strictEqual(flattenedArity(sig), exp.arity);
    });
  }
});

// =============================================================================
// Phase 2: Backward Term Extraction
// =============================================================================

describe('Backward Term Extraction', () => {
  let calc, AST, prover, ruleSpecs, alternatives;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    const built = buildRuleSpecs(calc);
    ruleSpecs = built.specs;
    alternatives = built.alternatives;
    prover = createProver(calc);
  });

  const seq = (linear, succ) => {
    const linearFormulas = linear.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const succFormula = typeof succ === 'string' ? calc.parse(succ) : succ;
    return Seq.fromArrays(linearFormulas, [], succFormula);
  };

  const seqCart = (linear, cart, succ) => {
    const lf = linear.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const cf = cart.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const sf = typeof succ === 'string' ? calc.parse(succ) : succ;
    return Seq.fromArrays(lf, cf, sf);
  };

  function proveAndExtract(s) {
    const result = prover.prove(s, { rules: ruleSpecs, alternatives });
    assert.strictEqual(result.success, true, 'proof should succeed');
    const term = extractTerm(result.proofTree, calc);
    assert.ok(term, 'term extraction should succeed');
    return term;
  }

  // --- Identity ---

  it('A ⊢ A → id(A)', () => {
    const A = AST.freevar('A');
    const term = proveAndExtract(seq([A], A));
    assert.strictEqual(term.rule, 'id');
    assert.strictEqual(term.principal, A);
    assert.strictEqual(term.subterms.length, 0);
  });

  // --- Tensor ---

  it('A, B ⊢ A * B → tensor_r(id, id)', () => {
    const A = AST.freevar('A');
    const B = AST.freevar('B');
    const term = proveAndExtract(seq([A, B], AST.tensor(A, B)));
    assert.strictEqual(term.rule, 'tensor_r');
    assert.strictEqual(term.subterms.length, 2);
    assert.strictEqual(term.subterms[0].rule, 'id');
    assert.strictEqual(term.subterms[1].rule, 'id');
  });

  it('A * B ⊢ B * A → tensor_l(_, tensor_r(id, id))', () => {
    const A = AST.freevar('A');
    const B = AST.freevar('B');
    const term = proveAndExtract(seq([AST.tensor(A, B)], AST.tensor(B, A)));
    assert.strictEqual(term.rule, 'tensor_l');
    assert.ok(term.principal, 'should have principal');
    assert.strictEqual(term.subterms.length, 1);
    assert.strictEqual(term.subterms[0].rule, 'tensor_r');
  });

  // --- Linear Implication ---

  it('A ⊢ B -o (A * B) → loli_r(...)', () => {
    const A = AST.freevar('A');
    const B = AST.freevar('B');
    const term = proveAndExtract(seq([A], AST.loli(B, AST.tensor(A, B))));
    assert.strictEqual(term.rule, 'loli_r');
    assert.strictEqual(term.subterms.length, 1);
    // Body is tensor_r
    assert.strictEqual(term.subterms[0].rule, 'tensor_r');
  });

  it('P, P -o Q ⊢ Q → loli_l(_, id, id)', () => {
    const P = AST.freevar('P');
    const Q = AST.freevar('Q');
    const term = proveAndExtract(seq([P, AST.loli(P, Q)], Q));
    assert.strictEqual(term.rule, 'loli_l');
    assert.ok(term.principal, 'should have principal (loli formula)');
    assert.strictEqual(term.subterms.length, 2);
  });

  // --- Additive Conjunction (With) ---

  it('A ⊢ A & A → with_r(id, id)', () => {
    const A = AST.freevar('A');
    const term = proveAndExtract(seq([A], AST.with(A, A)));
    assert.strictEqual(term.rule, 'with_r');
    assert.strictEqual(term.subterms.length, 2);
    assert.strictEqual(term.subterms[0].rule, 'id');
    assert.strictEqual(term.subterms[1].rule, 'id');
  });

  it('A & B ⊢ A → with_l1(..., id)', () => {
    const A = AST.freevar('A');
    const B = AST.freevar('B');
    const term = proveAndExtract(seq([AST.with(A, B)], A));
    assert.ok(term.rule === 'with_l1' || term.rule === 'with_l2');
    assert.ok(term.principal, 'should have principal');
    assert.strictEqual(term.subterms.length, 1);
  });

  // --- Additive Disjunction (Oplus) ---

  it('A ⊢ A + B → oplus_r1(id)', () => {
    const A = AST.freevar('A');
    const B = AST.freevar('B');
    const term = proveAndExtract(seq([A], AST.oplus(A, B)));
    assert.strictEqual(term.rule, 'oplus_r1');
    assert.strictEqual(term.subterms.length, 1);
    assert.strictEqual(term.subterms[0].rule, 'id');
  });

  // --- One ---

  it('⊢ I → one_r()', () => {
    const term = proveAndExtract(seq([], AST.one()));
    assert.strictEqual(term.rule, 'one_r');
    assert.strictEqual(term.subterms.length, 0);
  });

  it('I ⊢ I → one_l(_, one_r)', () => {
    const term = proveAndExtract(seq([AST.one()], AST.one()));
    // Could be id or one_l then one_r — depends on prover strategy
    assert.ok(term.rule === 'id' || term.rule === 'one_l');
  });

  // --- Zero ---

  it('zero ⊢ C → zero_l(_)', () => {
    const C = AST.freevar('C');
    const term = proveAndExtract(seq([AST.zero()], C));
    assert.strictEqual(term.rule, 'zero_l');
    assert.ok(term.principal, 'should have principal');
    assert.strictEqual(term.subterms.length, 0);
  });

  // --- Bang ---

  it('!A ⊢ A → bang_l(_, id)', () => {
    const A = AST.freevar('A');
    const term = proveAndExtract(seq([AST.bang(GRADE_W,A)], A));
    // Prover uses spec key bang_l (= absorption, the primary !L rule)
    assert.ok(term.rule === 'bang_l' || term.rule === 'dereliction' || term.rule === 'absorption',
      `expected bang_l/dereliction/absorption, got ${term.rule}`);
    assert.ok(term.principal, 'should have principal');
    assert.strictEqual(term.subterms.length, 1);
  });

  // --- Copy ---

  it('; A ⊢ A → copy(A, id)', () => {
    const A = AST.freevar('A');
    const term = proveAndExtract(seqCart([], [A], A));
    assert.strictEqual(term.rule, 'copy');
    assert.ok(term.principal, 'should have principal from cartesian');
    assert.strictEqual(term.subterms.length, 1);
    assert.strictEqual(term.subterms[0].rule, 'id');
  });

  // --- Structure: nested terms ---

  it('(A * B) -o C, A, B ⊢ C → nested term', () => {
    const A = AST.freevar('A');
    const B = AST.freevar('B');
    const C = AST.freevar('C');
    const term = proveAndExtract(seq([AST.loli(AST.tensor(A, B), C), A, B], C));
    // Should use loli_l: provide tensor_r(id,id) as argument, id as continuation
    assert.strictEqual(term.rule, 'loli_l');
    assert.strictEqual(term.subterms.length, 2);
    // First sub-proof should produce A * B
    assert.strictEqual(term.subterms[0].rule, 'tensor_r');
  });

  // --- Quantifier extraction ---

  it('p(a) ⊢ ∃X. p(X) → exists_r(witness, subproof)', () => {
    const a = Store.put('atom', ['a']);
    const pa = Store.put('p', [a]);
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const ex = Store.put('exists', [pb]);
    const s = Seq.fromArrays([pa], [], ex);
    const term = proveAndExtract(s);
    assert.strictEqual(term.rule, 'exists_r');
    assert.ok(term.witness != null, 'should have a witness');
    assert.strictEqual(term.subterms.length, 1);
  });

  it('exists_l extraction from proof tree', () => {
    // Manual proof tree: ∃X.p(X) ⊢ ∃X.p(X)
    // exists_l opens ∃X.p(X) on left with eigenvariable c
    // Succedent stays ∃X.p(X) (doesn't contain eigenvariable)
    const { ProofTree } = require('../lib/prover/pt');
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const ex = Store.put('exists', [pb]);
    const evar = Store.put('evar', [99n]); // fresh eigenvariable
    const pe = Store.put('p', [evar]);

    // Leaf: p(c) ⊢ p(c) — id after exists_r instantiates the right ∃
    const leaf = new ProofTree({
      conclusion: Seq.fromArrays([pe], [], pe),
      rule: 'id', proven: true, premises: []
    });
    // exists_l: ∃X.p(X) ⊢ ∃X.p(X)  →  p(c) ⊢ ∃X.p(X)
    // (succedent is the original ∃X.p(X), not pe)
    const existsR = new ProofTree({
      conclusion: Seq.fromArrays([pe], [], ex),
      rule: 'exists_r', proven: true, premises: [leaf]
    });
    const tree = new ProofTree({
      conclusion: Seq.fromArrays([ex], [], ex),
      rule: 'exists_l', proven: true, premises: [existsR]
    });
    const term = extractTerm(tree, calc);
    assert.ok(term);
    assert.strictEqual(term.rule, 'exists_l');
    assert.ok(term.principal != null, 'should have principal');
    assert.ok(term.eigenvariable != null, 'should have eigenvariable');
    assert.strictEqual(term.eigenvariable, evar);
    assert.strictEqual(term.subterms.length, 1);
    assert.strictEqual(term.subterms[0].rule, 'exists_r');
  });

  it('∀X. p(X) ⊢ ∃X. p(X) → forall_l then exists_r', () => {
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const fa = Store.put('forall', [pb]);
    const ex = Store.put('exists', [pb]);
    const s = Seq.fromArrays([fa], [], ex);
    const term = proveAndExtract(s);
    assert.strictEqual(term.rule, 'forall_l');
    assert.ok(term.principal != null, 'should have principal');
    assert.ok(term.witness != null, 'should have witness');
    assert.strictEqual(term.subterms.length, 1);
  });

  it('identity via unification: ∀X.p(X) ⊢ p(a) → metavar resolved in id leaf', () => {
    // After forall_l, identity fires via unify(p(_X), p(a)).
    // The prover resolves metavars in identity leaves, so p(_X) becomes p(a).
    // Principal === succedent via O(1) hash equality.
    const b0 = Store.put('bound', [0n]);
    const pb = Store.put('p', [b0]);
    const fa = Store.put('forall', [pb]);
    const a = Store.put('atom', ['a']);
    const pa = Store.put('p', [a]);

    const s = Seq.fromArrays([fa], [], pa);
    const term = proveAndExtract(s);
    assert.strictEqual(term.rule, 'forall_l');
    const idTerm = term.subterms[0];
    assert.strictEqual(idTerm.rule, 'id');
    // After theta resolution, principal IS p(a) — hash equality works
    assert.strictEqual(idTerm.principal, pa, 'principal should be p(a) after resolution');
  });

  it('⊢ ∀X. (X -o X) → forall_r(eigenvariable, loli_r(id))', () => {
    // Body uses bound variable, so forall_r introduces a detectable eigenvariable
    const b0 = Store.put('bound', [0n]);
    const body = AST.loli(b0, b0); // X -o X
    const fa = Store.put('forall', [body]);
    const s = Seq.fromArrays([], [], fa);
    const term = proveAndExtract(s);
    assert.strictEqual(term.rule, 'forall_r');
    assert.ok(term.eigenvariable != null, 'should have eigenvariable');
    assert.strictEqual(term.subterms.length, 1);
    // Inner proof: loli_r wrapping id (λx.x)
    assert.strictEqual(term.subterms[0].rule, 'loli_r');
  });

  // --- Null safety ---

  it('returns null for unproven tree', () => {
    const { fromGoal } = require('../lib/prover/pt');
    const A = AST.freevar('A');
    const tree = fromGoal(seq([A], AST.freevar('B')));
    const term = extractTerm(tree, calc);
    assert.strictEqual(term, null);
  });

  it('returns null for null input', () => {
    assert.strictEqual(extractTerm(null, calc), null);
  });
});

// =============================================================================
// Phase 3: Forward Term Builders
// =============================================================================

describe('Forward Term Builders', () => {
  let calc, AST, roles;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    roles = calc.roles;
  });

  describe('rightFocusTerm', () => {
    it('atom: id(x) consuming from linear', () => {
      const p = AST.atom('p');
      const result = rightFocusTerm({ [p]: 1 }, {}, p, roles);
      assert.ok(result, 'should succeed');
      assert.strictEqual(result.term.rule, 'id');
      assert.strictEqual(result.term.principal, p);
      assert.deepStrictEqual(result.remaining, {});
    });

    it('tensor: tensor_r(id, id)', () => {
      const p = AST.atom('p');
      const q = AST.atom('q');
      const pq = AST.tensor(p, q);
      const result = rightFocusTerm({ [p]: 1, [q]: 1 }, {}, pq, roles);
      assert.ok(result, 'should succeed');
      assert.strictEqual(result.term.rule, 'tensor_r');
      assert.strictEqual(result.term.subterms.length, 2);
      assert.strictEqual(result.term.subterms[0].rule, 'id');
      assert.strictEqual(result.term.subterms[0].principal, p);
      assert.strictEqual(result.term.subterms[1].rule, 'id');
      assert.strictEqual(result.term.subterms[1].principal, q);
    });

    it('one: one_r() with empty linear', () => {
      const one = AST.one();
      const result = rightFocusTerm({}, {}, one, roles);
      assert.ok(result, 'should succeed');
      assert.strictEqual(result.term.rule, 'one_r');
    });

    it('one: fails with non-empty linear', () => {
      const one = AST.one();
      const p = AST.atom('p');
      const result = rightFocusTerm({ [p]: 1 }, {}, one, roles);
      assert.strictEqual(result, null);
    });

    it('bang: promotion(id(a)) from persistent', () => {
      const p = AST.atom('p');
      const bangP = AST.bang(GRADE_W,p);
      const result = rightFocusTerm({}, { [p]: 1 }, bangP, roles);
      assert.ok(result, 'should succeed');
      assert.strictEqual(result.term.rule, 'promotion');
      assert.strictEqual(result.term.subterms[0].rule, 'id');
      assert.strictEqual(result.term.subterms[0].principal, p);
    });

    it('nested: tensor(atom, bang(atom))', () => {
      const p = AST.atom('p');
      const q = AST.atom('q');
      const goal = AST.tensor(p, AST.bang(GRADE_W,q));
      const result = rightFocusTerm({ [p]: 1 }, { [q]: 1 }, goal, roles);
      assert.ok(result, 'should succeed');
      assert.strictEqual(result.term.rule, 'tensor_r');
      assert.strictEqual(result.term.subterms[0].rule, 'id');
      assert.strictEqual(result.term.subterms[1].rule, 'promotion');
    });

    it('fails for loli (async)', () => {
      const p = AST.atom('p');
      const q = AST.atom('q');
      const loli = AST.loli(p, q);
      const result = rightFocusTerm({ [p]: 1 }, {}, loli, roles);
      assert.strictEqual(result, null);
    });

    it('fails for missing resource', () => {
      const p = AST.atom('p');
      const result = rightFocusTerm({}, {}, p, roles);
      assert.strictEqual(result, null);
    });
  });

  describe('monadicTerm', () => {
    it('empty trace: returns rfTerm directly', () => {
      const rfTerm = { rule: 'one_r', principal: null, subterms: [] };
      const term = monadicTerm([], rfTerm);
      assert.deepStrictEqual(term, rfTerm);
    });

    it('single step: wraps rfTerm', () => {
      const rfTerm = { rule: 'id', principal: 42, subterms: [] };
      const trace = [{ rule: 'step1', consumed: { 10: 1 } }];
      const term = monadicTerm(trace, rfTerm);
      assert.strictEqual(term.rule, 'step1');
      assert.strictEqual(term.subterms.length, 1);
      assert.deepStrictEqual(term.subterms[0], rfTerm);
    });

    it('multi-step: nested chain', () => {
      const rfTerm = { rule: 'id', principal: 42, subterms: [] };
      const trace = [
        { rule: 'r1', consumed: { 1: 1 } },
        { rule: 'r2', consumed: { 2: 1 } },
        { rule: 'r3', consumed: { 3: 1 } }
      ];
      const term = monadicTerm(trace, rfTerm);
      // r1 -> r2 -> r3 -> rfTerm
      assert.strictEqual(term.rule, 'r1');
      assert.strictEqual(term.subterms[0].rule, 'r2');
      assert.strictEqual(term.subterms[0].subterms[0].rule, 'r3');
      assert.deepStrictEqual(term.subterms[0].subterms[0].subterms[0], rfTerm);
    });
  });

  describe('exploreTerm', () => {
    const mockRfFn = (state) => ({ rule: 'id', principal: 1, subterms: [] });

    it('leaf: produces rightFocus term', () => {
      const tree = { type: 'leaf', state: {} };
      const term = exploreTerm(tree, mockRfFn, {});
      assert.strictEqual(term.rule, 'id');
    });

    it('branch with single child: wraps child', () => {
      const tree = {
        type: 'branch', state: null,
        children: [{ rule: 'step1', child: { type: 'leaf', state: {} } }]
      };
      const term = exploreTerm(tree, mockRfFn, {});
      assert.strictEqual(term.rule, 'step1');
      assert.strictEqual(term.subterms[0].rule, 'id');
    });

    it('dead branch: unreachable', () => {
      const tree = { type: 'dead', state: null };
      const term = exploreTerm(tree, mockRfFn, {});
      assert.strictEqual(term.rule, 'unreachable');
    });

    it('bound/cycle/memo: returns null', () => {
      assert.strictEqual(exploreTerm({ type: 'bound', state: {} }, mockRfFn), null);
      assert.strictEqual(exploreTerm({ type: 'cycle', state: {} }, mockRfFn), null);
      assert.strictEqual(exploreTerm({ type: 'memo', state: {} }, mockRfFn), null);
    });

    it('oplus fork: oplus_l with case-split subterms', () => {
      const tree = {
        type: 'branch', state: null,
        children: [
          { rule: 'r1', choice: 0, child: { type: 'leaf', state: {} } },
          { rule: 'r1', choice: 1, child: { type: 'leaf', state: {} } }
        ]
      };
      const term = exploreTerm(tree, mockRfFn, {});
      assert.strictEqual(term.rule, 'oplus_l');
      assert.strictEqual(term.subterms.length, 2);
    });
  });
});

// =============================================================================
// Phase 4: Type Checker
// =============================================================================

describe('Type Checker', () => {
  let calc, AST, prover, ruleSpecs, alternatives, checker;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    const built = buildRuleSpecs(calc);
    ruleSpecs = built.specs;
    alternatives = built.alternatives;
    prover = createProver(calc);
    checker = createChecker(calc);
  });

  const seq = (linear, succ) => {
    const linearFormulas = linear.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const succFormula = typeof succ === 'string' ? calc.parse(succ) : succ;
    return Seq.fromArrays(linearFormulas, [], succFormula);
  };

  const seqCart = (linear, cart, succ) => {
    const lf = linear.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const cf = cart.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const sf = typeof succ === 'string' ? calc.parse(succ) : succ;
    return Seq.fromArrays(lf, cf, sf);
  };

  function proveExtractCheck(s) {
    const result = prover.prove(s, { rules: ruleSpecs, alternatives });
    assert.strictEqual(result.success, true, 'proof should succeed');
    const term = extractTerm(result.proofTree, calc);
    assert.ok(term, 'term extraction should succeed');
    const checkResult = checker.check(term, s);
    return { term, checkResult };
  }

  // --- expand ---

  describe('expand', () => {
    it('expands an atom', () => {
      const p = AST.atom('p');
      const e = expand(p);
      assert.ok(e);
      assert.strictEqual(e.tag, 'atom');
      assert.strictEqual(e.hash, p);
    });

    it('expands a compound type', () => {
      const p = AST.atom('p');
      const q = AST.atom('q');
      const t = AST.tensor(p, q);
      const e = expand(t);
      assert.strictEqual(e.tag, 'tensor');
      assert.strictEqual(e.children.length, 2);
      assert.strictEqual(e.children[0].hash, p);
      assert.strictEqual(e.children[1].hash, q);
    });

    it('returns null for non-terms', () => {
      assert.strictEqual(expand(0), null);
    });

    it('expands loli (arity 2)', () => {
      const p = AST.atom('p'), q = AST.atom('q');
      const e = expand(AST.loli(p, q));
      assert.strictEqual(e.tag, 'loli');
      assert.strictEqual(e.children.length, 2);
      assert.strictEqual(e.children[0].hash, p);
      assert.strictEqual(e.children[1].hash, q);
    });

    it('expands with (arity 2)', () => {
      const p = AST.atom('p'), q = AST.atom('q');
      const e = expand(AST.with(p, q));
      assert.strictEqual(e.tag, 'with');
      assert.strictEqual(e.children.length, 2);
    });

    it('expands oplus (arity 2)', () => {
      const p = AST.atom('p'), q = AST.atom('q');
      const e = expand(AST.oplus(p, q));
      assert.strictEqual(e.tag, 'oplus');
      assert.strictEqual(e.children.length, 2);
    });

    it('expands bang (arity 2: grade + formula)', () => {
      const p = AST.atom('p');
      const e = expand(AST.bang(GRADE_W,p));
      assert.strictEqual(e.tag, 'bang');
      assert.strictEqual(e.children.length, 2);
      assert.strictEqual(e.children[1].hash, p);
    });

    it('expands monad (arity 1)', () => {
      const p = AST.atom('p');
      const e = expand(AST.monad(p));
      assert.strictEqual(e.tag, 'monad');
      assert.strictEqual(e.children.length, 1);
      assert.strictEqual(e.children[0].hash, p);
    });

    it('expands nested structure recursively', () => {
      const p = AST.atom('p'), q = AST.atom('q');
      const e = expand(AST.bang(GRADE_W,AST.tensor(p, q)));
      assert.strictEqual(e.tag, 'bang');
      assert.strictEqual(e.children[1].tag, 'tensor');
      assert.strictEqual(e.children[1].children[0].hash, p);
    });
  });

  // --- Round-trip: prove → extract → check ---

  describe('round-trip (prove → extract → check)', () => {
    it('A ⊢ A (identity)', () => {
      const A = AST.freevar('A');
      const { checkResult } = proveExtractCheck(seq([A], A));
      assert.strictEqual(checkResult.valid, true);
    });

    it('A, B ⊢ A * B (tensor_r)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const { checkResult } = proveExtractCheck(seq([A, B], AST.tensor(A, B)));
      assert.strictEqual(checkResult.valid, true);
    });

    it('A * B ⊢ B * A (tensor_l + tensor_r)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const { checkResult } = proveExtractCheck(seq([AST.tensor(A, B)], AST.tensor(B, A)));
      assert.strictEqual(checkResult.valid, true);
    });

    it('⊢ I (one_r)', () => {
      const { checkResult } = proveExtractCheck(seq([], AST.one()));
      assert.strictEqual(checkResult.valid, true);
    });

    it('A ⊢ B -o (A * B) (loli_r)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const { checkResult } = proveExtractCheck(seq([A], AST.loli(B, AST.tensor(A, B))));
      assert.strictEqual(checkResult.valid, true);
    });

    it('P, P -o Q ⊢ Q (loli_l)', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const { checkResult } = proveExtractCheck(seq([P, AST.loli(P, Q)], Q));
      assert.strictEqual(checkResult.valid, true);
    });

    it('A ⊢ A & A (with_r)', () => {
      const A = AST.freevar('A');
      const { checkResult } = proveExtractCheck(seq([A], AST.with(A, A)));
      assert.strictEqual(checkResult.valid, true);
    });

    it('A & B ⊢ A (with_l)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const { checkResult } = proveExtractCheck(seq([AST.with(A, B)], A));
      assert.strictEqual(checkResult.valid, true);
    });

    it('A ⊢ A + B (oplus_r)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const { checkResult } = proveExtractCheck(seq([A], AST.oplus(A, B)));
      assert.strictEqual(checkResult.valid, true);
    });

    it('zero ⊢ C (zero_l)', () => {
      const C = AST.freevar('C');
      const { checkResult } = proveExtractCheck(seq([AST.zero()], C));
      assert.strictEqual(checkResult.valid, true);
    });

    it('; A ⊢ A (copy from cartesian)', () => {
      const A = AST.freevar('A');
      const { checkResult } = proveExtractCheck(seqCart([], [A], A));
      assert.strictEqual(checkResult.valid, true);
    });

    it('(A * B) -o C, A, B ⊢ C (nested)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const { checkResult } = proveExtractCheck(seq([AST.loli(AST.tensor(A, B), C), A, B], C));
      assert.strictEqual(checkResult.valid, true);
    });
  });

  // --- loli_match (C2) ---

  describe('loli_match — linear loli consumption (C2)', () => {
    it('validates loli_match inside monad_r evidence', () => {
      // Sequent: (a -o {b}), a |- {b}
      // monad_r enters lax mode, then loli_match consumes the loli:
      //   1. antecedent proof: id(a) — consumes a from delta
      //   2. consequent {b} added to delta, then monad_l unwraps to b, id(b)
      const a = AST.atom('a'), b = AST.atom('b');
      const monadB = AST.monad(b);
      const loli = AST.loli(a, monadB);

      const evidence = {
        rule: 'loli_match',
        principal: loli,
        groundAntecedent: a,
        groundFacts: [b],
        subterms: [
          { rule: 'id', principal: a, subterms: [] },
          { rule: 'monad_l', principal: monadB, subterms: [
            { rule: 'id', principal: b, subterms: [] }
          ] }
        ]
      };

      const term = { rule: 'monad_r', principal: null, subterms: [], evidence };
      const s = seq([loli, a], monadB);
      const result = checker.check(term, s);
      assert.strictEqual(result.valid, true, result.error || '');
    });

    it('rejects loli_match with wrong antecedent proof', () => {
      const a = AST.atom('a'), b = AST.atom('b'), c = AST.atom('c');
      const monadB = AST.monad(b);
      const loli = AST.loli(a, monadB);

      const evidence = {
        rule: 'loli_match',
        principal: loli,
        groundAntecedent: a,
        groundFacts: [b],
        subterms: [
          { rule: 'id', principal: c, subterms: [] },  // c not in context
          { rule: 'id', principal: b, subterms: [] }
        ]
      };

      const term = { rule: 'monad_r', principal: null, subterms: [], evidence };
      const s = seq([loli, a], monadB);
      const result = checker.check(term, s);
      assert.strictEqual(result.valid, false, 'should reject wrong antecedent');
    });
  });

  // --- Invalid terms rejected ---

  describe('invalid terms rejected', () => {
    it('rejects null term', () => {
      const A = AST.freevar('A');
      const result = checker.check(null, seq([A], A));
      assert.strictEqual(result.valid, false);
    });

    it('rejects unknown rule', () => {
      const A = AST.freevar('A');
      const result = checker.check({ rule: 'bogus', principal: null, subterms: [] }, seq([A], A));
      assert.strictEqual(result.valid, false);
    });

    it('rejects id with wrong principal', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      // Term says id(B) but B is not in the context [A]
      const result = checker.check(
        { rule: 'id', principal: B, subterms: [] },
        seq([A], A)
      );
      assert.strictEqual(result.valid, false);
    });

    it('rejects id with type mismatch', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      // id(A) : B — type doesn't match
      const result = checker.check(
        { rule: 'id', principal: A, subterms: [] },
        seq([A], B)
      );
      assert.strictEqual(result.valid, false);
    });

    it('unreachable returns unverified', () => {
      const A = AST.freevar('A');
      const result = checker.check(
        { rule: 'unreachable', principal: null, subterms: [], reason: 'test' },
        seq([], A)
      );
      assert.strictEqual(result.valid, true);
      assert.strictEqual(result.unverified, 'constraintUNSAT');
    });

    it('ffi returns unverified', () => {
      const A = AST.freevar('A');
      const result = checker.check(
        { rule: 'ffi', principal: null, subterms: [], witness: 'test' },
        seq([], A)
      );
      assert.strictEqual(result.valid, true);
      assert.strictEqual(result.unverified, 'ffiAxiom');
    });
  });
});

// =============================================================================
// Phase 5: Bridge Integration
// =============================================================================

describe('Bridge Integration', () => {
  let calc, AST, kernel;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    kernel = createKernel(calc);
  });

  describe('monad_r term construction', () => {
    it('extractTerm for monad_r attaches monadic term evidence when available', () => {
      // Simulate a proof tree with monad_r state containing a monadicTerm
      const mockMonadicTerm = { rule: 'id', principal: 42, subterms: [] };
      const mockTree = {
        proven: true,
        rule: 'monad_r',
        conclusion: {},
        premises: [],
        state: {
          modeSwitch: true, trace: [], monadicTerm: mockMonadicTerm,
          termVerified: true
        }
      };
      const term = extractTerm(mockTree, calc);
      assert.ok(term);
      assert.strictEqual(term.rule, 'monad_r');
      assert.strictEqual(term.evidence, mockMonadicTerm);
    });

    it('extractTerm for monad_r falls back to trace without monadic term', () => {
      const trace = [{ rule: 'step1', consumed: {} }];
      const mockTree = {
        proven: true,
        rule: 'monad_r',
        conclusion: {},
        premises: [],
        state: { modeSwitch: true, trace }
      };
      const term = extractTerm(mockTree, calc);
      assert.ok(term);
      assert.strictEqual(term.rule, 'monad_r');
      assert.strictEqual(term.evidence, trace);
    });
  });

  describe('kernel monad_r verification upgrade', () => {
    it('monad_r returns unverified without term evidence', () => {
      const succ = AST.monad(AST.atom('p'));
      const s = Seq.fromArrays([], [], succ);
      const result = kernel.verifyStep(s, 'monad_r', []);
      assert.strictEqual(result.valid, true);
      assert.strictEqual(result.unverified, 'modeSwitch');
    });

    it('monad_r returns verified with termVerified state', () => {
      const succ = AST.monad(AST.atom('p'));
      const s = Seq.fromArrays([], [], succ);
      const monadicTerm = { rule: 'id', principal: AST.atom('p'), subterms: [] };
      const state = { termVerified: true, monadicTerm };
      const result = kernel.verifyStep(s, 'monad_r', [], state);
      assert.strictEqual(result.valid, true);
      assert.strictEqual(result.unverified, undefined);
      assert.strictEqual(result.evidence, monadicTerm);
    });

    it('verifyTree passes state to verifyStep for monad_r', () => {
      const { ProofTree } = require('../lib/prover/pt');
      const succ = AST.monad(AST.atom('p'));
      const s = Seq.fromArrays([], [], succ);
      const monadicTerm = { rule: 'id', principal: AST.atom('p'), subterms: [] };
      const tree = new ProofTree({
        conclusion: s, rule: 'monad_r', proven: true, premises: [],
        state: { termVerified: true, monadicTerm }
      });
      const result = kernel.verifyTree(tree);
      assert.strictEqual(result.valid, true);
      assert.strictEqual(result.errors.length, 0);
    });
  });
});

// =============================================================================
// Phase 6: End-to-end Bridge Terms & Zero-overhead
// =============================================================================

describe('End-to-end bridge term construction', () => {
  let calc, AST;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
  });

  // Helper: compile a simple forward rule  a -o {b}
  function makeRule(a, b) {
    const ruleH = AST.loli(a, AST.monad(b));
    return compileRule({
      name: 'test_fwd', hash: ruleH,
      antecedent: a, consequent: AST.monad(b)
    }, { connectives: ILL_CONNECTIVES });
  }

  it('modeSwitch with terms:true produces monadicTerm', () => {
    const a = AST.atom('a'), b = AST.atom('b');
    const compiled = makeRule(a, b);
    const seq = Seq.fromArrays([a], [], AST.monad(b));

    const result = modeSwitch(seq, { forwardRules: [compiled] }, { terms: true });
    assert.ok(result, 'should produce a result');
    const st = result.proofNode.state;
    assert.ok(st.monadicTerm, 'should have monadicTerm');
    assert.ok(st.rightFocusTerm, 'should have rightFocusTerm');
    assert.strictEqual(st.termVerified, true);
  });

  it('monadicTerm has correct structure: let-binding wrapping rightFocus id', () => {
    const a = AST.atom('a'), b = AST.atom('b');
    const compiled = makeRule(a, b);
    const seq = Seq.fromArrays([a], [], AST.monad(b));

    const result = modeSwitch(seq, { forwardRules: [compiled] }, { terms: true });
    const mt = result.proofNode.state.monadicTerm;
    // Single forward step → one let-binding wrapping the rightFocus term
    assert.strictEqual(mt.rule, 'test_fwd');
    assert.ok(mt.subterms.length >= 1);
    // Terminal subterm should be the rightFocus result (id consuming b)
    const terminal = mt.subterms[mt.subterms.length - 1];
    assert.strictEqual(terminal.rule, 'id');
    assert.strictEqual(terminal.principal, b);
  });

  it('extractTerm on modeSwitch result attaches evidence', () => {
    const a = AST.atom('a'), b = AST.atom('b');
    const compiled = makeRule(a, b);
    const seq = Seq.fromArrays([a], [], AST.monad(b));

    const result = modeSwitch(seq, { forwardRules: [compiled] }, { terms: true });
    const term = extractTerm(result.proofNode, calc);
    assert.ok(term);
    assert.strictEqual(term.rule, 'monad_r');
    assert.ok(term.evidence, 'should have monadic term as evidence');
    assert.strictEqual(term.evidence.rule, 'test_fwd');
  });

  it('kernel verifies modeSwitch proof node with termVerified', () => {
    const a = AST.atom('a'), b = AST.atom('b');
    const compiled = makeRule(a, b);
    const seq = Seq.fromArrays([a], [], AST.monad(b));

    const result = modeSwitch(seq, { forwardRules: [compiled] }, { terms: true });
    const kernel = createKernel(calc);
    const vr = kernel.verifyStep(
      result.proofNode.conclusion, 'monad_r', [],
      result.proofNode.state
    );
    assert.strictEqual(vr.valid, true);
    assert.strictEqual(vr.unverified, undefined, 'should be fully verified');
    assert.ok(vr.evidence, 'should carry evidence');
  });

  it('leftover linear resources → modeSwitch returns null', () => {
    const a = AST.atom('a'), b = AST.atom('b');
    // Forward rule: a -o {a * b} — produces BOTH a and b
    const ruleH = AST.loli(a, AST.monad(AST.tensor(a, b)));
    const compiled = compileRule({
      name: 'overproducer', hash: ruleH,
      antecedent: a, consequent: AST.monad(AST.tensor(a, b))
    }, { connectives: ILL_CONNECTIVES });

    // Succedent only wants {a} — b will be leftover after rightFocus
    const seq = Seq.fromArrays([a], [], AST.monad(a));
    const result = modeSwitch(seq, { forwardRules: [compiled] }, { terms: true });
    assert.strictEqual(result, null, 'should fail: leftover b after rightFocus');
  });

  it('rightFocus decomposition failure → modeSwitch returns null', () => {
    const a = AST.atom('a'), b = AST.atom('b');
    const compiled = makeRule(a, b);
    // Forward produces b, but succedent wants {a} — rightFocus can't find a
    const seq = Seq.fromArrays([a], [], AST.monad(a));
    const result = modeSwitch(seq, { forwardRules: [compiled] });
    assert.strictEqual(result, null, 'should fail: residual b does not match succedent a');
  });
});

describe('Zero-overhead (terms: false)', () => {
  let calc, AST;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
  });

  function makeRule(a, b) {
    const ruleH = AST.loli(a, AST.monad(b));
    return compileRule({
      name: 'test_fwd', hash: ruleH,
      antecedent: a, consequent: AST.monad(b)
    }, { connectives: ILL_CONNECTIVES });
  }

  it('modeSwitch without terms option produces no term data', () => {
    const a = AST.atom('a'), b = AST.atom('b');
    const compiled = makeRule(a, b);
    const seq = Seq.fromArrays([a], [], AST.monad(b));

    const result = modeSwitch(seq, { forwardRules: [compiled] });
    assert.ok(result, 'proof still succeeds');
    const st = result.proofNode.state;
    assert.strictEqual(st.rightFocusTerm, null, 'no rightFocusTerm');
    assert.strictEqual(st.monadicTerm, null, 'no monadicTerm');
    assert.strictEqual(st.termVerified, false, 'not termVerified');
  });

  it('modeSwitch with terms:false produces no term data', () => {
    const a = AST.atom('a'), b = AST.atom('b');
    const compiled = makeRule(a, b);
    const seq = Seq.fromArrays([a], [], AST.monad(b));

    const result = modeSwitch(seq, { forwardRules: [compiled] }, { terms: false });
    assert.ok(result, 'proof still succeeds');
    const st = result.proofNode.state;
    assert.strictEqual(st.rightFocusTerm, null);
    assert.strictEqual(st.monadicTerm, null);
    assert.strictEqual(st.termVerified, false);
  });
});
