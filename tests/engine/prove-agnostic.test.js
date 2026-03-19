/**
 * Calculus-agnostic backward prover tests.
 *
 * Exercises the slot-indexed theta + trail backtracking prover
 * using synthetic clauses with no ILL-specific connectives.
 * Validates: matching, backtracking, recursion, equational normalization,
 * metavar binding, multi-premise clauses, and proof term output.
 */

const { describe, it } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { prove } = require('../../lib/engine/prove');

// ── Helpers ──────────────────────────────────────────────────────────

function atom(name) { return Store.put('atom', [name]); }
function metavar(name) { return Store.put('metavar', [name]); }
function pred(name, ...args) { return Store.put(name, args); }

/** Build clauses/types Maps from declarative specs */
function buildSpec(spec) {
  const types = new Map();
  const clauses = new Map();
  for (const [name, head, ...premises] of spec) {
    if (premises.length === 0) {
      types.set(name, head);
    } else {
      clauses.set(name, { hash: head, premises });
    }
  }
  return { types, clauses };
}

/** Prove a goal and return { success, theta (as plain object), term } */
function proveGoal(goal, spec, opts = {}) {
  const { types, clauses } = buildSpec(spec);
  const result = prove(goal, clauses, types, {
    normalize: x => x,          // no ILL normalization
    buildClauseTerm: null,       // use default
    tryFFI: null,                // no FFI
    useFFI: false,
    ...opts,
  });
  // Convert theta to a readable object
  const theta = {};
  if (result.theta) {
    for (const [k, v] of result.theta) {
      theta[Store.child(k, 0)] = v; // metavar name → value
    }
  }
  return { success: result.success, theta, term: result.term, trace: result.trace };
}

// ── Tests ────────────────────────────────────────────────────────────

describe('Backward Prover — Calculus Agnostic', () => {
  // Synthetic predicates: parent(X, Y), ancestor(X, Y), append(L, M, N)

  describe('Type/axiom matching', () => {
    const SPEC = [
      // parent(alice, bob). parent(bob, carol). parent(carol, dave).
      ['p/ab', pred('parent', atom('alice'), atom('bob'))],
      ['p/bc', pred('parent', atom('bob'), atom('carol'))],
      ['p/cd', pred('parent', atom('carol'), atom('dave'))],
    ];

    it('proves a ground fact', () => {
      const r = proveGoal(pred('parent', atom('alice'), atom('bob')), SPEC);
      assert(r.success);
    });

    it('fails for non-existent fact', () => {
      const r = proveGoal(pred('parent', atom('alice'), atom('dave')), SPEC);
      assert(!r.success);
    });

    it('binds output metavar', () => {
      const r = proveGoal(pred('parent', atom('alice'), metavar('X')), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['X'], atom('bob'));
    });

    it('binds input metavar', () => {
      const r = proveGoal(pred('parent', metavar('X'), atom('carol')), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['X'], atom('bob'));
    });

    it('binds both metavars', () => {
      const r = proveGoal(pred('parent', metavar('X'), metavar('Y')), SPEC);
      assert(r.success);
      // Should match first candidate (p/ab)
      assert.strictEqual(r.theta['X'], atom('alice'));
      assert.strictEqual(r.theta['Y'], atom('bob'));
    });
  });

  describe('Clause resolution with premises', () => {
    const SPEC = [
      // ancestor(X, Y) :- parent(X, Y).
      ['anc/base', pred('ancestor', metavar('A'), metavar('B')),
        pred('parent', metavar('A'), metavar('B'))],
      // ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).
      ['anc/step', pred('ancestor', metavar('A'), metavar('C')),
        pred('parent', metavar('A'), metavar('B')),
        pred('ancestor', metavar('B'), metavar('C'))],
      // Facts
      ['p/ab', pred('parent', atom('alice'), atom('bob'))],
      ['p/bc', pred('parent', atom('bob'), atom('carol'))],
      ['p/cd', pred('parent', atom('carol'), atom('dave'))],
    ];

    it('direct parent is ancestor (base case)', () => {
      const r = proveGoal(pred('ancestor', atom('alice'), atom('bob')), SPEC);
      assert(r.success);
    });

    it('grandparent is ancestor (1 step)', () => {
      const r = proveGoal(pred('ancestor', atom('alice'), atom('carol')), SPEC);
      assert(r.success);
    });

    it('great-grandparent is ancestor (2 steps)', () => {
      const r = proveGoal(pred('ancestor', atom('alice'), atom('dave')), SPEC);
      assert(r.success);
    });

    it('non-ancestor fails', () => {
      const r = proveGoal(pred('ancestor', atom('dave'), atom('alice')), SPEC);
      assert(!r.success);
    });

    it('binds intermediate variables', () => {
      const r = proveGoal(pred('ancestor', atom('alice'), metavar('Z')), SPEC);
      assert(r.success);
      // DFS: anc/base fires first → Z = bob
      assert.strictEqual(r.theta['Z'], atom('bob'));
    });
  });

  describe('Backtracking', () => {
    // Clauses ordered so first candidate fails, second succeeds
    const SPEC = [
      // likes(X, Y) :- rich(X), expensive(Y).     ← will fail (alice not rich)
      ['likes/rich', pred('likes', metavar('X'), metavar('Y')),
        pred('rich', metavar('X')), pred('expensive', metavar('Y'))],
      // likes(X, Y) :- kind(X), cute(Y).           ← will succeed
      ['likes/kind', pred('likes', metavar('X'), metavar('Y')),
        pred('kind', metavar('X')), pred('cute', metavar('Y'))],
      // Facts
      ['f/kind', pred('kind', atom('alice'))],
      ['f/cute', pred('cute', atom('puppy'))],
    ];

    it('backtracks past failing clause to find solution', () => {
      const r = proveGoal(pred('likes', atom('alice'), metavar('Y')), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['Y'], atom('puppy'));
    });

    it('fails when all clauses fail', () => {
      const r = proveGoal(pred('likes', atom('bob'), metavar('Y')), SPEC);
      assert(!r.success); // bob is neither rich nor kind
    });
  });

  describe('Depth limit', () => {
    // Infinite recursion: loop(X) :- loop(X).
    const SPEC = [
      ['loop/r', pred('loop', metavar('X')), pred('loop', metavar('X'))],
    ];

    it('respects maxDepth', () => {
      const r = proveGoal(pred('loop', atom('a')), SPEC, { maxDepth: 10 });
      assert(!r.success);
    });
  });

  describe('Multi-argument indexing', () => {
    // color(red). color(blue). color(green).
    const SPEC = [
      ['c/r', pred('color', atom('red'))],
      ['c/b', pred('color', atom('blue'))],
      ['c/g', pred('color', atom('green'))],
    ];

    it('finds specific color', () => {
      assert(proveGoal(pred('color', atom('blue')), SPEC).success);
    });

    it('fails for unknown color', () => {
      assert(!proveGoal(pred('color', atom('purple')), SPEC).success);
    });

    it('enumerates via metavar (returns first)', () => {
      const r = proveGoal(pred('color', metavar('C')), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['C'], atom('red')); // first in index
    });
  });

  describe('Compound term matching', () => {
    // succ-based nat: add(z, Y, Y). add(s(X), Y, s(Z)) :- add(X, Y, Z).
    const z = atom('z');
    const SPEC = [
      ['add/z', pred('add', z, metavar('Y'), metavar('Y'))],
      ['add/s', pred('add', pred('s', metavar('X')), metavar('Y'), pred('s', metavar('Z'))),
        pred('add', metavar('X'), metavar('Y'), metavar('Z'))],
    ];

    function nat(n) {
      let r = z;
      for (let i = 0; i < n; i++) r = pred('s', r);
      return r;
    }

    it('add(0, 3, 3)', () => {
      assert(proveGoal(pred('add', nat(0), nat(3), nat(3)), SPEC).success);
    });

    it('add(2, 3, 5)', () => {
      assert(proveGoal(pred('add', nat(2), nat(3), nat(5)), SPEC).success);
    });

    it('add(2, 3, 4) fails', () => {
      assert(!proveGoal(pred('add', nat(2), nat(3), nat(4)), SPEC).success);
    });

    it('add(2, 3, ?Z) binds Z=5', () => {
      const r = proveGoal(pred('add', nat(2), nat(3), metavar('Z')), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['Z'], nat(5));
    });

    it('add(?X, 3, 5) binds X=2', () => {
      const r = proveGoal(pred('add', metavar('X'), nat(3), nat(5)), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['X'], nat(2));
    });
  });

  describe('Repeated variables in clause head', () => {
    // eq(X, X).
    const SPEC = [
      ['eq/refl', pred('eq', metavar('X'), metavar('X'))],
    ];

    it('equal terms succeed', () => {
      assert(proveGoal(pred('eq', atom('a'), atom('a')), SPEC).success);
    });

    it('unequal terms fail', () => {
      assert(!proveGoal(pred('eq', atom('a'), atom('b')), SPEC).success);
    });

    it('metavar in one position gets bound', () => {
      const r = proveGoal(pred('eq', atom('hello'), metavar('Y')), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['Y'], atom('hello'));
    });
  });

  describe('Equational normalization: binlit ↔ o/i/e', () => {
    // Uses binary structural patterns with binlit compact form
    // inc(e, i(e)).  inc(i(X), o(s(X))). inc(o(X), i(X)).
    // (simplified: inc(0, 1). inc via structural binary)

    it('matches binlit against structural pattern', () => {
      const e = atom('e');
      const SPEC = [
        // plus_z: plus(e, Y, Y). — zero + Y = Y
        ['plus/z', pred('plus', e, metavar('Y'), metavar('Y'))],
      ];
      // plus(0, 5, ?Z) should match via equational normalization (0 = e)
      const r = proveGoal(
        pred('plus', Store.put1('binlit', 0n), Store.put1('binlit', 5n), metavar('Z')),
        SPEC
      );
      assert(r.success);
      assert.strictEqual(Store.child(r.theta['Z'], 0), 5n);
    });
  });

  describe('Equational normalization: arrlit ↔ acons/ae', () => {
    it('matches arrlit against acons pattern', () => {
      const ae = atom('ae');
      const SPEC = [
        // head(acons(H, T), H).
        ['head/cons', pred('head', pred('acons', metavar('H'), metavar('T')), metavar('H'))],
        // head(ae, default).
        ['head/empty', pred('head', ae, atom('default'))],
      ];
      // head([10, 20, 30], ?X) — arrlit should expand to acons
      const arr = Store.putArray(new Uint32Array([
        Store.put1('binlit', 10n),
        Store.put1('binlit', 20n),
        Store.put1('binlit', 30n),
      ]));
      const r = proveGoal(pred('head', arr, metavar('X')), SPEC);
      assert(r.success);
      assert.strictEqual(Store.child(r.theta['X'], 0), 10n);
    });
  });

  describe('Sequential prove() calls (state isolation)', () => {
    const SPEC = [
      ['f/a', pred('f', atom('a'), atom('1'))],
      ['f/b', pred('f', atom('b'), atom('2'))],
      ['f/c', pred('f', atom('c'), atom('3'))],
    ];

    it('independent calls return correct results', () => {
      const r1 = proveGoal(pred('f', atom('a'), metavar('V')), SPEC);
      const r2 = proveGoal(pred('f', atom('b'), metavar('V')), SPEC);
      const r3 = proveGoal(pred('f', atom('c'), metavar('V')), SPEC);
      assert(r1.success);
      assert(r2.success);
      assert(r3.success);
      assert.strictEqual(r1.theta['V'], atom('1'));
      assert.strictEqual(r2.theta['V'], atom('2'));
      assert.strictEqual(r3.theta['V'], atom('3'));
    });
  });

  describe('Compiled premise construction (PUT instructions)', () => {
    // These tests exercise the _executePut path for different premise shapes:
    // simple predicates, nested compounds, multi-premise clauses, and
    // ground sub-trees mixed with metavar slots.

    it('simple pred(X, Y) premise — both args from slots', () => {
      // rel(X, Y) :- link(X, Z), link(Z, Y)
      const SPEC = [
        ['rel', pred('rel', metavar('X'), metavar('Y')),
          pred('link', metavar('X'), metavar('Z')),
          pred('link', metavar('Z'), metavar('Y'))],
        ['l/ab', pred('link', atom('a'), atom('b'))],
        ['l/bc', pred('link', atom('b'), atom('c'))],
      ];
      const r = proveGoal(pred('rel', atom('a'), metavar('R')), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['R'], atom('c'));
    });

    it('nested compound premise — succ(succ(X))', () => {
      Store.registerTag('succ');
      // double(X, Y) :- step(X, Z), step(Z, Y)
      // step(succ(N), N)  [type: peels one succ]
      const SPEC = [
        ['double', pred('double', metavar('X'), metavar('Y')),
          pred('step', metavar('X'), metavar('Z')),
          pred('step', metavar('Z'), metavar('Y'))],
        ['step', pred('step', pred('succ', metavar('N')), metavar('N'))],
      ];
      const two = pred('succ', pred('succ', atom('zero')));
      const r = proveGoal(pred('double', two, metavar('R')), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['R'], atom('zero'));
    });

    it('ground sub-tree in premise preserved', () => {
      // check(X) :- valid(X, ground_tag)
      const SPEC = [
        ['check', pred('check', metavar('X')),
          pred('valid', metavar('X'), atom('ok'))],
        ['v/a', pred('valid', atom('a'), atom('ok'))],
      ];
      const r = proveGoal(pred('check', atom('a')), SPEC);
      assert(r.success);
    });

    it('three-premise clause with shared variables', () => {
      // chain(A, D) :- hop(A, B), hop(B, C), hop(C, D)
      const SPEC = [
        ['chain', pred('chain', metavar('A'), metavar('D')),
          pred('hop', metavar('A'), metavar('B')),
          pred('hop', metavar('B'), metavar('C')),
          pred('hop', metavar('C'), metavar('D'))],
        ['h/12', pred('hop', atom('1'), atom('2'))],
        ['h/23', pred('hop', atom('2'), atom('3'))],
        ['h/34', pred('hop', atom('3'), atom('4'))],
      ];
      const r = proveGoal(pred('chain', atom('1'), metavar('R')), SPEC);
      assert(r.success);
      assert.strictEqual(r.theta['R'], atom('4'));
    });
  });

  describe('Trace output', () => {
    const SPEC = [
      ['anc/base', pred('ancestor', metavar('A'), metavar('B')),
        pred('parent', metavar('A'), metavar('B'))],
      ['p/ab', pred('parent', atom('alice'), atom('bob'))],
    ];

    it('produces trace when enabled', () => {
      const r = proveGoal(pred('ancestor', atom('alice'), metavar('Z')), SPEC, { trace: true });
      assert(r.success);
      assert(Array.isArray(r.trace));
      assert(r.trace.length > 0);
    });
  });
});
