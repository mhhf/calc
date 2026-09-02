/**
 * Exact rationals — TODO_0265 Phase 1 unit tests.
 *
 * Covers the two-representation design (rat(N,D) term + ratlit storage):
 *   lib/rat.js                              pure ℚ arithmetic
 *   lib/kernel/store.js                     ratlit leaf + till tag commit
 *   lib/engine/theories/ratlit-theory.js    codec + eq-theory + classifier
 *   lib/engine/theories/rat-ffi.js          FFI overloads (via arithmetic.js)
 *   lib/engine/store-binary.js              serialize/compact with 2-bigint leaf
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import rat from '../../lib/rat.js';
import { ratlitTheory, putRat, ratParts, isRatTerm, installRatlitTheory }
  from '../../lib/engine/theories/ratlit-theory.js';
import { classifyFirstArg } from '../../lib/kernel/eq-theory.js';
import arithmetic from '../../calculus/ill/lib/ffi/arithmetic.js';
import ratFFI from '../../lib/engine/theories/rat-ffi.js';
import { serialize, deserialize, compact } from '../../lib/engine/store-binary.js';

const bin = (n) => Store.put1('binlit', n);
const mv = (name) => Store.put('metavar', [name]);

describe('lib/rat.js — pure rational arithmetic', () => {
  it('norm reduces and orients sign', () => {
    assert.deepEqual(rat.norm(2n, 4n), [1n, 2n]);
    assert.deepEqual(rat.norm(0n, 7n), [0n, 1n]);
    assert.deepEqual(rat.norm(3n, -6n), [-1n, 2n]);
    assert.deepEqual(rat.norm(-3n, -6n), [1n, 2n]);
    assert.throws(() => rat.norm(1n, 0n), RangeError);
  });

  it('add/sub/mul/div are exact and normalized', () => {
    assert.deepEqual(rat.add([1n, 2n], [1n, 3n]), [5n, 6n]);
    assert.deepEqual(rat.add([1n, 6n], [1n, 3n]), [1n, 2n]);
    assert.deepEqual(rat.sub([1n, 3n], [1n, 2n]), [-1n, 6n]);
    assert.deepEqual(rat.mul([2n, 3n], [3n, 4n]), [1n, 2n]);
    assert.deepEqual(rat.div([1n, 2n], [3n, 1n]), [1n, 6n]);
    assert.equal(rat.div([1n, 2n], [0n, 1n]), null);
  });

  it('cmp orders by value', () => {
    assert.equal(rat.cmp([1n, 3n], [1n, 2n]), -1);
    assert.equal(rat.cmp([2n, 4n], [1n, 2n]), 0);
    assert.equal(rat.cmp([3n, 2n], [1n, 1n]), 1);
  });

  it('gcd handles zeros and signs', () => {
    assert.equal(rat.gcd(0n, 5n), 5n);
    assert.equal(rat.gcd(12n, 18n), 6n);
    assert.equal(rat.gcd(-12n, 18n), 6n);
    assert.equal(rat.gcd(0n, 0n), 0n);
  });
});

describe('lib/rat.js — algebraic properties (sample grid)', () => {
  const SAMPLES = [];
  for (const n of [0n, 1n, 2n, 3n, 7n, 12n, 101n])
    for (const d of [1n, 2n, 3n, 5n, 12n]) SAMPLES.push([n, d]);

  it('norm is idempotent over the grid', () => {
    for (const [n, d] of SAMPLES) {
      const r1 = rat.norm(n, d);
      assert.deepEqual(rat.norm(r1[0], r1[1]), r1);
    }
  });

  it('add/mul are commutative over the grid', () => {
    for (const a of SAMPLES.slice(0, 12)) for (const b of SAMPLES.slice(0, 12)) {
      assert.deepEqual(rat.add(a, b), rat.add(b, a));
      assert.deepEqual(rat.mul(a, b), rat.mul(b, a));
    }
  });

  // ℚ field axioms + the (max, +) tropical structure the scheduler runs on
  // (round-13 testing residue ix). max is availability-⊕, add is effect-⊗.
  const max = (a, b) => (rat.cmp(a, b) >= 0 ? a : b);
  const b0 = [0n, 1n];
  const G = SAMPLES.slice(0, 10).map(([n, d]) => rat.norm(n, d))
    .concat([[-1n, 2n], [-3n, 1n]].map(([n, d]) => rat.norm(n, d)));

  it('field axioms: associativity, distributivity, inverses (sample grid)', () => {
    for (const a of G) for (const b of G) for (const c of G.slice(0, 5)) {
      assert.deepEqual(rat.add(rat.add(a, b), c), rat.add(a, rat.add(b, c)));
      assert.deepEqual(rat.mul(rat.mul(a, b), c), rat.mul(a, rat.mul(b, c)));
      assert.deepEqual(rat.mul(a, rat.add(b, c)), rat.add(rat.mul(a, b), rat.mul(a, c)));
    }
    for (const a of G) {
      assert.deepEqual(rat.add(a, rat.sub([0n, 1n], a)), [0n, 1n]);   // additive inverse
      if (a[0] !== 0n) assert.deepEqual(rat.mul(a, rat.div([1n, 1n], a)), [1n, 1n]);
      assert.deepEqual(rat.add(a, [0n, 1n]), a);                       // units
      assert.deepEqual(rat.mul(a, [1n, 1n]), a);
    }
  });

  it('tropical (max, +) dioid: distributivity, idempotence, unit', () => {
    for (const a of G) for (const b of G) for (const c of G.slice(0, 5)) {
      // ⊗ distributes over ⊕: max(a,b) + c = max(a+c, b+c)
      assert.deepEqual(rat.add(max(a, b), c), max(rat.add(a, c), rat.add(b, c)));
      assert.deepEqual(max(max(a, b), c), max(a, max(b, c)));
    }
    for (const a of G) {
      assert.deepEqual(max(a, a), a);          // ⊕ idempotent
      // 0 is the ⊕-unit on ℚ≥0 (the v1 stamp domain — activation starts at unit)
      if (rat.cmp(a, b0) >= 0) assert.deepEqual(max(a, b0), a);
    }
  });

  it('order: transitivity, totality, translation compatibility', () => {
    for (const a of G) for (const b of G) {
      assert.equal(rat.cmp(a, b) + rat.cmp(b, a), 0);                  // antisymmetric/total
      for (const c of G.slice(0, 5)) {
        if (rat.cmp(a, b) <= 0 && rat.cmp(b, c) <= 0) {
          assert.ok(rat.cmp(a, c) <= 0, 'transitivity');
        }
        // compatibility: a ≤ b ⇒ a+c ≤ b+c (what makes B&B pruning sound)
        if (rat.cmp(a, b) <= 0) assert.ok(rat.cmp(rat.add(a, c), rat.add(b, c)) <= 0);
      }
    }
  });

  it('gcd zero cases are symmetric; isInt agrees with den=1', () => {
    assert.equal(rat.gcd(5n, 0n), 5n);
    assert.equal(rat.gcd(0n, 5n), 5n);
    for (const [n, d] of SAMPLES) {
      const r = rat.norm(n, d);
      assert.equal(rat.isInt(r), r[1] === 1n);
    }
  });
});

describe('store — till kernel tag commit', () => {
  it('PRED_BOUNDARY covers exactly the pre-registered tags (regression)', () => {
    assert.equal(Store.PRED_BOUNDARY, 35); // 'gmonad' merged into binary 'monad' (D6, TODO_0157)
    for (const t of ['ratlit', 'at', 'after', 'before', 'monad']) {
      assert.ok(Store.TAG[t] !== undefined, `${t} registered`);
      assert.ok(Store.TAG[t] < Store.PRED_BOUNDARY, `${t} below boundary`);
    }
    const dyn = Store.put('some_fresh_pred_0265', [bin(1n)]);
    assert.ok(Store.tagId(dyn) >= Store.PRED_BOUNDARY);
  });

  it('ratlit stores two bigint children, is a ground leaf', () => {
    const h = Store.put('ratlit', [5n, 6n]);
    assert.equal(Store.tag(h), 'ratlit');
    assert.equal(Store.arity(h), 2);
    assert.equal(Store.child(h, 0), 5n);
    assert.equal(Store.child(h, 1), 6n);
    assert.ok(Store.isGround(h));
    assert.equal(Store.put('ratlit', [5n, 6n]), h); // content-addressed
  });
});

describe('ratlit-theory — codec and canonical form', () => {
  it('putRat canonicalizes: equal rationals are hash-equal', () => {
    assert.equal(putRat(2n, 4n), putRat(1n, 2n));
    assert.equal(putRat(1n, -2n), putRat(-1n, 2n));
    assert.equal(putRat(10n, 4n), putRat(5n, 2n));
  });

  it('putRat collapses den=1 to binlit (ℚ ⊇ ℕ, one hash per value)', () => {
    assert.equal(putRat(6n, 2n), bin(3n));
    assert.equal(putRat(0n, 5n), bin(0n));
    assert.equal(Store.tag(putRat(7n, 2n)), 'ratlit');
  });

  it('ratParts decodes ratlit, bin coercion, and structural rat(N,D)', () => {
    assert.deepEqual(ratParts(putRat(5n, 6n)), [5n, 6n]);
    assert.deepEqual(ratParts(bin(3n)), [3n, 1n]);
    const structural = Store.put('rat', [bin(2n), bin(4n)]);
    assert.deepEqual(ratParts(structural), [2n, 4n]); // un-normalized as written
    assert.equal(ratParts(mv('X')), null);
    assert.equal(ratParts(Store.put('rat', [bin(1n), bin(0n)])), null); // 1/0
  });

  it('isRatTerm gates the FFI dispatch: bins are NOT rational-represented', () => {
    assert.ok(isRatTerm(putRat(1n, 2n)));
    assert.ok(isRatTerm(Store.put('rat', [bin(1n), bin(2n)])));
    assert.ok(!isRatTerm(bin(7n)));
    assert.ok(!isRatTerm(Store.put('atom', ['e'])));
  });

  it('rewrite: ratlit → rat(binlit, binlit) for pattern matching', () => {
    const rl = putRat(5n, 6n);
    const ratTag = Store.TAG.rat;
    const r = ratlitTheory.rewrite(Store.TAG.ratlit, rl, ratTag, 2);
    assert.equal(Store.tag(r), 'rat');
    assert.equal(Store.child(Store.child(r, 0), 0), 5n);
    assert.equal(Store.child(Store.child(r, 1), 0), 6n);
    assert.ok(ratlitTheory.canRewrite(Store.TAG.ratlit, ratTag));
    assert.ok(!ratlitTheory.canRewrite(Store.TAG.binlit, ratTag));
  });

  it('canonicalize maps structural rat to canonical compact form, recursively', () => {
    const structural = Store.put('rat', [bin(2n), bin(4n)]);
    assert.equal(ratlitTheory.canonicalize(structural), putRat(1n, 2n));
    const intish = Store.put('rat', [bin(6n), bin(2n)]);
    assert.equal(ratlitTheory.canonicalize(intish), bin(3n));
    const wrapped = Store.put('foo_wrap_0265', [structural, bin(9n)]);
    const canon = ratlitTheory.canonicalize(wrapped);
    assert.equal(Store.child(canon, 0), putRat(1n, 2n));
    assert.equal(Store.child(canon, 1), bin(9n));
    // zero denominator stays put (clauses guard it)
    const bad = Store.put('rat', [bin(1n), bin(0n)]);
    assert.equal(ratlitTheory.canonicalize(bad), bad);
  });

  it('installRatlitTheory registers the first-arg classifier (ratlit → rat bucket)', () => {
    installRatlitTheory();
    assert.equal(classifyFirstArg(Store.TAG.ratlit, putRat(1n, 2n)), 'rat');
    assert.equal(classifyFirstArg(Store.TAG.binlit, bin(1n)), null); // binlit stays inline
  });
});

describe('FFI — split namespaces (bin family vs q-family)', () => {
  const half = () => putRat(1n, 2n);
  const third = () => putRat(1n, 3n);

  it('bin family rejects rationals (no overloading — D8.1 revised)', () => {
    assert.ok(!arithmetic.plus([half(), third(), mv('R')]).success);
    assert.ok(!arithmetic.mul([half(), bin(4n), mv('R')]).success);
    assert.ok(!arithmetic.sub([half(), third(), mv('R')]).success);
    assert.ok(!arithmetic.div([half(), bin(3n), mv('R')]).success);
    assert.ok(!arithmetic.lt([third(), half()]).success);
    assert.ok(!arithmetic.eq([putRat(2n, 4n), half()]).success);
    // and bin×bin semantics are byte-identical to before Phase 1
    assert.equal(arithmetic.plus([bin(3n), bin(4n), mv('R')]).theta[0][1], bin(7n));
    assert.equal(arithmetic.div([bin(7n), bin(2n), mv('R')]).theta[0][1], bin(3n));
  });

  it('qplus/qmul: exact, bins coerce, den=1 collapses', () => {
    let r = ratFFI.qplus([half(), third(), mv('R')]);
    assert.equal(r.theta[0][1], putRat(5n, 6n));
    r = ratFFI.qplus([bin(3n), half(), mv('R')]);
    assert.equal(r.theta[0][1], putRat(7n, 2n));
    r = ratFFI.qplus([half(), half(), mv('R')]);
    assert.equal(r.theta[0][1], bin(1n)); // collapses to binlit
    r = ratFFI.qmul([putRat(2n, 3n), putRat(3n, 4n), mv('R')]);
    assert.equal(r.theta[0][1], putRat(1n, 2n));
    r = ratFFI.qmul([bin(4n), putRat(3n, 4n), mv('R')]);
    assert.equal(r.theta[0][1], bin(3n));
  });

  it('qsub is checked (fails on negative), qdiv is exact field division', () => {
    let r = ratFFI.qsub([half(), third(), mv('R')]);
    assert.equal(r.theta[0][1], putRat(1n, 6n));

    r = ratFFI.qsub([third(), half(), mv('R')]);
    assert.ok(!r.success);
    assert.equal(r.reason, 'negative_result'); // checked, not saturating

    r = ratFFI.qdiv([half(), bin(3n), mv('R')]);
    assert.equal(r.theta[0][1], putRat(1n, 6n));

    r = ratFFI.qdiv([bin(3n), half(), mv('R')]);
    assert.equal(r.theta[0][1], bin(6n));

    r = ratFFI.qdiv([bin(7n), bin(2n), mv('R')]);
    assert.equal(r.theta[0][1], putRat(7n, 2n)); // exact, unlike Euclidean div

    r = ratFFI.qdiv([half(), bin(0n), mv('R')]);
    assert.ok(!r.success);
    assert.equal(r.reason, 'division_by_zero');
  });

  it('q-comparisons: qlt/qle/qeq/qneq/qeq_bool by value', () => {
    assert.ok(ratFFI.qlt([third(), half()]).success);
    assert.ok(!ratFFI.qlt([half(), third()]).success);
    assert.ok(ratFFI.qlt([third(), bin(1n)]).success);
    assert.ok(ratFFI.qle([half(), half()]).success);
    assert.ok(ratFFI.qeq([putRat(2n, 4n), half()]).success);
    assert.ok(ratFFI.qeq([bin(3n), bin(3n)]).success);
    assert.ok(ratFFI.qneq([half(), third()]).success);
    assert.ok(!ratFFI.qneq([half(), putRat(2n, 4n)]).success);
    assert.equal(ratFFI.qeq_bool([half(), third(), mv('Z')]).theta[0][1], bin(0n));
    assert.equal(ratFFI.qeq_bool([half(), half(), mv('Z')]).theta[0][1], bin(1n));
  });

  it('qmin/qmax: order-theoretic selection, bins coerce, result is an argument (P2)', () => {
    // mixed bin/frac: the q order decides, the chosen ARGUMENT is the result
    assert.equal(ratFFI.qmin([bin(7n), putRat(13n, 2n), mv('R')]).theta[0][1], putRat(13n, 2n));
    assert.equal(ratFFI.qmax([bin(7n), putRat(13n, 2n), mv('R')]).theta[0][1], bin(7n));
    assert.equal(ratFFI.qmin([third(), half(), mv('R')]).theta[0][1], putRat(1n, 3n));
    assert.equal(ratFFI.qmax([third(), half(), mv('R')]).theta[0][1], putRat(1n, 2n));
    // bin×bin agrees with the bin instance (the coherence law behind the
    // collapsed names — num.min/num.max dispatch)
    assert.equal(ratFFI.qmin([bin(3n), bin(5n), mv('R')]).theta[0][1], bin(3n));
    assert.equal(arithmetic.min([bin(3n), bin(5n), mv('R')]).theta[0][1], bin(3n));
    // equal values are one hash either way
    assert.equal(ratFFI.qmin([putRat(2n, 4n), half(), mv('R')]).theta[0][1], half());
    assert.equal(ratFFI.qmax([putRat(2n, 4n), half(), mv('R')]).theta[0][1], half());
    // ℚ≥0 contract: negatives refused like every q-op
    assert.ok(!ratFFI.qmin([putRat(-1n, 2n), half(), mv('R')]).success);
    // non-ground input: advisory conversion failure
    assert.ok(!ratFFI.qmax([mv('X'), half(), mv('R')]).success);
  });

  it('canonicalize folds o/i numerals over rational leaves (o(x)=2x, i(x)=2x+1)', () => {
    const wrapped = Store.put('o', [Store.put('o', [putRat(3n, 4n)])]);
    assert.equal(ratlitTheory.canonicalize(wrapped), bin(3n)); // 4 · 3/4
    const iWrapped = Store.put('i', [putRat(1n, 4n)]);
    assert.equal(ratlitTheory.canonicalize(iWrapped), putRat(3n, 2n)); // 2·1/4 + 1
  });
});

describe('negative rationals — ℚ≥0 contract (audit round 11)', () => {
  it('storage is signed (D14: no migration later) but q-op FFI refuses negatives', () => {
    const neg = putRat(-7n, 3n);
    assert.equal(Store.tag(neg), 'ratlit');
    assert.equal(Store.child(neg, 0), -7n);
    // FFI parity with the ℕ-ranged clause layer: both must refuse.
    for (const [name, arity] of [['qplus', 3], ['qsub', 3], ['qmul', 3], ['qdiv', 3], ['qlt', 2], ['qeq', 2]]) {
      const args = arity === 3 ? [neg, bin(1n), mv('R')] : [neg, bin(1n)];
      const res = ratFFI[name](args);
      assert.ok(!res.success, `${name} refuses a negative numerator`);
    }
    // Symmetric: negative in the second position
    assert.ok(!ratFFI.qplus([bin(1n), neg, mv('R')]).success);
  });

  it('rewrite still refuses negatives (clause layer cannot represent them)', () => {
    const neg = putRat(-1n, 2n);
    const tr = Store.TAG.rat;
    if (tr !== undefined) {
      assert.equal(ratlitTheory.rewrite(Store.tagId(neg), neg, tr, 2), null);
    }
  });
});

describe('store-binary — ratlit round-trip and GC', () => {
  it('serialize/deserialize preserves ratlit (2 bigint children)', () => {
    const rl = putRat(-7n, 3n); // negative num exercises the sign byte
    const pair = Store.put('pair_0265', [rl, bin(9n)]);
    const buf = serialize(Store.snapshot({ root: pair }));
    const snap = deserialize(buf);
    Store.restore(snap);
    const root = snap.metadata.root;
    const rl2 = Store.child(root, 0);
    assert.equal(Store.tag(rl2), 'ratlit');
    assert.equal(Store.child(rl2, 0), -7n);
    assert.equal(Store.child(rl2, 1), 3n);
    // content addressing survives: re-putting finds the restored node
    assert.equal(Store.put('ratlit', [-7n, 3n]), rl2);
  });

  it('compact does not remap ratlit bigint children as term IDs', () => {
    Store.clear();
    // garbage first so compaction actually renumbers
    for (let i = 0; i < 50; i++) Store.put('garbage_0265', [bin(BigInt(i))]);
    const rl = putRat(5n, 6n);
    const root = Store.put('pair_0265', [rl, bin(1n)]);
    const snap = compact(Store.snapshot({ root }));
    assert.ok(snap.nodeCount < 55, 'garbage collected');
    Store.restore(snap);
    const r2 = snap.metadata.root;
    const rlr = Store.child(r2, 0);
    assert.equal(Store.tag(rlr), 'ratlit');
    assert.equal(Store.child(rlr, 0), 5n);
    assert.equal(Store.child(rlr, 1), 6n);
    assert.equal(putRat(5n, 6n), rlr); // dedup hash recomputed correctly
  });
});
