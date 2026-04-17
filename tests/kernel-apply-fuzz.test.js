/**
 * TODO_0216 Phase 0 H1 — apply() property fuzzer
 *
 * Generates random (term, theta) pairs with a fixed seed and asserts
 * equality between the production `apply()` and a frozen reference
 * (`apply_ref` below) pinned at Phase 0 semantics.
 *
 * Catches:
 *  • D (Phase 1) arrlit descent / ground-bit false negatives
 *  • A (Phase 2) Map-vs-linear first-match divergence (duplicate keys)
 *  • N (Phase 3) Substitution-type translation bugs
 *  • any silent `apply()` drift
 *
 * Shapes exercised:
 *  • atoms, freevars, metavars
 *  • binary connectives (tensor/loli/with/oplus) to varying depth
 *  • arrlit children
 *  • θ with 0, 1, 5, 30 entries
 *  • θ with duplicate keys (first-match semantics enforced)
 *  • θ whose values themselves contain metavars (then post-closed for idempotence)
 *
 * When Phases 1-3 land, rerun this file — any failure is a correctness regression.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const calculus = require('../lib/calculus');
const Store = require('../lib/kernel/store');
const { apply } = require('../lib/kernel/substitute');

// ── Frozen reference apply — DO NOT EDIT ────────────────────────────────────
//
// Literal copy of lib/kernel/substitute.js::apply at commit 92dd11e. Used as
// oracle for the fuzzer. When Phase 1-3 ship, production `apply` must stay
// semantically identical to this.

function apply_ref(h, theta) {
  if (theta.length === 0) return h;

  function go(hash) {
    for (let i = 0; i < theta.length; i++) {
      if (theta[i][0] === hash) return theta[i][1];
    }

    const t = Store.tag(hash);
    if (!t) return hash;

    if (t === 'atom' || t === 'freevar' || t === 'metavar') return hash;

    if (Store.tagId(hash) === Store.TAG.arrlit) {
      const elems = Store.getArrayElements(hash);
      if (!elems || elems.length === 0) return hash;
      let changed = false;
      let newElems;
      for (let i = 0; i < elems.length; i++) {
        const ne = go(elems[i]);
        if (ne !== elems[i]) {
          if (!changed) {
            changed = true;
            newElems = new Uint32Array(elems.length);
            for (let j = 0; j < i; j++) newElems[j] = elems[j];
          }
          newElems[i] = ne;
        } else if (changed) {
          newElems[i] = elems[i];
        }
      }
      return changed ? Store.putArray(newElems) : hash;
    }

    const a = Store.arity(hash);
    let changed = false;
    const newChildren = [];
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (Store.isTermChild(c)) {
        const nc = go(c);
        if (nc !== c) changed = true;
        newChildren.push(nc);
      } else {
        newChildren.push(c);
      }
    }

    return changed ? Store.put(t, newChildren) : hash;
  }

  return go(h);
}

// ── Deterministic PRNG (mulberry32) ─────────────────────────────────────────

function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// ── Term generators ─────────────────────────────────────────────────────────

function pick(r, arr) { return arr[Math.floor(r() * arr.length)]; }

function makeVocab(AST) {
  return {
    atoms: ['p', 'q', 'r', 's', 'stop', 'revert', 'foo'].map(n => AST.atom(n)),
    freevars: ['X', 'Y', 'Z'].map(n => AST.freevar(n)),
    metavars: ['m0', 'm1', 'm2', 'm3', 'm4'].map(n => AST.metavar(n)),
  };
}

function genTerm(r, vocab, AST, depth) {
  if (depth <= 0) {
    const bag = r() < 0.35
      ? vocab.metavars
      : (r() < 0.5 ? vocab.atoms : vocab.freevars);
    return pick(r, bag);
  }
  const k = r();
  if (k < 0.15) {
    // arrlit with 2-4 elements
    const n = 2 + Math.floor(r() * 3);
    const elems = new Uint32Array(n);
    for (let i = 0; i < n; i++) elems[i] = genTerm(r, vocab, AST, depth - 1);
    return Store.putArray(elems);
  }
  if (k < 0.4) return AST.tensor(genTerm(r, vocab, AST, depth - 1), genTerm(r, vocab, AST, depth - 1));
  if (k < 0.6) return AST.loli(genTerm(r, vocab, AST, depth - 1), genTerm(r, vocab, AST, depth - 1));
  if (k < 0.75) return AST.with(genTerm(r, vocab, AST, depth - 1), genTerm(r, vocab, AST, depth - 1));
  if (k < 0.9) return AST.oplus(genTerm(r, vocab, AST, depth - 1), genTerm(r, vocab, AST, depth - 1));
  const bag = r() < 0.5 ? vocab.atoms : vocab.metavars;
  return pick(r, bag);
}

function genTheta(r, vocab, AST, sizeHint) {
  const n = Math.max(0, Math.floor(r() * (sizeHint + 1)));
  const theta = [];
  for (let i = 0; i < n; i++) {
    const v = pick(r, vocab.metavars);
    const val = genTerm(r, vocab, AST, 1 + Math.floor(r() * 3));
    theta.push([v, val]);
  }
  return theta;
}

// Close θ under itself (idempotent form — required invariant per substitute.js:87).
function closeTheta(theta) {
  for (let i = 0; i < theta.length; i++) {
    theta[i][1] = apply_ref(theta[i][1], theta);
  }
  return theta;
}

// ── Tests ───────────────────────────────────────────────────────────────────

describe('TODO_0216 H1 — apply() property fuzzer vs frozen reference', { concurrency: 1 }, () => {
  let AST, vocab;

  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
    vocab = makeVocab(AST);
  });

  it('empty theta is identity (100 terms)', () => {
    const r = rng(0xC0FFEE);
    for (let i = 0; i < 100; i++) {
      const h = genTerm(r, vocab, AST, 3 + Math.floor(r() * 3));
      assert.strictEqual(apply(h, []), h);
      assert.strictEqual(apply_ref(h, []), h);
    }
  });

  it('idempotent θ matches frozen reference (2000 cases)', () => {
    const r = rng(0xBAD1DEA);
    for (let i = 0; i < 2000; i++) {
      const h = genTerm(r, vocab, AST, 2 + Math.floor(r() * 4));
      const theta = closeTheta(genTheta(r, vocab, AST, 5));
      const a = apply(h, theta);
      const b = apply_ref(h, theta);
      if (a !== b) {
        assert.fail(`drift at case ${i}: apply=${a} ref=${b} theta.len=${theta.length}`);
      }
    }
  });

  it('large idempotent θ (30 entries) matches reference (300 cases)', () => {
    const r = rng(0xFACEFEED);
    for (let i = 0; i < 300; i++) {
      const h = genTerm(r, vocab, AST, 3 + Math.floor(r() * 4));
      const theta = closeTheta(genTheta(r, vocab, AST, 30));
      const a = apply(h, theta);
      const b = apply_ref(h, theta);
      assert.strictEqual(a, b, `large-theta drift at case ${i} (theta.len=${theta.length})`);
    }
  });

  it('first-match semantics on duplicate-key θ (500 cases)', () => {
    // Ensures that if A changes θ to a Map, the first-match rule is preserved
    // by checking against the reference (which is a linear scan — first hit wins).
    const r = rng(0xDEADBEEF);
    for (let i = 0; i < 500; i++) {
      const h = genTerm(r, vocab, AST, 2 + Math.floor(r() * 3));
      // Build θ with guaranteed duplicates by appending overwriting entries.
      const base = genTheta(r, vocab, AST, 5);
      const extras = [];
      for (let k = 0; k < base.length; k++) {
        if (r() < 0.5) {
          // duplicate key with a DIFFERENT value
          extras.push([base[k][0], pick(r, vocab.atoms)]);
        }
      }
      const theta = [...base, ...extras]; // do NOT close — we specifically test first-match
      const a = apply(h, theta);
      const b = apply_ref(h, theta);
      assert.strictEqual(a, b, `duplicate-key drift at case ${i}`);
    }
  });

  it('arrlit deep-nesting case coverage (200 cases)', () => {
    const r = rng(0xA110CA7E);
    for (let i = 0; i < 200; i++) {
      // Force arrlit in outer position.
      const n = 2 + Math.floor(r() * 3);
      const elems = new Uint32Array(n);
      for (let k = 0; k < n; k++) elems[k] = genTerm(r, vocab, AST, 2 + Math.floor(r() * 3));
      const h = Store.putArray(elems);
      const theta = closeTheta(genTheta(r, vocab, AST, 8));
      assert.strictEqual(apply(h, theta), apply_ref(h, theta),
        `arrlit drift at case ${i}`);
    }
  });

  it('ground term short-circuit (no metavars in term)', () => {
    // Pre-validates D: a term with no metavars should be an identity under
    // any θ. Production `apply` may or may not skip the scan — either way
    // the value must match the reference.
    const r = rng(0x12345678);
    const groundVocab = { atoms: vocab.atoms, freevars: vocab.freevars, metavars: [] };
    for (let i = 0; i < 300; i++) {
      const h = genTerm(r, groundVocab, AST, 2 + Math.floor(r() * 4));
      const theta = closeTheta(genTheta(r, vocab, AST, 10));
      // Ground term means θ cannot hit — result must equal `h`.
      assert.strictEqual(apply(h, theta), h, `ground miss at case ${i}`);
      assert.strictEqual(apply_ref(h, theta), h);
    }
  });
});
