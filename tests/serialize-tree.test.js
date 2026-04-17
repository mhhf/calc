/**
 * Tests for proof-tree/v1 serializer (lib/prover/serialize-tree.js).
 *
 * Fixtures are constructed directly from the ILL AST + Seq helpers so
 * the serializer can be exercised without driving the full prover.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const Store = require('../lib/kernel/store');
const Seq = require('../lib/kernel/sequent');
const { ProofTree, fromGoal, leaf } = require('../lib/prover/pt');
const {
  FORMAT_VERSION,
  serializeTree,
  serializeFormula,
  serializeSequent,
  computeNodeId,
  _newContext,
} = require('../lib/prover/serialize-tree');
const calculus = require('../lib/calculus');
const { GRADE_W } = require('../lib/engine/grades');

describe('serialize-tree / proof-tree/v1', () => {
  let AST;

  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
  });

  describe('format version', () => {
    it('exposes canonical version string', () => {
      assert.strictEqual(FORMAT_VERSION, 'proof-tree/v1');
    });

    it('top-level output carries format field', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const pt = leaf(s, 'id');
      const out = serializeTree(pt, { calculus: 'ill' });
      assert.strictEqual(out.format, 'proof-tree/v1');
    });
  });

  describe('formula AST', () => {
    it('freevar → { tag, name }', () => {
      const ctx = _newContext({});
      const key = serializeFormula(AST.freevar('A'), ctx);
      assert.deepStrictEqual(ctx.formulas[key], { tag: 'freevar', name: 'A' });
    });

    it('atom → { tag, name }', () => {
      const ctx = _newContext({});
      const key = serializeFormula(AST.atom('foo'), ctx);
      assert.deepStrictEqual(ctx.formulas[key], { tag: 'atom', name: 'foo' });
    });

    it('metavar → { tag, name }', () => {
      const ctx = _newContext({});
      const key = serializeFormula(AST.metavar('X'), ctx);
      assert.deepStrictEqual(ctx.formulas[key], { tag: 'metavar', name: 'X' });
    });

    it('one (nullary) → { tag }', () => {
      const ctx = _newContext({});
      const key = serializeFormula(AST.one(), ctx);
      assert.deepStrictEqual(ctx.formulas[key], { tag: 'one' });
    });

    it('zero (nullary) → { tag }', () => {
      const ctx = _newContext({});
      const key = serializeFormula(AST.zero(), ctx);
      assert.deepStrictEqual(ctx.formulas[key], { tag: 'zero' });
    });

    it('tensor(A, B) → { tag, args: [refA, refB] }', () => {
      const ctx = _newContext({});
      const key = serializeFormula(AST.tensor(AST.freevar('A'), AST.freevar('B')), ctx);
      const top = ctx.formulas[key];
      assert.strictEqual(top.tag, 'tensor');
      assert.strictEqual(top.args.length, 2);
      assert.deepStrictEqual(ctx.formulas[top.args[0]], { tag: 'freevar', name: 'A' });
      assert.deepStrictEqual(ctx.formulas[top.args[1]], { tag: 'freevar', name: 'B' });
    });

    it('loli(A, B) → { tag, args: [refA, refB] }', () => {
      const ctx = _newContext({});
      const key = serializeFormula(AST.loli(AST.freevar('A'), AST.freevar('B')), ctx);
      assert.strictEqual(ctx.formulas[key].tag, 'loli');
      assert.strictEqual(ctx.formulas[key].args.length, 2);
    });

    it('with(A, B) → { tag, args: [refA, refB] }', () => {
      const ctx = _newContext({});
      // `with` is a reserved word so we access it via the dynamic key.
      const key = serializeFormula(AST['with'](AST.freevar('A'), AST.freevar('B')), ctx);
      assert.strictEqual(ctx.formulas[key].tag, 'with');
      assert.strictEqual(ctx.formulas[key].args.length, 2);
    });

    it('oplus(A, B) → { tag, args: [refA, refB] }', () => {
      const ctx = _newContext({});
      const key = serializeFormula(AST.oplus(AST.freevar('A'), AST.freevar('B')), ctx);
      assert.strictEqual(ctx.formulas[key].tag, 'oplus');
      assert.strictEqual(ctx.formulas[key].args.length, 2);
    });

    it('bang(GRADE_W, A) → two-arg generic form (grade is an atom ref)', () => {
      const ctx = _newContext({});
      const h = Store.put('bang', [GRADE_W, AST.freevar('A')]);
      const key = serializeFormula(h, ctx);
      const top = ctx.formulas[key];
      assert.strictEqual(top.tag, 'bang');
      assert.strictEqual(top.args.length, 2);
      assert.deepStrictEqual(ctx.formulas[top.args[0]], { tag: 'atom', name: 'gw' });
      assert.deepStrictEqual(ctx.formulas[top.args[1]], { tag: 'freevar', name: 'A' });
    });

    it('monad({A}) → { tag, args: [refA] }', () => {
      const ctx = _newContext({});
      const key = serializeFormula(AST.monad(AST.freevar('A')), ctx);
      assert.strictEqual(ctx.formulas[key].tag, 'monad');
      assert.strictEqual(ctx.formulas[key].args.length, 1);
    });

    it('exists(body) with de Bruijn bound(0) inside', () => {
      const ctx = _newContext({});
      const body = Store.put('bound', [0n]);
      const key = serializeFormula(AST.exists(body), ctx);
      const top = ctx.formulas[key];
      assert.strictEqual(top.tag, 'exists');
      assert.strictEqual(top.args.length, 1);
      const inner = ctx.formulas[top.args[0]];
      assert.deepStrictEqual(inner, { tag: 'bound', value: '0' });
    });

    it('forall(body) with de Bruijn bound(1)', () => {
      const ctx = _newContext({});
      const body = Store.put('bound', [1n]);
      const key = serializeFormula(AST.forall(body), ctx);
      assert.strictEqual(ctx.formulas[key].tag, 'forall');
      assert.strictEqual(ctx.formulas[key].args.length, 1);
      assert.deepStrictEqual(
        ctx.formulas[ctx.formulas[key].args[0]],
        { tag: 'bound', value: '1' }
      );
    });

    it('binlit carries bigint value as decimal string', () => {
      const ctx = _newContext({});
      const h = Store.put('binlit', [42n]);
      const key = serializeFormula(h, ctx);
      assert.deepStrictEqual(ctx.formulas[key], { tag: 'binlit', value: '42' });
    });

    it('strlit carries string value', () => {
      const ctx = _newContext({});
      const h = Store.put('strlit', ['hello']);
      const key = serializeFormula(h, ctx);
      assert.deepStrictEqual(ctx.formulas[key], { tag: 'strlit', value: 'hello' });
    });

    it('arrlit → { tag, elements: [refs] }', () => {
      const ctx = _newContext({});
      const a = AST.freevar('A');
      const b = AST.freevar('B');
      const h = Store.putArray([a, b]);
      const key = serializeFormula(h, ctx);
      const top = ctx.formulas[key];
      assert.strictEqual(top.tag, 'arrlit');
      assert.strictEqual(top.elements.length, 2);
      assert.deepStrictEqual(ctx.formulas[top.elements[0]], { tag: 'freevar', name: 'A' });
      assert.deepStrictEqual(ctx.formulas[top.elements[1]], { tag: 'freevar', name: 'B' });
    });
  });

  describe('pool dedup', () => {
    it('repeated formula within one AST has a single pool entry', () => {
      const ctx = _newContext({});
      const a = AST.freevar('A');
      const key = serializeFormula(AST.tensor(a, a), ctx);
      const top = ctx.formulas[key];
      assert.strictEqual(top.args[0], top.args[1]); // same ref
      // Pool: just A and tensor(A, A).
      assert.strictEqual(Object.keys(ctx.formulas).length, 2);
    });

    it('formula shared between sequent and premise deduplicates', () => {
      const A = AST.freevar('A');
      const sLeaf = Seq.fromArrays([A], [], A);
      const p1 = leaf(sLeaf, 'id');
      const p2 = leaf(sLeaf, 'id');
      const root = new ProofTree({
        conclusion: Seq.fromArrays([], [], AST.tensor(A, A)),
        premises: [p1, p2],
        rule: 'tensor_r',
        proven: true,
      });
      const out = serializeTree(root, { calculus: 'ill' });
      // Pool: freevar(A) and tensor(A, A) — 2 entries total.
      assert.strictEqual(Object.keys(out.formulas).length, 2);
    });

    it('formula in antecedent and succedent maps to one pool entry', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const pt = leaf(s, 'id');
      const out = serializeTree(pt, { calculus: 'ill' });
      assert.strictEqual(Object.keys(out.formulas).length, 1);
      const [only] = Object.keys(out.formulas);
      assert.strictEqual(out.root.sequent.contexts.linear[0], only);
      assert.strictEqual(out.root.sequent.succedent, only);
    });
  });

  describe('sequent serialization', () => {
    it('preserves calculus-native context names (linear, cartesian)', () => {
      const ctx = _newContext({});
      const s = Seq.fromArrays([AST.freevar('A')], [AST.freevar('B')], AST.freevar('C'));
      const j = serializeSequent(s, ctx);
      const keys = Object.keys(j.contexts).sort();
      assert.deepStrictEqual(keys, ['cartesian', 'linear']);
      assert.strictEqual(j.contexts.linear.length, 1);
      assert.strictEqual(j.contexts.cartesian.length, 1);
      assert.ok(typeof j.succedent === 'string');
    });

    it('null succedent serializes as null', () => {
      const ctx = _newContext({});
      const j = serializeSequent(Seq.empty(), ctx);
      assert.strictEqual(j.succedent, null);
    });

    it('empty contexts serialize as empty arrays', () => {
      const ctx = _newContext({});
      const s = Seq.fromArrays([], [], AST.freevar('A'));
      const j = serializeSequent(s, ctx);
      assert.deepStrictEqual(j.contexts.linear, []);
      assert.deepStrictEqual(j.contexts.cartesian, []);
    });

    it('preserves multiset order within a context', () => {
      const ctx = _newContext({});
      const s = Seq.fromArrays(
        [AST.freevar('A'), AST.freevar('B'), AST.freevar('C')],
        [],
        AST.freevar('D')
      );
      const j = serializeSequent(s, ctx);
      // Three distinct refs, in the order we put them in.
      const linear = j.contexts.linear;
      assert.strictEqual(linear.length, 3);
      const names = linear.map((k) => ctx.formulas[k].name);
      assert.deepStrictEqual(names, ['A', 'B', 'C']);
    });
  });

  describe('tree serialization', () => {
    it('leaf: rule set, proven true, no premises', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const out = serializeTree(leaf(s, 'id'), { calculus: 'ill' });
      assert.strictEqual(out.root.rule, 'id');
      assert.strictEqual(out.root.proven, true);
      assert.deepStrictEqual(out.root.premises, []);
    });

    it('unproven goal: rule null, proven false', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('B'));
      const out = serializeTree(fromGoal(s), { calculus: 'ill' });
      assert.strictEqual(out.root.rule, null);
      assert.strictEqual(out.root.proven, false);
    });

    it('internal node: premises serialized recursively', () => {
      const s1 = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const s2 = Seq.fromArrays([AST.freevar('B')], [], AST.freevar('B'));
      const p1 = leaf(s1, 'id');
      const p2 = leaf(s2, 'id');
      const root = new ProofTree({
        conclusion: Seq.fromArrays(
          [AST.freevar('A'), AST.freevar('B')],
          [],
          AST.tensor(AST.freevar('A'), AST.freevar('B'))
        ),
        premises: [p1, p2],
        rule: 'tensor_r',
        proven: true,
      });
      const out = serializeTree(root, { calculus: 'ill' });
      assert.strictEqual(out.root.rule, 'tensor_r');
      assert.strictEqual(out.root.premises.length, 2);
      assert.strictEqual(out.root.premises[0].rule, 'id');
      assert.strictEqual(out.root.premises[1].rule, 'id');
      // Premises carry their own sequents referencing shared pool refs.
      assert.strictEqual(out.root.premises[0].sequent.contexts.linear.length, 1);
    });

    it('top-level fields: format, calculus, profile, formulas, root', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const out = serializeTree(leaf(s, 'id'), { calculus: 'ill', profile: 'default' });
      assert.strictEqual(out.format, 'proof-tree/v1');
      assert.strictEqual(out.calculus, 'ill');
      assert.strictEqual(out.profile, 'default');
      assert.ok(out.formulas && typeof out.formulas === 'object');
      assert.ok(out.root && typeof out.root === 'object');
    });

    it('profile defaults to "default" when omitted', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const out = serializeTree(leaf(s, 'id'), { calculus: 'ill' });
      assert.strictEqual(out.profile, 'default');
    });
  });

  describe('round-trip stability', () => {
    it('same ProofTree serialized twice → identical JSON bytes', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const pt = leaf(s, 'id');
      const a = JSON.stringify(serializeTree(pt, { calculus: 'ill' }));
      const b = JSON.stringify(serializeTree(pt, { calculus: 'ill' }));
      assert.strictEqual(a, b);
    });

    it('trees built independently from the same inputs → identical JSON', () => {
      // Rebuild everything from scratch: two different ProofTree objects
      // but structurally identical. Store content-addresses so the
      // underlying formula hashes are the same → pool keys match.
      const build = () => {
        const s = Seq.fromArrays(
          [AST.freevar('A'), AST.freevar('B')],
          [],
          AST.tensor(AST.freevar('A'), AST.freevar('B'))
        );
        const sLeaf = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
        return new ProofTree({
          conclusion: s,
          premises: [leaf(sLeaf, 'id'), leaf(sLeaf, 'id')],
          rule: 'tensor_r',
          proven: true,
        });
      };
      const j1 = JSON.stringify(serializeTree(build(), { calculus: 'ill' }));
      const j2 = JSON.stringify(serializeTree(build(), { calculus: 'ill' }));
      assert.strictEqual(j1, j2);
    });
  });

  describe('node ids', () => {
    it('structurally identical leaves get the same id', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const id1 = serializeTree(leaf(s, 'id'), { calculus: 'ill' }).root.id;
      const id2 = serializeTree(leaf(s, 'id'), { calculus: 'ill' }).root.id;
      assert.strictEqual(id1, id2);
    });

    it('different rule → different id', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const id1 = serializeTree(leaf(s, 'id'), { calculus: 'ill' }).root.id;
      const id2 = serializeTree(leaf(s, 'axiom'), { calculus: 'ill' }).root.id;
      assert.notStrictEqual(id1, id2);
    });

    it('different sequent → different id (within a single serialize call)', () => {
      // NOTE: Pool keys are positional per serialize() call in v1, so two
      // *isomorphic* trees serialized in separate calls collide. To test that
      // different sequents get different ids, build a parent tree that holds
      // both as premises so they share one pool and their refs diverge.
      const sLeafA = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const sLeafB = Seq.fromArrays([AST.freevar('B')], [], AST.freevar('B'));
      const sRoot = Seq.fromArrays(
        [],
        [],
        AST.tensor(AST.freevar('A'), AST.freevar('B')),
      );
      const parent = new ProofTree({
        conclusion: sRoot,
        premises: [leaf(sLeafA, 'id'), leaf(sLeafB, 'id')],
        rule: 'tensor_r',
        proven: true,
      });
      const { root } = serializeTree(parent, { calculus: 'ill' });
      const [pA, pB] = root.premises;
      assert.notStrictEqual(pA.id, pB.id);
    });

    it('different premise set → different id', () => {
      const sRoot = Seq.fromArrays([], [], AST.tensor(AST.freevar('A'), AST.freevar('B')));
      const sLeaf = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const p = leaf(sLeaf, 'id');
      const one = new ProofTree({
        conclusion: sRoot,
        premises: [p],
        rule: 'tensor_r',
        proven: true,
      });
      const two = new ProofTree({
        conclusion: sRoot,
        premises: [p, p],
        rule: 'tensor_r',
        proven: true,
      });
      const id1 = serializeTree(one, { calculus: 'ill' }).root.id;
      const id2 = serializeTree(two, { calculus: 'ill' }).root.id;
      assert.notStrictEqual(id1, id2);
    });

    it('node id is invariant under multiset permutation of a context', () => {
      // Same multiset, different order → computeNodeId sorts refs per
      // context, so the id is the same.
      const s1 = Seq.fromArrays(
        [AST.freevar('A'), AST.freevar('B')],
        [],
        AST.freevar('C')
      );
      const s2 = Seq.fromArrays(
        [AST.freevar('B'), AST.freevar('A')],
        [],
        AST.freevar('C')
      );
      const id1 = serializeTree(leaf(s1, 'id'), { calculus: 'ill' }).root.id;
      const id2 = serializeTree(leaf(s2, 'id'), { calculus: 'ill' }).root.id;
      assert.strictEqual(id1, id2);
    });

    it('id format: "n" followed by 8 hex characters', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const id = serializeTree(leaf(s, 'id'), { calculus: 'ill' }).root.id;
      assert.match(id, /^n[0-9a-f]{8}$/);
    });

    it('computeNodeId is pure (same inputs → same output)', () => {
      const seqJ = {
        contexts: { linear: ['f1'], cartesian: [] },
        succedent: 'f1',
      };
      const a = computeNodeId('id', seqJ, []);
      const b = computeNodeId('id', seqJ, []);
      assert.strictEqual(a, b);
    });
  });

  describe('meta + profile passthrough', () => {
    it('top-level meta is passed through verbatim', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const meta = { elapsed_ms: 12, source: 'fixture.md:42', nested: { k: 1 } };
      const out = serializeTree(leaf(s, 'id'), { calculus: 'ill', meta });
      assert.deepStrictEqual(out.meta, meta);
    });

    it('profileHash is emitted when provided', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const out = serializeTree(leaf(s, 'id'), {
        calculus: 'ill',
        profile: 'verified',
        profileHash: 'sha256:abc',
      });
      assert.strictEqual(out.profile, 'verified');
      assert.strictEqual(out.profileHash, 'sha256:abc');
    });

    it('profileHash is absent when not provided', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const out = serializeTree(leaf(s, 'id'), { calculus: 'ill' });
      assert.strictEqual('profileHash' in out, false);
    });
  });
});
