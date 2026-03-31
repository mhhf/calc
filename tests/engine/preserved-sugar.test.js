/**
 * Tests for preserved resource sugar ($prefix) — TODO_0149
 *
 * The $ prefix marks a linear resource as preserved across a forward rule:
 * $P on the antecedent desugars to P on both LHS and RHS.
 */
const { describe, it } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine');
const { parseExpr, desugarPreserved } = require('../../lib/engine/convert');
const forward = require('../../lib/engine/forward');
const { ILL_CONNECTIVES } = require('../../lib/engine/ill/connectives');
const { resolveConnectives, flattenAntecedent, compileRule } = require('../../lib/engine/compile');

const ILL_RC = resolveConnectives(ILL_CONNECTIVES);

// Helper: compile a forward rule from a formula string
function compileFromExpr(name, exprStr) {
  const h = parseExpr(exprStr);
  const desugared = desugarPreserved(h);
  const [ante, conseq] = Store.children(desugared);
  return compileRule({ name, hash: desugared, antecedent: ante, consequent: conseq },
    { connectives: ILL_CONNECTIVES });
}

describe('Preserved resource sugar ($prefix)', { timeout: 10000 }, () => {

  // ── Parsing ────────────────────────────────────────────────────────────

  describe('parsing', () => {
    it('parses $atom as preserved(atom)', () => {
      const h = parseExpr('$foo');
      assert.strictEqual(Store.tag(h), 'preserved');
      const inner = Store.child(h, 0);
      // foo is lowercase → atom('foo')
      assert.strictEqual(Store.tag(inner), 'atom');
      assert.strictEqual(Store.child(inner, 0), 'foo');
    });

    it('parses $pred X as preserved(pred(X))', () => {
      const h = parseExpr('$bytecode BC');
      assert.strictEqual(Store.tag(h), 'preserved');
      const inner = Store.child(h, 0);
      assert.strictEqual(Store.tag(inner), 'bytecode');
    });

    it('parses $P in tensor context', () => {
      // Use predicate application so tags are meaningful
      const h = parseExpr('$bytecode BC * pc PC');
      assert.strictEqual(Store.tag(h), 'tensor');
      assert.strictEqual(Store.tag(Store.child(h, 0)), 'preserved');
      assert.strictEqual(Store.tag(Store.child(h, 1)), 'pc');
    });
  });

  // ── Desugaring ─────────────────────────────────────────────────────────

  describe('desugaring', () => {
    it('desugars single $P to P on both LHS and RHS', () => {
      // Use predicate application (bytecode BC) so tags are predicate names
      const sugared = parseExpr('$bytecode BC * pc PC -o { gas G }');
      const desugared = desugarPreserved(sugared);

      const ante = Store.child(desugared, 0);
      const anteFlat = flattenAntecedent(ante, ILL_RC);
      const anteTags = anteFlat.linear.map(h => Store.tag(h));
      assert(anteTags.includes('bytecode'), 'antecedent should contain bytecode');
      assert(anteTags.includes('pc'), 'antecedent should contain pc');

      // Consequent should have bytecode injected alongside gas
      const conseq = Store.child(desugared, 1);
      const body = Store.child(conseq, 0);
      const conseqFlat = flattenAntecedent(body, ILL_RC);
      const conseqTags = conseqFlat.linear.map(h => Store.tag(h));
      assert(conseqTags.includes('bytecode'), 'consequent should contain bytecode (injected)');
      assert(conseqTags.includes('gas'), 'consequent should contain gas (original)');
    });

    it('desugars multiple $P resources', () => {
      const sugared = parseExpr('$bytecode BC * $gas G * pc PC -o { stack S }');
      const desugared = desugarPreserved(sugared);

      const ante = Store.child(desugared, 0);
      const anteFlat = flattenAntecedent(ante, ILL_RC);
      assert.strictEqual(anteFlat.linear.length, 3);

      const conseq = Store.child(desugared, 1);
      const body = Store.child(conseq, 0);
      const conseqFlat = flattenAntecedent(body, ILL_RC);
      const conseqTags = conseqFlat.linear.map(h => Store.tag(h));
      assert(conseqTags.includes('bytecode'), 'consequent should have bytecode');
      assert(conseqTags.includes('gas'), 'consequent should have gas');
      assert(conseqTags.includes('stack'), 'consequent should have stack');
    });

    it('preserves hash identity: desugared P == longhand P', () => {
      // Single preserved resource: hash of P in ante should equal hash of P in conseq
      const sugared = parseExpr('$bytecode BC * pc PC -o { pc PC\' }');
      const desugared = desugarPreserved(sugared);

      const ante = Store.child(desugared, 0);
      const anteFlat = flattenAntecedent(ante, ILL_RC);
      const bytecodeInAnte = anteFlat.linear.find(h => Store.tag(h) === 'bytecode');

      const conseq = Store.child(desugared, 1);
      const body = Store.child(conseq, 0);
      const conseqFlat = flattenAntecedent(body, ILL_RC);
      const bytecodeInConseq = conseqFlat.linear.find(h => Store.tag(h) === 'bytecode');

      assert.strictEqual(bytecodeInAnte, bytecodeInConseq,
        'preserved resource should have identical hash on both sides (content-addressed)');
    });

    it('no-op when no $ present', () => {
      const h = parseExpr('foo * bar -o { baz }');
      const desugared = desugarPreserved(h);
      assert.strictEqual(h, desugared, 'should return same hash when no $ present');
    });

    it('no-op for non-loli formulas', () => {
      const h = parseExpr('foo * bar');
      const desugared = desugarPreserved(h);
      assert.strictEqual(h, desugared, 'should return same hash for non-forward formula');
    });
  });

  // ── Error cases ────────────────────────────────────────────────────────

  describe('errors', () => {
    it('rejects $!P (preserved persistent)', () => {
      const h = parseExpr('$!foo * bar -o { baz }');
      assert.throws(() => desugarPreserved(h), /\$!P is not allowed/);
    });

    it('rejects $ in consequent', () => {
      // Manually construct: preserved(foo) * bar -o { preserved(baz) }
      // Need preserved in antecedent too, since validation only runs when
      // antecedent has preserved items (otherwise it's a no-op early return)
      const foo = Store.put('atom', ['foo']);
      const bar = Store.put('atom', ['bar']);
      const baz = Store.put('atom', ['baz']);
      const ante = Store.put('tensor', [Store.put('preserved', [foo]), bar]);
      const conseq = Store.put('monad', [Store.put('preserved', [baz])]);
      const body = Store.put('loli', [ante, conseq]);
      assert.throws(() => desugarPreserved(body), /consequent/);
    });
  });

  // ── Compilation ────────────────────────────────────────────────────────

  describe('compilation', () => {
    it('produces identical compiled rule as longhand', () => {
      // Sugared: $bytecode BC * pc PC -o { pc PC' }
      const sugared = compileFromExpr('sugared',
        '$bytecode BC * pc PC -o { pc PC\' }');

      // Longhand: bytecode BC * pc PC -o { bytecode BC * pc PC' }
      const longhand = compileFromExpr('longhand',
        'bytecode BC * pc PC -o { bytecode BC * pc PC\' }');

      // Same antecedent structure
      assert.strictEqual(sugared.antecedent.linear.length, longhand.antecedent.linear.length,
        'same number of antecedent linear resources');

      // Same consequent structure
      assert.strictEqual(sugared.consequent.linear.length, longhand.consequent.linear.length,
        'same number of consequent linear resources');

      // Both should detect bytecode as preserved
      const sugaredPreservedTags = sugared.preserved.map(h => Store.tag(h));
      const longhandPreservedTags = longhand.preserved.map(h => Store.tag(h));
      assert.deepStrictEqual(sugaredPreservedTags, longhandPreservedTags,
        'same preserved resources detected by analyzeDeltas');
    });

    it('preserved resources appear in compiled.preserved', () => {
      const compiled = compileFromExpr('test',
        '$bytecode BC * gas GAS -o { gas GAS\' }');

      assert(compiled.preserved.length >= 1, 'should have at least 1 preserved');
      const preservedTags = compiled.preserved.map(h => Store.tag(h));
      assert(preservedTags.includes('bytecode'), 'bytecode should be preserved');
    });
  });

  // ── Engine execution ───────────────────────────────────────────────────

  describe('engine execution', () => {
    it('preserved resource survives rule firing', () => {
      // Use a simple rule without existentials for clean testing
      const simpleCompiled = compileFromExpr('simple',
        '$keeper * consumed -o { produced }');

      const keeper = parseExpr('keeper');
      const consumed = parseExpr('consumed');
      const produced = parseExpr('produced');

      const simpleState = forward.createState(
        { [keeper]: 1, [consumed]: 1 },
        {}
      );

      const result = forward.run(simpleState, [simpleCompiled]);

      assert(result.quiescent, 'should reach quiescence');
      assert.strictEqual(result.steps, 1, 'should fire once');
      assert.strictEqual(result.state.linear[keeper], 1,
        'preserved resource should still be present');
      assert.strictEqual(result.state.linear[produced], 1,
        'produced resource should be present');
      assert(!result.state.linear[consumed],
        'consumed resource should be gone');
    });
  });

  // ── Integration: EVM file loading ──────────────────────────────────────

  describe('EVM integration', { timeout: 30000 }, () => {
    it('loads evm.ill with $ syntax and executes', async () => {
      const calc = await mde.load(
        path.join(__dirname, '../../calculus/ill/programs/multisig.ill')
      );

      const state = mde.decomposeQuery(calc.queries.get('symex'));
      const result = calc.exec(state, { maxSteps: 10, trace: true });

      assert(result.steps >= 5,
        `Expected >= 5 steps, got ${result.steps}. Trace: ${result.trace?.join(' → ')}`);
    });
  });
});
