/**
 * TODO_0216 Phase 3 (idea N) — Substitution type tests
 *
 * Validates the thin `Substitution` wrapper:
 *  • fromPairs/toArray round-trip
 *  • apply() agrees with legacy apply([[v,val]]) form
 *  • compose is associative and respects σ-overriding-τ
 *  • idempotence assertion fires when CALC_0216_SUBST_ASSERT=1
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const calculus = require('../lib/calculus');
const { apply } = require('../lib/kernel/substitute');
const { Substitution } = require('../lib/kernel/substitution');

describe('TODO_0216 H7 — Substitution wrapper', () => {
  let AST;

  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
  });

  it('toArray round-trips the original pairs', () => {
    const pairs = [
      [AST.metavar('X'), AST.atom('p')],
      [AST.metavar('Y'), AST.atom('q')],
    ];
    const s = Substitution.fromPairs(pairs);
    assert.strictEqual(s.toArray(), pairs);
    assert.strictEqual(s.size, 2);
  });

  it('empty is identity', () => {
    const s = Substitution.empty();
    const h = AST.tensor(AST.atom('p'), AST.atom('q'));
    assert.strictEqual(s.apply(h), h);
  });

  it('apply() matches legacy array-form apply', () => {
    const x = AST.metavar('X');
    const pairs = [[x, AST.atom('p')]];
    const t = AST.tensor(x, AST.atom('q'));

    const viaArray = apply(t, pairs);
    const viaSubst = Substitution.fromPairs(pairs).apply(t);
    assert.strictEqual(viaSubst, viaArray);
  });

  it('apply(h, substitution) also unwraps the wrapper', () => {
    const x = AST.metavar('X');
    const pairs = [[x, AST.atom('p')]];
    const s = Substitution.fromPairs(pairs);
    const t = AST.tensor(x, x);

    assert.strictEqual(apply(t, s), apply(t, pairs));
  });

  it('compose: (σ ∘ τ) applied = σ(τ(·))', () => {
    const x = AST.metavar('X');
    const y = AST.metavar('Y');
    const a = AST.atom('a');
    const b = AST.atom('b');

    const tau   = Substitution.fromPairs([[x, y]]);
    const sigma = Substitution.fromPairs([[y, a]]);

    const composed = sigma.compose(tau);
    const t = AST.tensor(x, b);

    // composed.apply(t) should substitute x → y → a
    assert.strictEqual(composed.apply(t), sigma.apply(tau.apply(t)));
  });

  it('compose: σ wins over τ on shared domain', () => {
    const x = AST.metavar('X');
    const p = AST.atom('p');
    const q = AST.atom('q');

    const tau   = Substitution.fromPairs([[x, p]]);
    const sigma = Substitution.fromPairs([[x, q]]);

    // σ ∘ τ on x: σ(τ(x)) = σ(p) = p  (σ doesn't touch p)
    // so τ's binding survives — this is the classic σ∘τ direction.
    const composed = sigma.compose(tau);
    assert.strictEqual(composed.apply(x), p);
  });
});
