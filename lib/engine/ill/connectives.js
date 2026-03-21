/**
 * ILL Connective Table
 *
 * Layer: ILL (Intuitionistic Linear Logic)
 *
 * Maps each ILL connective tag to its structural properties:
 * { category, arity, polarity }. Mirrors the @category and @polarity
 * annotations in ill.calc — this constant is the engine's view of
 * the same data until the engine loads .calc files directly.
 *
 * The engine never queries tag names — it queries structural categories.
 * compile.js:resolveConnectives() derives tag lookups from this table.
 *
 * For a new calculus: create a parallel table with that calculus's
 * connective tags and their structural properties.
 */

const ILL_CONNECTIVES = {
  tensor: { category: 'multiplicative', arity: 2, polarity: 'positive' },
  loli:   { category: 'multiplicative', arity: 2, polarity: 'negative' },
  bang:   { category: 'exponential',    arity: 1 },
  one:    { category: 'multiplicative', arity: 0 },
  monad:  { category: 'monad',          arity: 1 },
  oplus:  { category: 'additive',       arity: 2, polarity: 'positive' },
  with:   { category: 'additive',       arity: 2, polarity: 'negative' },
  exists: { category: 'quantifier',     arity: 1, polarity: 'positive' },
  zero:   { category: 'additive',       arity: 0 },
};

module.exports = { ILL_CONNECTIVES };
