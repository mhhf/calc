/**
 * SELL Grade Constants — {0, 1, ω} semiring labels.
 *
 * SELL (Subexponential Linear Logic, Nigam-Miller PPDP 2009) parameterizes
 * the exponential modality: `!_a A` where `a` is drawn from a label preorder.
 * Our label set is QTT's {0, 1, ω} semiring (Atkey LICS 2018) with the
 * V-shaped partial order: {0 ≤ ω, 1 ≤ ω, 0 ∥ 1}.
 *
 * Grades are content-addressed atoms in the Store:
 *   GRADE_0 = atom('g0')  — compile-time (composed away before runtime)
 *   GRADE_W = atom('gw')  — persistent (weakening + contraction)
 *
 * Grade-1 (linear) is implicit — bare formula without bang wrapper.
 * No GRADE_1 constant is stored in the tree. This matches SELL convention
 * where the identity subexponential is implicit.
 *
 * Grade-0 non-interference: grade-0 resources have no runtime effect
 * (Choudhury et al. POPL 2021, Lemma 6.2; THY_0015 for our staging proof).
 * Rules with grade-0 patterns are filtered out before runtime execution.
 */

'use strict';

const Store = require('../kernel/store');

const exp = {
  GRADE_0: Store.put('atom', ['g0']),
  GRADE_W: Store.put('atom', ['gw']),
};

// Re-register after Store.clear() so IDs stay valid for destructured captures.
// After clear, Store assigns IDs sequentially starting from 1 — since this hook
// runs first (registered at module load), grades always get IDs 1 and 2.
Store.onClear(() => {
  exp.GRADE_0 = Store.put('atom', ['g0']);
  exp.GRADE_W = Store.put('atom', ['gw']);
});

module.exports = exp;
