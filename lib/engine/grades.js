/**
 * SELL Grade Constants — {0, 1, ω} semiring labels.
 *
 * Grades are content-addressed atoms in the Store:
 *   GRADE_0 = atom('g0')  — compile-time (composed away before runtime)
 *   GRADE_W = atom('gw')  — persistent (weakening + contraction)
 *
 * Grade-1 (linear) is implicit — bare formula without bang wrapper.
 * No GRADE_1 constant is stored in the tree.
 *
 * See: Nigam & Miller (PPDP 2009), Atkey (LICS 2018)
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
