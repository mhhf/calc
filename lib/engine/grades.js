/**
 * SELL Grade Labels — {0, 1, ω} semiring.
 *
 * SELL (Subexponential Linear Logic, Nigam-Miller PPDP 2009) parameterizes
 * the exponential modality: `!_a A` where `a` is drawn from a label preorder.
 * Our label set is QTT's {0, 1, ω} semiring (Atkey LICS 2018) with the
 * V-shaped partial order: {0 ≤ ω, 1 ≤ ω, 0 ∥ 1}.
 *
 * Grades are content-addressed atoms in the Store:
 *   grade0() = atom('g0')  — compile-time (composed away before runtime)
 *   gradeW() = atom('gw')  — persistent (weakening + contraction)
 *
 * They are RECOMPUTED on demand, never captured as module-level Store-ID
 * constants. Content-addressing makes `Store.put` idempotent, so a call always
 * returns the current correct ID for the atom — even after the Store is
 * reindexed by clear() or by the snapshot → compact → restore cache round trip.
 * A captured raw ID would go stale there and silently alias a foreign node
 * (TODO_0267); not capturing removes that whole hazard — and the onClear
 * re-pinning hook the captured constants used to require.
 *
 * All uses are on cold parse/compose paths; the extra dedup lookup is free.
 * The one hot site (loli-drain) hoists gradeW() to a local across its loop —
 * within a single execution the Store is never reindexed, so the ID is stable.
 *
 * Grade-1 (linear) is implicit — bare formula without bang wrapper.
 * No grade-1 label is stored in the tree. This matches SELL convention
 * where the identity subexponential is implicit.
 *
 * Grade-0 non-interference: grade-0 resources have no runtime effect
 * (Choudhury et al. POPL 2021, Lemma 6.2; THY_0015 for our staging proof).
 * Rules with grade-0 patterns are filtered out before runtime execution.
 */

'use strict';

import Store from '../kernel/store.js';

export const grade0 = () => Store.put('atom', ['g0']);
export const gradeW = () => Store.put('atom', ['gw']);

export default { grade0, gradeW };
