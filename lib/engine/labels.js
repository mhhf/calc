/**
 * StampTable — per-State label interning over a calculus value algebra
 * (THY_0024 "Graded Labelled States", TODO_0278 B2).
 *
 * The labelled state stores rows (innerHash, stampId, count): the formula
 * hash is a time-stable content address; the label lives HERE, as a small
 * id into this table. Entries carry the exact value, a cached monotone
 * float (the order fast path), a value-derived Zobrist mix (rider 2: ids
 * are history-dependent — E5 horizon-split states must hash equal — so
 * hashes derive from values, never ids), and a memoized reified term.
 * term() is the lazy internalization boundary: only labels a rule
 * actually binds or computes with ever touch the Store.
 *
 * The table is session-local and MORTAL: rebase rebuild-swaps the state
 * into a fresh table (timed.js _rebaseNow) — O(live rows), zero term
 * allocation, dead entries die with the old table. Contrast the
 * append-only Store arena, where every (inner × stamp) pair used to
 * intern an immortal node.
 *
 * Value algebra contract (calculus-supplied, e.g. tillGrades.values):
 *   unit          — the ⊗-unit value (the default label, D11)
 *   canon(v)      — canonical representative (interning equality)
 *   parse(h) → v  — ground stamp term → value (canonStamp folded in)
 *   reify(v) → h  — value → term
 *   cmp / add / sub — exact order + effect monoid (sub signed, for shifts)
 *   merge         — optional ⊔ tensor-merge of co-consumed labels
 *                   (grade-algebra.md): 'join' (= default, max by cmp —
 *                   the float-fast id path) or a value-level function
 *   prunes        — optional ⊕ order-prune: 'geq' (= default,
 *                   cmp(p, b) >= 0) or a value-level function
 *   float(v)      — monotone rounding; NaN = exact-only
 *   mix(v) → i32  — value-derived hash contribution
 *   key(v)        — Map key for a CANONICAL value
 *   scale(v, n)   — v·n for n ∈ ℕ (acceleration: period × cycles)
 *   floorDiv(a,b) — ⌊a/b⌋ as a Number, b > 0, a ≥ 0 (acceleration: how
 *                   many periods fit a span — the Archimedean question)
 */

const STAMP_BITS = 23;
const STAMP_CAP = 1 << STAMP_BITS;      // 8,388,608 distinct labels per table
const INNER_CAP = 2 ** 29;              // packRef fence on the inner id

/** Packed 52-bit fact ref: (innerHash, stampId) as one float64-exact
 *  number — Map-keyable, and splittable into two ints for arena records. */
const packRef = (inner, sid) => inner * STAMP_CAP + sid;
const refInner = (ref) => Math.floor(ref / STAMP_CAP);
const refStamp = (ref) => ref % STAMP_CAP;

/** Resolve a ⊔/⊕ algebra slot: undefined or the canonical symbolic name
 *  → null (the table's fast id-level realization); a function → itself;
 *  anything else (a typo'd string, say) is a loud config error. */
function _slot(name, v, canonical) {
  if (v === undefined || v === canonical) return null;
  if (typeof v === 'function') return v;
  throw new Error(`StampTable: alg.${name} must be '${canonical}' or a value-level function (got ${JSON.stringify(v)})`);
}

class StampTable {
  constructor(alg) {
    this.alg = alg;
    this.ids = new Map();               // alg.key(canonical value) -> id
    this.vals = [];
    this.floats = [];
    this.mixes = [];
    this.terms = [];                    // reified term hash | -1 (lazy)
    // ⊔/⊕ slot resolution (grade-algebra.md; TODO_0284 P1), once per
    // table: a symbolic slot names a canonical realization the table
    // runs on its float-fast id cmp (null sentinel below); a function
    // slot is a custom value-level realization; anything else is loud.
    this._mergeFn = _slot('merge', alg.merge, 'join');
    this._prunesFn = _slot('prunes', alg.prunes, 'geq');
    this.unitId = this.intern(alg.unit);   // always id 0
  }

  get size() { return this.vals.length; }

  intern(v) {
    if (this.alg.canon) v = this.alg.canon(v);
    const k = this.alg.key(v);
    let id = this.ids.get(k);
    if (id === undefined) {
      id = this.vals.length;
      if (id >= STAMP_CAP) {
        throw new Error(`StampTable overflow: ${id} distinct labels — raise the rebase/compaction cadence (STAMP_BITS=${STAMP_BITS})`);
      }
      this.ids.set(k, id);
      this.vals.push(v);
      this.floats.push(this.alg.float(v));
      this.mixes.push(this.alg.mix(v));
      this.terms.push(-1);
    }
    return id;
  }

  /** Ground stamp TERM → id (parse folds calculus canonicalization). */
  internTerm(h) { return this.intern(this.alg.parse(h)); }

  value(id) { return this.vals[id]; }
  float(id) { return this.floats[id]; }
  mix(id) { return this.mixes[id]; }

  /** The reification boundary: label → term, memoized per entry. */
  term(id) {
    let t = this.terms[id];
    if (t === -1) { t = this.alg.reify(this.vals[id]); this.terms[id] = t; }
    return t;
  }

  /** Total order by cached float, exact fallback (monotone rounding —
   *  floats differing decides; ties and NaN sentinels go exact). */
  cmp(a, b) {
    if (a === b) return 0;
    const fa = this.floats[a], fb = this.floats[b];
    if (fa < fb) return -1;
    if (fa > fb) return 1;
    return this.alg.cmp(this.vals[a], this.vals[b]);
  }

  /** Effect composition id ⊗ value → id (the firing law's output label). */
  compose(id, dv) {
    if (this.alg.cmp(dv, this.alg.unit) === 0) return id;
    return this.intern(this.alg.add(this.vals[id], dv));
  }

  /** ⊔ tensor-merge on ids — co-consumed labels join into one activation
   *  (grade-algebra.md; TODO_0284 P1). 'join' (the order-class C4 join,
   *  also the default) runs as max by the float-fast id cmp — the old
   *  inline code path, intern-free. A function slot is a custom
   *  value-level merge: an argument returned by reference keeps its id;
   *  a value-creating merge (e.g. usage `+`) interns its result.
   *  Distinct ids never compare equal (canonical interning), so join
   *  tie-bias is unobservable here. */
  merge(a, b) {
    const m = this._mergeFn;
    // The a === b identity shortcut belongs to the JOIN realization only:
    // a non-idempotent function slot (usage +, weight ·) must run even on
    // equal ids — w ⊔ w = w², not w (P3b, the first non-idempotent
    // instance, caught this).
    if (m === null) return a === b ? a : (this.cmp(a, b) > 0 ? a : b);   // 'join'
    const v = m(this.vals[a], this.vals[b]);
    if (v === this.vals[a]) return a;
    if (v === this.vals[b]) return b;
    return this.intern(v);
  }

  /** ⊕ order-class prune on ids: is a partial match at grade p already
   *  dead against best b? 'geq' (the contract's blessed realization,
   *  also the default) is cmp(p, b) >= 0 on the float-fast id cmp —
   *  `>=` keeps the FIRST match at equal grade (the FIFO half of
   *  timed.js's invariant pair). A function slot unpacks values. */
  prunes(p, b) {
    const f = this._prunesFn;
    return f === null ? this.cmp(p, b) >= 0 : f(this.vals[p], this.vals[b]);
  }

  // NOTE (design record): a uniform in-place shiftAll(−B) was considered
  // for rebase and REJECTED — a shifted value can collide with the unit
  // (a row at exactly stamp B), breaking the table's value-injectivity
  // that value-derived hashing and row dedup depend on. Rebase instead
  // REBUILD-SWAPS into a fresh table (timed.js _rebaseNow): interning
  // merges collisions, dead entries die with the old table.

  /** Test hook: pretend the table already holds n entries (fence tests). */
  _forceSize(n) { this.vals.length = n; }
}

export { StampTable, packRef, refInner, refStamp, STAMP_BITS, STAMP_CAP, INNER_CAP };
export default { StampTable, packRef, refInner, refStamp, STAMP_BITS, STAMP_CAP, INNER_CAP };
