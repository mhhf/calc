/**
 * FactSet label-column mode (THY_0024, TODO_0278 B2).
 *
 * Rows are (innerHash, stampId, count): the inner column IS group(k)
 * (time-stable content addresses), the stamp column rides beside it,
 * multiplicity is run-length. The public fact handle is the packed
 * 52-bit ref. Pins:
 *   - insert/remove/count round trip by ref; rows dedup by (inner, sid)
 *   - group order: stamp-major (table cmp), inner-hash tiebreak
 *   - Zobrist is content-derived: insertion order and table-id HISTORY
 *     must not affect the state hash (rider 2 — E5 splits hash equal)
 *   - undo: 5-int arena records restore content and hash exactly
 *   - snapshot: independent columns, SHARED stamp table
 *   - boundary: fromObject decodes at(A, t) / bare facts; toObject mints
 *     the same at-encoding back (representation invisible outside)
 *   - fences: inner id and stamp id caps throw loudly
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import { FactSet, Arena, fromObject, toObject } from '../../lib/engine/fact-set.js';
import { packRef, refInner, refStamp, INNER_CAP } from '../../lib/engine/fact-set.js';
import { StampTable } from '../../lib/timed/labels.js';
import tillConfig, { tillGrades } from '../../calculus/till/calculus-config.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import { ratParts } from '../../lib/kernel/rat-term.js';

const policy = { ...tillConfig.factSetPolicy, labels: tillGrades.values, stampTable: StampTable };
const atom = (n) => Store.put('atom', [n]);
const mk = () => new FactSet(Store.TAG_NAMES.length, policy);
const T = (fs, n, d = 1n) => fs.stamps.intern([BigInt(n), d]);
const gid = (fs, inner) => fs._key(Store.tagId(inner), packRef(inner, 0));

describe('FactSet label columns', () => {
  it('inserts rows deduped by (inner, sid) with run-length counts', () => {
    const fs = mk();
    const w = atom('wood');
    const t3 = T(fs, 3);
    const ref = packRef(w, t3);
    fs.insert(Store.tagId(w), ref, null, 2);
    fs.insert(Store.tagId(w), ref, null, 3);
    assert.equal(fs.count(Store.tagId(w), ref), 5);
    assert.equal(fs.total, 5);
    assert.equal(fs.groupLen(gid(fs, w)), 1);
    const other = packRef(w, T(fs, 4));
    fs.insert(Store.tagId(w), other, null, 1);
    assert.equal(fs.groupLen(gid(fs, w)), 2);
    assert.equal(fs.count(Store.tagId(w), other), 1);
    fs.remove(Store.tagId(w), ref, null, 4);
    assert.equal(fs.count(Store.tagId(w), ref), 1);
    fs.remove(Store.tagId(w), ref, null, 1);
    assert.equal(fs.count(Store.tagId(w), ref), 0);
    assert.equal(fs.groupLen(gid(fs, w)), 1);
  });

  it('orders groups stamp-major with inner tiebreak; columns stay parallel', () => {
    const fs = mk();
    const a = atom('pa');
    const k = gid(fs, a);
    const later = packRef(a, T(fs, 9));
    const early = packRef(a, T(fs, 1));
    const mid = packRef(a, T(fs, 5, 2n));
    fs.insert(0, later, null, 1);
    fs.insert(0, early, null, 2);
    fs.insert(0, mid, null, 1);
    const inner = fs.group(k);
    const sids = fs.groupSids(k);
    const cnts = fs.groupCounts(k);
    const vals = [...sids].map(s => fs.stamps.value(s)[0] * 2n / fs.stamps.value(s)[1]);
    assert.deepEqual([...inner], [a, a, a]);
    assert.deepEqual(vals, [2n, 5n, 18n]);          // 1 < 5/2 < 9 (doubled)
    assert.deepEqual([...cnts], [2, 1, 1]);
  });

  it('state hash is content-derived: order- and id-history-independent', () => {
    const w = atom('wood'), s = atom('stone');
    const build = (skewTable, order) => {
      const fs = mk();
      if (skewTable) for (let i = 0; i < 7; i++) T(fs, 1000 + i);  // burn ids
      const rows = [
        [w, 3n, 2], [w, 7n, 1], [s, 3n, 4],
      ];
      for (const i of order) {
        const [inner, t, n] = rows[i];
        fs.insert(Store.tagId(inner), packRef(inner, T(fs, t)), null, n);
      }
      return fs.hash;
    };
    const h1 = build(false, [0, 1, 2]);
    const h2 = build(true, [2, 1, 0]);
    assert.equal(h1, h2);
    assert.notEqual(h1, build(false, [0, 1]));       // content actually matters
  });

  it('arena undo restores rows and hash through 5-int records', () => {
    const fs = mk();
    const w = atom('wood');
    const r1 = packRef(w, T(fs, 1));
    const r2 = packRef(w, T(fs, 2));
    fs.insert(0, r1, null, 3);
    const h0 = fs.hash, t0 = fs.total;
    const arena = new Arena(64);
    const cp = arena.checkpoint();
    fs.insert(0, r2, arena, 2);
    fs.remove(0, r1, arena, 3);
    assert.notEqual(fs.hash, h0);
    fs.undo(arena, cp);
    assert.equal(fs.hash, h0);
    assert.equal(fs.total, t0);
    assert.equal(fs.count(0, r1), 3);
    assert.equal(fs.count(0, r2), 0);
  });

  it('snapshot copies columns independently and shares the stamp table', () => {
    const fs = mk();
    const w = atom('wood');
    const r = packRef(w, T(fs, 4));
    fs.insert(0, r, null, 2);
    const snap = fs.snapshot();
    assert.equal(snap.stamps, fs.stamps);
    fs.remove(0, r, null, 1);
    assert.equal(fs.count(0, r), 1);
    assert.equal(snap.count(0, r), 2);
    assert.equal(snap.hash === fs.hash, false);
  });

  it('fromObject/toObject: the at-encoding is the boundary format', () => {
    const w = atom('wood');
    const stamped = Store.put('at', [w, putRat(5n, 2n)]);
    const state = fromObject({ [stamped]: 3, [w]: 1 }, {}, policy);
    assert.ok(state.linear._lab);
    const k = gid(state.linear, w);
    assert.equal(state.linear.groupLen(k), 2);        // unit row + 5/2 row
    const back = toObject(state);
    assert.equal(back.linear[stamped], 3);
    const unitStamped = Store.put('at', [w, putRat(0n, 1n)]);
    assert.equal(back.linear[unitStamped], 1);        // bare fact reads as @0 (D11)
    const again = fromObject(back.linear, back.persistent, policy);
    assert.equal(again.linear.hash, state.linear.hash);
  });

  it('ref decode round trips and the inner fence is loud', () => {
    const w = atom('wood');
    const fs = mk();
    const sid = T(fs, 123);
    const ref = packRef(w, sid);
    assert.equal(refInner(ref), w);
    assert.equal(refStamp(ref), sid);
    assert.throws(() => fs.insert(0, packRef(INNER_CAP + 1, 0), null, 1), /inner/);
  });
});
