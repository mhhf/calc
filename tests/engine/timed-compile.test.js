/**
 * Timed compile + match — TODO_0265 Phase 3.
 *
 * compileRule strips after/before wrappers into slot-compiled
 * rule.windows guard metadata and readPreserved wrappers into
 * rule.readOnly; the matcher routes read patterns through the reserved
 * path UNCONDITIONALLY (reading is semantics, not the $-optimization):
 * the fact is matched, never consumed, never re-produced.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import forward from '../../lib/engine/forward.js';
import { explore } from '../../lib/engine/explore.js';
import { compileRule } from '../../lib/engine/compile.js';
import { illConnectives } from '../../lib/engine/ill/connectives.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import { makeMatchOpts } from './_match-opts.js';
import { gradeW } from '../../lib/engine/grades.js';

const atom = (n) => Store.put('atom', [n]);
const mv = (n) => Store.put('metavar', [n]);
const t2 = (a, b) => Store.put('tensor', [a, b]);
const loli = (a, b) => Store.put('loli', [a, b]);
const monad = (b) => Store.put('monad', [b]);

function compile(name, ante, conseq) {
  return compileRule(
    { name, hash: loli(ante, conseq), antecedent: ante, consequent: conseq },
    { connectives: illConnectives() });
}

describe('compileRule: window stripping', () => {
  it('after/before leave the pattern list into slot-compiled rule.windows', () => {
    const pat = Store.put('at', [atom('food'), mv('Q')]);
    const ante = t2(t2(pat, Store.put('after', [mv('Q')])),
                    Store.put('before', [putRat(7n, 2n)]));
    const rule = compile('spoil', ante, monad(atom('done')));

    assert.deepEqual(rule.antecedent.linear, [pat], 'windows are not patterns');
    assert.deepEqual(rule.windows.after, [{ slot: rule.metavarSlots[mv('Q')] }]);
    assert.deepEqual(rule.windows.before, [{ ground: putRat(7n, 2n) }]);
    assert.equal(rule.readOnly, undefined);
  });

  it('unbound window variable is a compile error', () => {
    const ante = t2(atom('a'), Store.put('after', [mv('W')]));
    assert.throws(() => compile('bad', ante, monad(atom('b'))), /not bound/);
  });

  it('window variable bound ONLY in the consequent is also a compile error (audit r12)', () => {
    // W gets a slot via the consequent, but θ[slot] would be undefined at
    // match time — the check must demand an ANTECEDENT binding.
    const ante = t2(atom('a'), Store.put('after', [mv('W')]));
    assert.throws(() => compile('bad2', ante, monad(Store.put('b', [mv('W')]))), /not bound/);
    // A persistent-goal binding (the desugarTimed output shape) is fine.
    const ante2 = t2(t2(atom('a'), Store.put('after', [mv('Q')])),
      Store.put('bang', [gradeW(), Store.put('qplus', [mv('X'), mv('Y'), mv('Q')])]));
    const ok = compile('okwin', ante2, monad(atom('b')));
    assert.deepEqual(ok.windows.after, [{ slot: ok.metavarSlots[mv('Q')] }]);
  });

  it('rules without timed forms carry no windows/readOnly fields (ILL delta-zero)', () => {
    const rule = compile('plain', t2(atom('a'), atom('b')), monad(atom('c')));
    assert.equal(rule.windows, undefined);
    assert.equal(rule.readOnly, undefined);
  });

  it('windows/readOnly survive JSON serialization (cache round-trip)', () => {
    const pat = Store.put('at', [atom('w'), mv('Q')]);
    const ante = t2(t2(Store.put('readPreserved', [atom('emp')]), pat),
                    Store.put('after', [mv('Q')]));
    const rule = compile('roundtrip', ante, monad(atom('c')));
    const back = JSON.parse(JSON.stringify({ windows: rule.windows, readOnly: rule.readOnly }));
    assert.deepEqual(back.windows, rule.windows);
    assert.deepEqual(back.readOnly, rule.readOnly);
  });
});

describe('read marker: reserved-path semantics (E7.2)', () => {
  it('read fact is matched but NOT consumed', () => {
    const ante = t2(Store.put('readPreserved', [atom('emp')]), atom('job'));
    const rule = compile('work', ante, monad(atom('done')));
    assert.deepEqual(rule.readOnly, [atom('emp')]);
    assert.deepEqual(rule.antecedent.linear.slice().sort(), [atom('emp'), atom('job')].sort());

    const state = forward.createState({ [atom('emp')]: 1, [atom('job')]: 1 }, {});
    const result = forward.run(state, [rule]);
    assert.equal(result.steps, 1);
    assert.equal(result.state.linear[atom('emp')], 1, 'read fact untouched');
    assert.equal(result.state.linear[atom('job')], undefined, 'plain fact consumed');
    assert.equal(result.state.linear[atom('done')], 1);
  });

  it('read works with optimizePreserved OFF (not an optimization)', () => {
    const ante = t2(Store.put('readPreserved', [atom('emp')]), atom('job'));
    const rule = compile('work2', ante, monad(atom('done')));
    const state = forward.createState({ [atom('emp')]: 1, [atom('job')]: 1 }, {});
    const result = forward.run(state, [rule], {
      matchOpts: makeMatchOpts({ optimizePreserved: false }),
    });
    assert.equal(result.steps, 1);
    assert.equal(result.state.linear[atom('emp')], 1, 'read fact untouched');
  });

  it('explore(): read fact survives in EVERY leaf across branching + backtracking', () => {
    // Two rules conflict over 'job'; both read 'emp'. Whatever branch explore
    // takes (and undoes), the read fact must appear untouched in every leaf.
    const r1 = compile('w1', t2(Store.put('readPreserved', [atom('emp')]), atom('job')),
      monad(atom('d1')));
    const r2 = compile('w2', t2(Store.put('readPreserved', [atom('emp')]), atom('job')),
      monad(atom('d2')));
    const state = forward.createState({ [atom('emp')]: 1, [atom('job')]: 1 }, {});
    const tree = explore(state, [r1, r2], { maxDepth: 10 });
    const leaves = [];
    (function walk(n) {
      if (!n) return;
      if (n.type === 'leaf') leaves.push(n.state);
      for (const c of (n.children || [])) walk(c.child);
    })(tree);
    assert.equal(leaves.length, 2, 'both branches explored');
    for (const leaf of leaves) {
      assert.equal(leaf.linear.count(Store.tagId(atom('emp')), atom('emp')), 1,
        'read fact present and single in every leaf');
      assert.equal(leaf.linear.count(Store.tagId(atom('job')), atom('job')), 0,
        'consumed fact gone in every leaf');
    }
  });

  it('explore(): read+consume conflict holds under backtracking too', () => {
    const rc = compile('rc2', t2(Store.put('readPreserved', [atom('a')]), atom('a')),
      monad(atom('c')));
    const one = explore(forward.createState({ [atom('a')]: 1 }, {}), [rc], { maxDepth: 5 });
    assert.equal(one.type, 'leaf', 'no firing possible with a single token');
    const two = explore(forward.createState({ [atom('a')]: 2 }, {}), [rc], { maxDepth: 5 });
    assert.notEqual(two.type, 'leaf');
  });

  it('read + consume of the same single token conflict (reserved blocks double use)', () => {
    const ante = t2(Store.put('readPreserved', [atom('a')]), atom('a'));
    const rule = compile('rc', ante, monad(atom('c')));
    const one = forward.run(forward.createState({ [atom('a')]: 1 }, {}), [rule]);
    assert.equal(one.steps, 0, 'one token cannot be both read and consumed');
    const two = forward.run(forward.createState({ [atom('a')]: 2 }, {}), [rule]);
    assert.equal(two.steps, 1);
    assert.equal(two.state.linear[atom('a')], 1, 'read copy survives, consumed copy gone');
  });
});
