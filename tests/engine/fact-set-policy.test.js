/**
 * FactSet index policy — TODO_0265 Phase 3 (D5/D13).
 *
 * "The index is optimization, the multiset is semantics": FactSet takes an
 * optional { groupKey, cmp } policy. till files at(A,t) under A's predicate
 * tag with a stamp-then-hash order (the FIFO cohort index); absent policy
 * is bit-identical to the historical layout. The index-equivalence tests
 * instantiate D13's corollary: an index may never change WHICH matches
 * exist, only how fast candidates are found.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import { FactSet, Arena, fromObject } from '../../lib/engine/fact-set.js';
import forward from '../../lib/engine/forward.js';
import { explore } from '../../lib/engine/explore.js';
import { compileRule } from '../../lib/engine/compile.js';
import { ILL_CONNECTIVES } from '../../lib/engine/ill/connectives.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import { ratParts } from '../../lib/engine/theories/ratlit-theory.js';
import { cmp as ratCmp } from '../../lib/rat.js';
import path from 'path';
import mde from '../../lib/engine/index.js';
import illCalculusConfig from '../../lib/engine/ill/calculus-config.js';
import { show } from '../../lib/engine/show.js';

const atom = (n) => Store.put('atom', [n]);
const at = (a, n, d) => Store.put('at', [a, putRat(n, d)]);

// till's index policy (todo 0265 Phase 3 spec, verbatim shape)
const stampOf = (h) => Store.tag(h) === 'at'
  ? ratParts(Store.child(h, 1)) : [0n, 1n];
const TILL_POLICY = {
  groupKey: (h) => Store.tag(h) === 'at'
    ? Store.tagId(Store.child(h, 0)) : Store.tagId(h),
  cmp: (a, b) => ratCmp(stampOf(a), stampOf(b)) || (a - b),
};

describe('FactSet policy: grouping + order', () => {
  it('groupKey files at(A,t) under A\'s group', () => {
    const fs = new FactSet(Store.TAG_NAMES.length, TILL_POLICY);
    const f1 = at(atom('wood'), 3n, 1n);
    fs.insert(Store.tagId(f1), f1, null);
    assert.equal(fs.groupLen(Store.TAG.at), 0, 'nothing under the at tag');
    assert.equal(fs.groupLen(Store.TAG.atom), 1, 'filed under the inner group');
    assert.ok(fs.has(Store.tagId(f1), f1), 'has() re-derives the group');
    assert.equal(fs.count(Store.tagId(f1), f1), 1);
  });

  it('cmp orders a group by stamp, then hash (FIFO index)', () => {
    const fs = new FactSet(Store.TAG_NAMES.length, TILL_POLICY);
    const w = atom('wood');
    const facts = [at(w, 3n, 1n), at(w, 1n, 2n), at(w, 2n, 1n), w /* stamp 0 */];
    for (const f of facts) fs.insert(Store.tagId(f), f, null);
    const got = Array.from(fs.group(Store.TAG.atom));
    assert.deepEqual(got, [w, at(w, 1n, 2n), at(w, 2n, 1n), at(w, 3n, 1n)],
      'ascending stamp order: 0, 1/2, 2, 3');
  });

  it('same-stamp copies stay adjacent (cohort multiplicity)', () => {
    const fs = new FactSet(Store.TAG_NAMES.length, TILL_POLICY);
    const f = at(atom('w'), 1n, 2n);
    fs.insert(Store.tagId(f), f, null);
    fs.insert(Store.tagId(f), f, null);
    assert.equal(fs.count(Store.tagId(f), f), 2);
    fs.remove(Store.tagId(f), f, null);
    assert.equal(fs.count(Store.tagId(f), f), 1);
  });

  it('Arena undo restores state exactly under an active policy', () => {
    const fs = new FactSet(Store.TAG_NAMES.length, TILL_POLICY);
    const w = atom('w');
    const early = at(w, 1n, 1n), late = at(w, 5n, 1n);
    fs.insert(Store.tagId(early), early, null);
    const hashBefore = fs.hash;
    const groupBefore = Array.from(fs.group(Store.TAG.atom));

    const arena = new Arena();
    const cp = arena.checkpoint();
    fs.insert(Store.tagId(late), late, arena);
    fs.remove(Store.tagId(early), early, arena);
    fs.undo(arena, cp);

    assert.equal(fs.hash, hashBefore, 'Zobrist restored');
    assert.deepEqual(Array.from(fs.group(Store.TAG.atom)), groupBefore);
  });

  it('snapshot carries the policy', () => {
    const fs = new FactSet(Store.TAG_NAMES.length, TILL_POLICY);
    const f = at(atom('w'), 2n, 1n);
    fs.insert(Store.tagId(f), f, null);
    const snap = fs.snapshot();
    assert.ok(snap.has(Store.tagId(f), f));
    assert.equal(snap.policy, TILL_POLICY);
  });

  it('absent policy is byte-identical to the historical layout', () => {
    const a = new FactSet(Store.TAG_NAMES.length);
    const b = new FactSet(Store.TAG_NAMES.length, null);
    for (const n of ['z', 'a', 'm']) {
      a.insert(0, atom(n), null);
      b.insert(0, atom(n), null);
    }
    assert.deepEqual(Array.from(a.group(0)), Array.from(b.group(0)));
    assert.equal(a.hash, b.hash);
  });
});

// ─── Index equivalence (D13 corollary) ──────────────────────────────

const loli = (a, b) => Store.put('loli', [a, b]);
const t2 = (a, b) => Store.put('tensor', [a, b]);
const monad = (b) => Store.put('monad', [b]);

function mkRule(name, ante, conseq) {
  return compileRule(
    { name, hash: loli(ante, conseq), antecedent: ante, consequent: conseq },
    { connectives: ILL_CONNECTIVES });
}

// Deterministic scrambled-but-total order: mixed key, hash tie-break.
const SCRAMBLED_POLICY = {
  cmp: (a, b) => {
    const ka = (Math.imul(a, 2654435761) >>> 16), kb = (Math.imul(b, 2654435761) >>> 16);
    return (ka - kb) || (a - b);
  },
};

describe('index equivalence: policies never change WHICH matches exist', () => {
  const POLICIES = [null, TILL_POLICY, SCRAMBLED_POLICY];

  it('confluent forward.run reaches the same final state under every policy', () => {
    const rules = [
      mkRule('r1', t2(atom('a'), atom('b')), monad(atom('c'))),
      mkRule('r2', t2(atom('c'), atom('d')), monad(atom('done'))),
    ];
    const results = POLICIES.map(p => {
      const state = fromObject(
        { [atom('a')]: 1, [atom('b')]: 1, [atom('d')]: 1 }, {}, p);
      return forward.run(state, rules);
    });
    for (const r of results) {
      assert.equal(r.steps, 2);
      assert.equal(r.state.linear[atom('done')], 1);
    }
    assert.equal(new Set(results.map(r => JSON.stringify(r.state.linear))).size, 1);
  });

  // Same D13 principle, other index: the virtual-discriminator fingerprint
  // (discriminatorPreds) is candidate-lookup optimization — turning it off
  // must not change execution (round-11 ledger item, folded here).
  it('discriminatorPreds [] ≡ [\'arr_get\']: identical EVM execution', () => {
    const evmPath = path.join(import.meta.dirname, '../../calculus/ill/programs/evm.ill');
    const noDisc = {
      ...illCalculusConfig,
      compile: {
        getModes: illCalculusConfig.compile.getModes,
        getModeMeta: illCalculusConfig.compile.getModeMeta,
        discriminatorPreds: [],
        cacheEpoch: 'ill-nodisc',
      },
    };
    const runWith = (loadOpts) => {
      const calc = mde.load(evmPath, { cache: false, ...loadOpts });
      // PUSH1 2, PUSH1 3, ADD, STOP (state shape from tests/forward/evm-arithmetic.ill)
      const linear = {};
      for (const f of ['pc 0', 'gas 0xffffff', 'stack ae', 'mem empty_mem',
        'memsize 0', 'bytecode [0x60, 0x02, 0x60, 0x03, 0x01, 0x00]']) {
        linear[mde.parseExpr(f)] = 1;
      }
      const result = calc.exec({ linear, persistent: {} }, { trace: true, maxSteps: 50 });
      return {
        steps: result.steps,
        quiescent: result.quiescent,
        trace: result.trace.map(t => (typeof t === 'string' ? t.split(' ')[0] : t.rule)),
        finalState: Object.keys(result.state.linear).map(h => show(Number(h))).sort(),
      };
    };
    const withDisc = runWith({});
    const without = runWith({ calculusConfig: noDisc });
    assert.ok(withDisc.steps > 1, 'program genuinely executes');
    assert.deepEqual(without, withDisc);
  });

  it('explore produces the same leaf-state set under every policy', () => {
    const rules = [
      mkRule('e1', t2(atom('a'), atom('b')), monad(atom('c'))),
      mkRule('e2', t2(atom('a'), atom('d')), monad(atom('e'))),
    ];
    const leafHashes = (tree) => {
      const out = [];
      (function walk(n) {
        if (!n) return;
        if (n.type === 'leaf') out.push(n.state.stateHash);
        for (const c of (n.children || [])) walk(c.child);
      })(tree);
      return out.sort().join(',');
    };
    const sets = POLICIES.map(p => {
      const state = fromObject(
        { [atom('a')]: 1, [atom('b')]: 1, [atom('d')]: 1 }, {}, p);
      return leafHashes(explore(state, rules, { maxDepth: 10 }));
    });
    assert.equal(sets[0], sets[1]);
    assert.equal(sets[0], sets[2]);
    assert.ok(sets[0].includes(','), 'genuinely nondeterministic program (≥2 leaves)');
  });
});
