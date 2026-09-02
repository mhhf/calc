/**
 * Refinement sorts, end-to-end (TODO_0011 rung 1) — the acceptance seeds
 * from the consolidated spec, run through real till loads:
 *   - subsumption: bin ≤ q, frac ≤ q; frac ≰ bin rejected
 *   - classifiers: members are propositions (≤ type); misuse rejected
 *   - bounded sort variables: sub a b D ⇒ D refined to bin;
 *     sub a c D (mixed bin/frac) ⇒ load error naming instances;
 *     an instance at the bound legalizes mixed goals
 *   - classifier rule schemas: load-time expansion, one rule per member
 *   - grade sorts: weight/count value fences on literals
 *   - hygiene: duplicate membership, cycles, missing prelude, sortless ILL
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import mde from '../../lib/engine/index.js';
import Store from '../../lib/kernel/store.js';
import tillConfig from '../../calculus/till/calculus-config.js';
import illConfig from '../../calculus/ill/calculus-config.js';
import { stamped } from './till-helpers.js';

const PRELUDE = path.join(import.meta.dirname, '../../calculus/till/prelude');
const RAT = path.join(PRELUDE, 'rat.ill');
const SORTS = path.join(PRELUDE, 'sorts.till');

let dir;
const write = (name, text) => {
  const p = path.join(dir, name);
  fs.writeFileSync(p, text);
  return p;
};
const load = (p) => mde.load(p, { calculusConfig: tillConfig, cache: false });
before(() => { dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-sorts-')); });
after(() => { fs.rmSync(dir, { recursive: true, force: true }); });

describe('subsumption over the numeric tower', () => {
  it('bin and frac literals satisfy q positions', () => {
    const p = write('tower-ok.ill', `#import(${RAT})
go: type.
priced: (p: q) -> type.
r: go * !plus 3 (1/2) P -o { priced P }.
`);
    const calc = load(p);
    assert.equal(calc.forwardRules.length, 1);
  });

  it('a frac at a bin position is rejected (frac ≰ bin)', () => {
    const p = write('tower-bad.ill', `#import(${RAT})
go: type.
f: (n: bin) -> type.
r: go * !f (rat (i e) (o (i e))) -o { go }.
`);
    assert.throws(() => load(p), /expected sort 'bin', got 'frac'/);
  });

  it('a metavar cannot serve two incompatible sorts', () => {
    const p = write('mv-bad.ill', `#import(${SORTS})
resource: sort.
wood: resource.
f: (n: resource) -> type.
g: (s: sort) -> type.
r: f X * g X -o { f X }.
`);
    assert.throws(() => load(p), /incompatible sorts/);
  });
});

describe('classifiers', () => {
  it('members are propositions: usable as resources, grouped for tooling', () => {
    const p = write('class-ok.ill', `#import(${SORTS})
resource: sort.
wood: resource.
stone: resource.
store: type.
r: store * wood -o { stone }.
`);
    const calc = load(p);
    assert.equal(calc.forwardRules.length, 1);
    assert.ok(calc.sorts, 'sort system present');
    assert.deepEqual([...calc.sorts.membersOf('resource')].sort(), ['stone', 'wood']);
  });

  it('a classifier member at a term-sort position is rejected', () => {
    const p = write('class-bad.ill', `#import(${RAT})
resource: sort.
wood: resource.
f: (n: bin) -> type.
go: type.
r: go * !f wood -o { go }.
`);
    assert.throws(() => load(p), /expected sort 'bin', got 'resource'/);
  });

  it('duplicate membership is a load error at the second declaration', () => {
    const p = write('dup.ill', `#import(${SORTS})
resource: sort.
material: sort.
wood: resource.
wood: material.
`);
    assert.throws(() => load(p), /Duplicate definition 'wood'/);
  });
});

describe('bounded sort variables (the sub acceptance spec)', () => {
  // nsub: one name, instances inferred from clause heads — a bin instance
  // (head patterns on binlit/e) and a frac instance (heads pattern on rat).
  const NSUB = `#import(${RAT})
go: type.
gotbin: (r: bin) -> type.
nsub: (s <: q) (a: s) -> (b: s) -> (r: s) -> type.
nsub/z: nsub X e X.
nsub/q: nsub (rat A B) (rat C D) R
  <- qsub (rat A B) (rat C D) R.
`;

  it('nsub a b D at bin: loads, result metavar refined to bin', () => {
    // D flows into gotbin's (r: bin) position — legal ONLY because the
    // solved instance sort (bin) is what D is checked at, not the bound q.
    const p = write('nsub-bin.ill', NSUB + `
r: go * !nsub 5 3 D -o { gotbin D }.
`);
    const calc = load(p);
    assert.equal(calc.forwardRules.length, 1);
  });

  it('nsub a c D mixed bin/frac: load error naming the instances', () => {
    const p = write('nsub-mixed.ill', NSUB + `
r: go * !nsub 5 (rat (i e) (o (i e))) D -o { go }.
`);
    assert.throws(() => load(p), /no instance at 'q'.*instances: \{.*bin.*\}/);
  });

  it('an instance at the bound (bare-variable head) legalizes mixed goals', () => {
    const p = write('nsub-q.ill', NSUB + `
nsub/any: nsub U V R
  <- qsub U V R.
r: go * !nsub 5 (rat (i e) (o (i e))) D -o { go }.
`);
    const calc = load(p);
    assert.equal(calc.forwardRules.length, 1);
  });

  it('solving outside the bound is rejected', () => {
    const p = write('nsub-oob.ill', NSUB + `
resource: sort.
wood: resource.
r: go * !nsub wood wood D -o { go }.
`);
    assert.throws(() => load(p), /no common supersort|outside the bound/);
  });
});

describe('classifier rule schemas (load-time expansion)', () => {
  const GAME = `#import(${SORTS})
resource: sort.
wood: resource.
stone: resource.
food: resource.
store: type.
stored: (r: resource) -> type.
keep: (r: resource) store * r -o { store * stored r }.
`;

  it('expands to one ground rule per member', () => {
    const calc = load(write('schema.ill', GAME));
    assert.deepEqual(calc.forwardRules.map(r => r.name).sort(),
      ['keep/food', 'keep/stone', 'keep/wood']);
  });

  it('expanded rules execute: the member is substituted, not the binder', () => {
    const calc = load(write('schema-exec.ill', GAME));
    const atom = (n) => mde.Store.put('atom', [n]);
    const res = calc.settle({
      linear: { [atom('store')]: 1, [atom('wood')]: 1 }, persistent: {},
    }, '0');
    const keys = Object.keys(stamped(res.state)).sort();
    assert.deepEqual(keys, ['store@0', 'stored@0']);
    assert.equal(res.events.length, 1);
    assert.equal(res.events[0].rule, 'keep/wood');
  });

  it('multiple binders expand as a cartesian product', () => {
    const calc = load(write('schema2.ill', `#import(${SORTS})
resource: sort.
wood: resource.
stone: resource.
place: sort.
barn: place.
silo: place.
put: (r: resource) (p: place) r * p -o { p }.
`));
    assert.deepEqual(calc.forwardRules.map(r => r.name).sort(),
      ['put/stone/barn', 'put/stone/silo', 'put/wood/barn', 'put/wood/silo']);
  });

  it('empty classifier is a load error, not a vanishing rule', () => {
    assert.throws(() => load(write('schema-empty.ill', `#import(${SORTS})
resource: sort.
store: type.
r: (x: resource) store * x -o { store }.
`)), /has no members/);
  });

  it('quantifying over a non-classifier is a load error', () => {
    assert.throws(() => load(write('schema-bin.ill', `#import(${RAT})
store: type.
r: (x: bin) store -o { store }.
`)), /not a classifier/);
  });

  it('binder shadowing a declared symbol is a load error', () => {
    assert.throws(() => load(write('schema-shadow.ill', `#import(${SORTS})
resource: sort.
wood: resource.
store: type.
r: (wood: resource) store * wood -o { store }.
`)), /shadows a declared symbol/);
  });
});

describe('grade sorts: value fences on literals', () => {
  it('a weight above 1 is rejected (parser range check; the checker fence backstops store-level construction)', () => {
    assert.throws(() => load(write('weight-bad.ill', `#import(${RAT})
a: type.
b: type.
c: type.
r: a -o { b +[3/2] c }.
`)), /must be in \[0, 1\]/);
  });

  it('weights in [0,1] load (integer and rational)', () => {
    const calc = load(write('weight-ok.ill', `#import(${RAT})
a: type.
b: type.
c: type.
r: a -o { b +[1/2] c }.
r2: a -o { b +[1] c }.
`));
    assert.equal(calc.forwardRules.length, 2);
  });

  it('rational delays pass the nonneg fence ({B}@d, A@t)', () => {
    const calc = load(write('delay-ok.ill', `#import(${RAT})
a: type.
b: type.
r: a@Q * after (Q + 2) -o { b }@(1/2).
`));
    assert.equal(calc.forwardRules.length, 1);
  });
});

describe('hygiene and presence gating', () => {
  it('subsort declaration without the prelude points at the import', () => {
    assert.throws(() => load(write('no-prelude.ill', `q: type.
bin2: type.
bin2 <: q.
`)), /sorts prelude/);
  });

  it('subsort cycle is a load error', () => {
    assert.throws(() => load(write('cycle.ill', `#import(${SORTS})
a2: type.
b2: type.
a2 <: b2.
b2 <: a2.
`)), /cycle/i);
  });

  it('unknown sort in a subsort declaration is a load error', () => {
    assert.throws(() => load(write('ghost-edge.ill', `#import(${SORTS})
a2: type.
a2 <: ghost.
`)), /unknown sort 'ghost'/);
  });

  it('a sortless calculus (ILL) refuses subsort declarations', () => {
    const p = write('ill-subsort.ill', `q: type.
bin2: type.
bin2 <: q.
`);
    assert.throws(() => mde.load(p, { calculusConfig: illConfig, cache: false }), /sortless/);
  });

  it('a sortless till program still loads through the string checker', () => {
    const calc = load(write('sortless.ill', `wood: type.
plank: type.
r: wood -o { plank }@1.
`));
    assert.equal(calc.forwardRules.length, 1);
    assert.equal(calc.sorts, null);
  });
});

describe('materialized subsort keys are collision-free (TODO_0272 MINOR 1)', () => {
  // Two DISTINCT edges whose sort names collide under a `_` key separator:
  //   (a, b_c) and (a_b, c) both join to `a_b_c`. The `/` separator keeps
  //   them distinct (`a/b_c` vs `a_b/c`); sort names can't contain `/`.
  it('both `a <: b_c` and `a_b <: c` materialize as distinct facts', () => {
    const calc = load(write('underscore-sorts.till', `#import(${SORTS})
a: type.
b_c: type.
a_b: type.
c: type.
a <: b_c.
a_b <: c.
`));
    const facts = new Set([...calc.clauses.values()].map(v => v.hash));
    const edge = (sub, sup) =>
      Store.put('subsort', [Store.put('atom', [sub]), Store.put('atom', [sup])]);
    // Under the old `_` separator one of these two clauses overwrote the
    // other in the clauses Map, so only one fact survived.
    assert.ok(facts.has(edge('a', 'b_c')), 'subsort a b_c must materialize');
    assert.ok(facts.has(edge('a_b', 'c')), 'subsort a_b c must materialize');
  });
});
