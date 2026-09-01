/**
 * @draw checker + prior materialization + drawn fence (TODO_0298 item 1b).
 *
 * Pins:
 *   - materialized priors: `@w` ratios become ground `prior s c ρ` facts
 *     for every member of a TOUCHED classifier (default 1), presence-gated
 *     on the program declaring the predicate; untouched classifiers and
 *     undeclared programs get nothing
 *   - the drawn fence: no program rule may produce OR match a `drawn`
 *     token (kernel-reserved, THY_0027 §1)
 *   - drawChecker: one collapse event re-derived from the program's sort
 *     system and declared priors — witness head, sort membership, weight
 *     agreement, wave/token consumption, opened-body introduction (bare
 *     and stamped), persistent conjuncts; the kernel routes it via
 *     calculus.stepCheckers (full verifyTree integration, no unverified)
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import Seq from '../../lib/kernel/sequent.js';
import Context from '../../lib/prover/context.js';
import mde from '../../lib/engine/index.js';
import { drawChecker } from '../../lib/prover/draw-check.js';
import { createKernel } from '../../lib/prover/kernel.js';
import willConfig, { loadWillSequent } from '../../calculus/will/calculus-config.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'will-draw-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));
const MEASURE = path.join(import.meta.dirname, '../../calculus/will/prelude/measure.will');

// land is deliberately UNANNOTATED: the touched classifier materializes
// its full member table with default weight 1
const HEADER = `#import(${MEASURE})
pos2: sort.
a0: pos2.
a1: pos2.
tile_t: sort.
sea: tile_t @w 2.
coast: tile_t @w 1.
land: tile_t.
mk: (c: pos2) -> type.
tile: (c: pos2) -> (t: tile_t) -> type.
prior: (s: sort) -> (c: tile_t) -> (w: q) -> type.
spawn: mk C -o { exists T: tile_t @w. tile C T }.
`;

const loadProg = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src);
  return mde.load(f, { calculusConfig: willConfig, cache: false });
};

const atom = (n) => Store.put('atom', [n]);
const bound0 = () => Store.put('bound', [0n]);
const bin = (n) => Store.put('binlit', [BigInt(n)]);
const tile = (c, t) => Store.put('tile', [c, t]);
const wave = () => Store.put('superpose',
  [atom('tile_t'), Store.put('exists', [tile(atom('a0'), bound0())])]);
const token = (m) => Store.put('drawn', [atom(m), atom('tile_t')]);
const at = (f, t) => Store.put('at', [f, t]);

describe('prior materialization', () => {
  let calc;
  before(() => { calc = loadProg('priors.will', HEADER); });

  const priorOf = (member) => {
    const W = Store.put('metavar', ['W']);
    const r = calc.prove(Store.put('prior', [atom('tile_t'), atom(member), W]));
    if (!r || !r.success) return null;
    for (const [k, v] of r.theta) if (k === W) return v;
    return null;
  };

  it('@w ratios are queryable prior facts', () => {
    assert.equal(priorOf('sea'), bin(2));
    assert.equal(priorOf('coast'), bin(1));
  });
  it('unannotated member of a touched classifier defaults to 1', () => {
    assert.equal(priorOf('land'), bin(1));
  });
  it('untouched classifier gets no facts', () => {
    const W = Store.put('metavar', ['W']);
    const r = calc.prove(Store.put('prior', [atom('pos2'), atom('a0'), W]));
    assert.ok(!r || !r.success);
  });
  it('a program without the prior declaration materializes nothing', () => {
    const c2 = loadProg('noprior.will', HEADER.replace(/prior: [^\n]*\n/, ''));
    assert.ok(![...c2.clauses.keys()].some((k) => k.startsWith('prior/')));
  });
});

describe('drawn fence (kernel-reserved, THY_0027 §1)', () => {
  it('a rule consequent producing a token is a load error', () => {
    assert.throws(
      () => loadProg('forge.will', HEADER + 'forge: mk a0 -o { drawn sea tile_t }.\n'),
      /kernel-reserved/);
  });
  it('a rule antecedent matching a token is a load error', () => {
    assert.throws(
      () => loadProg('read.will', HEADER + 'peek: drawn sea tile_t -o { mk a0 }.\n'),
      /kernel-reserved/);
  });
});

describe('@draw checker', () => {
  let prog, seqCalc, kernel;
  before(() => {
    prog = loadProg('draw.will', HEADER);
    seqCalc = loadWillSequent();
    kernel = createKernel(seqCalc);
  });

  const node = ({ lin, succ, premLin, premCart = [], draw }) => ({
    conclusion: Seq.fromArrays(lin, [], succ),
    premises: [{ conclusion: Seq.fromArrays(premLin, premCart, succ), premises: [], rule: 'id' }],
    rule: 'draw',
    state: { draw },
  });
  const tree = (n, lo = [Context.empty()]) =>
    drawChecker.tree(n, lo, { calculus: seqCalc, program: prog });

  it('accepts a bare collapse (wave + token → opened body)', () => {
    const goal = tile(atom('a0'), atom('sea'));
    const r = tree(node({
      lin: [wave(), token('sea')], succ: goal,
      premLin: [tile(atom('a0'), atom('sea'))],
      draw: { sort: 'tile_t', member: 'sea' },
    }));
    assert.equal(r.error, undefined);
    assert.ok(Context.isEmpty(r.leftover));
  });

  it('accepts a stamped wave (conjuncts split at the wave stamp)', () => {
    const goal = atom('goalz');
    const r = tree(node({
      lin: [at(wave(), bin(3)), token('sea')], succ: goal,
      premLin: [at(tile(atom('a0'), atom('sea')), bin(3))],
      draw: { sort: 'tile_t', member: 'sea' },
    }));
    assert.equal(r.error, undefined);
  });

  it('verifies the recorded weight against the declared prior', () => {
    const goal = atom('goalz');
    const mk = (weight) => node({
      lin: [wave(), token('sea')], succ: goal,
      premLin: [tile(atom('a0'), atom('sea'))],
      draw: { sort: 'tile_t', member: 'sea', weight },
    });
    assert.equal(tree(mk([2n, 1n])).error, undefined);
    assert.equal(tree(mk([4n, 2n])).error, undefined, 'unreduced ratio compares by value');
    assert.match(tree(mk([1n, 1n])).error, /declared prior/);
  });

  it('rejects a non-member and a foreign sort', () => {
    const goal = atom('goalz');
    const bad = tree(node({
      lin: [wave(), Store.put('drawn', [atom('volcano'), atom('tile_t')])], succ: goal,
      premLin: [tile(atom('a0'), atom('volcano'))],
      draw: { sort: 'tile_t', member: 'volcano' },
    }));
    assert.match(bad.error, /not a member/);
    const foreign = tree(node({
      lin: [wave(), token('sea')], succ: goal,
      premLin: [tile(atom('a0'), atom('sea'))],
      draw: { sort: 'mystery', member: 'sea' },
    }));
    assert.match(foreign.error, /not a classifier/);
  });

  it('rejects a missing token and a missing opened conjunct', () => {
    const goal = atom('goalz');
    const noToken = tree(node({
      lin: [wave()], succ: goal,
      premLin: [tile(atom('a0'), atom('sea'))],
      draw: { sort: 'tile_t', member: 'sea' },
    }));
    assert.match(noToken.error, /token .* not in the conclusion/);
    const noBody = tree(node({
      lin: [wave(), token('sea')], succ: goal,
      premLin: [],
      draw: { sort: 'tile_t', member: 'sea' },
    }));
    assert.match(noBody.error, /premise missing/);
  });

  it('rejects a succedent change', () => {
    const n = node({
      lin: [wave(), token('sea')], succ: atom('goalz'),
      premLin: [tile(atom('a0'), atom('sea'))],
      draw: { sort: 'tile_t', member: 'sea' },
    });
    n.premises[0].conclusion = Seq.fromArrays(
      [tile(atom('a0'), atom('sea'))], [], atom('other'));
    assert.match(tree(n).error, /succedent/);
  });

  it('full kernel verifyTree routes the checker (no unverified flags)', () => {
    const goal = tile(atom('a0'), atom('sea'));
    const t = node({
      lin: [wave(), token('sea')], succ: goal,
      premLin: [tile(atom('a0'), atom('sea'))],
      draw: { sort: 'tile_t', member: 'sea' },
    });
    const v = kernel.verifyTree(t, { program: prog });
    assert.ok(v.valid, v.errors.join('; '));
    assert.equal(v.unverified, undefined);
  });

  it('kernel rejects a forged draw (no witness record)', () => {
    const goal = tile(atom('a0'), atom('sea'));
    const t = node({
      lin: [wave(), token('sea')], succ: goal,
      premLin: [tile(atom('a0'), atom('sea'))],
      draw: null,
    });
    t.state = {};
    const v = kernel.verifyTree(t, { program: prog });
    assert.ok(!v.valid);
  });
});
