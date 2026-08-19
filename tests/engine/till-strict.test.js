/**
 * Closed-world sort checking — TODO_0265 Phase 6 post-mortem.
 *
 * The checker's original open-world skip let every undeclared symbol
 * self-introduce (a typo'd token became a new resource, silently), and its
 * strict flag was never wired — "strongly typed" was stderr noise. Under
 * till (cc.typeCheck: 'strict') loading now FAILS on:
 *   - undeclared atoms / predicates anywhere in rules or clauses
 *   - arity and sort mismatches on declared symbols
 *   - 'type' as an ARGUMENT sort (quantification over propositions — not
 *     supported without a classifier-sort theory extension; the string
 *     collision that let `kind: (x: type) -> …` slip through is closed)
 *   - unknown sorts in signatures (the phantom `ltype`)
 * ILL stays open-world (corpus audit pending); strictTypes: false opts a
 * till load out (ill-sorted-by-design engine fixtures).
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import mde from '../../lib/engine/index.js';
import tillConfig from '../../calculus/till/calculus-config.js';

describe('closed-world sort checking (till strict mode)', () => {
  let dir;
  const write = (name, text) => {
    const p = path.join(dir, name);
    fs.writeFileSync(p, text);
    return p;
  };
  const loadStrict = (p) => mde.load(p, { calculusConfig: tillConfig, cache: false });
  before(() => { dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-strict-')); });
  after(() => { fs.rmSync(dir, { recursive: true, force: true }); });

  it('undeclared atom in a rule fails the load', () => {
    const p = write('bad-atom.ill', 'src: type.\nr: src -o { wat }.\n');
    assert.throws(() => loadStrict(p), /unknown atom 'wat'/);
  });

  it('undeclared predicate fails the load', () => {
    const p = write('bad-pred.ill', 'utype: type.\nrock: utype.\nr: ghost(rock) -o { ghost(rock) }.\n');
    assert.throws(() => loadStrict(p), /unknown predicate 'ghost'/);
  });

  it('arity mismatch on a declared symbol fails the load', () => {
    const p = write('bad-arity.ill',
      'utype: type.\nrock: utype.\nred: (u: utype) -> type.\nr: red rock rock -o { red(rock) }.\n');
    assert.throws(() => loadStrict(p), /'red' expects 1 args/);
  });

  it('sort mismatch on a declared symbol fails the load', () => {
    const p = write('bad-sort.ill',
      'utype: type.\nrock: utype.\nbtype: type.\nblt: btype.\nred: (u: utype) -> type.\nr: red(blt) -o { red(rock) }.\n');
    assert.throws(() => loadStrict(p), /expected sort 'utype', got 'btype'/);
  });

  it("'type' as an argument sort is rejected — no quantification over propositions", () => {
    const p = write('bad-typequant.ill', 'kindx: (x: type) -> type.\n');
    assert.throws(() => loadStrict(p), /quantification over propositions/);
  });

  it('unknown sorts in signatures are rejected (the phantom ltype)', () => {
    const p = write('bad-ltype.ill', 'f: (x: ltype) -> type.\n');
    assert.throws(() => loadStrict(p), /unknown sort 'ltype'/);
  });

  it('a fully declared program loads strict-clean', () => {
    const p = write('good.ill',
      'wood: type.\nplank: type.\nsawmillx: type.\nr: sawmillx * wood -o { sawmillx * plank }@1.\n');
    const calc = loadStrict(p);
    assert.equal(calc.forwardRules.length, 1);
  });

  it('ILL is strict too (corpus audited clean); strictTypes: false opts out', () => {
    const p = write('permissive.ill', 'r: src -o { wat }.\n');
    assert.throws(() => mde.load(p, { cache: false }), /unknown atom/);   // ILL default: strict
    assert.ok(mde.load(p, { cache: false, strictTypes: false }));
    assert.ok(mde.load(p, { calculusConfig: tillConfig, cache: false, strictTypes: false }));
    assert.throws(() => loadStrict(p), /unknown atom/);
  });
});

describe('closed world covers directives too', () => {
  let dir;
  before(() => { dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-strict-q-')); });
  after(() => { fs.rmSync(dir, { recursive: true, force: true }); });

  it('a typo in a gate fails the load, not the gate', () => {
    const p = path.join(dir, 'bad-gate.ill');
    fs.writeFileSync(p,
      'wood: type.\nplank: type.\nr: wood -o { plank }@1.\n' +
      '#expect_x (settle: 2)\n  wod\n  =>\n  plank@1 .\n');
    assert.throws(() => mde.load(p, { calculusConfig: tillConfig, cache: false }),
      /directive 'expect_x'.*unknown atom 'wod'/s);
  });
});

describe('grade positions have their own closed grammar', () => {
  // The surface parser already rejects malformed count grades (`!_wood`),
  // so this guards the STORE level (programmatic states, future grammar):
  // checkAll must flag a non-grade in a bang grade position.
  it('a non-grade hash in a bang grade position is a closed-world error', async () => {
    const { checkAll } = await import('../../lib/engine/type-check.js');
    const Store = (await import('../../lib/kernel/store.js')).default;
    const wood = Store.put('atom', ['wood']);
    const bad = Store.put('bang', [wood, wood]);       // grade = a token atom
    const defs = new Map([['wood', Store.put('type', [])]]);
    const { errors } = checkAll(defs, [], new Map(), {
      closedWorld: true,
      queries: new Map([['expect_x', { lhsHash: bad, rhsHash: wood }]]),
    });
    assert.ok(errors.some(e => /invalid grade 'wood'/.test(e)), errors.join('; '));
  });
});
