/**
 * certifyConfluence (TODO_0309 P2, THY_0036) — the destination-
 * discipline confluence certifier, tested from three sides:
 *
 * 1. The SAX machine certifies (the discipline's motivating instance —
 *    FSCD 2020 Thm. 10 as a checked certificate, including the
 *    case_in1/case_in2 pair whose exclusion is the WRITE-ONCE cell,
 *    not dispatch-pattern shape).
 * 2. Adversarial refusals (the ci.js pattern): every discipline
 *    condition has a pinned witness — including the observable race.
 * 3. Explore integration: a certificate collapses interleaving
 *    branching to one path with the SAME final state; stale
 *    certificates throw rather than prune.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import saxConfig from '../../calculus/sax/calculus-config.js';
import illmde from '../../calculus/ill/index.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { stateHashStr } from '../../lib/engine/explore.js';

const MACHINE = path.join(import.meta.dirname, '../../calculus/sax/programs/machine.sax');

// The SAX machine's destination discipline (calculus data — the
// certifier itself knows no names).
const SAX_DISCIPLINE = {
  dest: { proc: 0, hole: 0 },
  dispatch: 'proc',
  persistentUnique: { cell: { keys: [0], values: [1] } },
  guards: { cell: 'hole' },
};

describe('certifyConfluence (TODO_0309 P2): the SAX machine', () => {
  let calc, parse;
  before(() => {
    calc = mde.load(MACHINE, { calculusConfig: saxConfig, cache: false });
    parse = (s) => mde.parseExpr(s, saxConfig.loader);
  });
  const initialOf = (facts) => mde.decomposeQuery(parse(facts));

  it('the machine + a well-formed state certify (FSCD Thm. 10, checked)', () => {
    const st = initialOf('!cell c vin1 * hole d * proc d (pcase c win2 win1)');
    const cert = calc.certifyConfluence(st, SAX_DISCIPLINE);
    assert.equal(cert.confluent, true, JSON.stringify(cert.witness || {}));
    assert.equal(typeof cert.rulesDigest, 'number');
    assert.equal(typeof cert.stateDigest, 'number');
  });

  it('case_in1/case_in2 are excluded by the write-once cell, not dispatch shape', () => {
    // Both case rules have IDENTICAL dispatch patterns — remove the
    // single-writer declaration and the pair must be refused as
    // overlapping: the exclusion genuinely lives in persistentUnique.
    const st = initialOf('hole d * proc d wun');
    const cert = calc.certifyConfluence(st, { ...SAX_DISCIPLINE, persistentUnique: {} });
    assert.equal(cert.confluent, false);
    // Without the single-writer declaration the machine is refused —
    // first at forward's witness variable (D3), and the case pair would
    // fall at D2: the write-once cell is load-bearing either way.
    assert.ok(['underdetermined-instance', 'overlapping-dispatch'].includes(cert.witness.reason),
      cert.witness.reason);
  });

  it('the observable race is refused at the initial state (duplicate destination)', () => {
    const st = initialOf('hole d * proc d win1 * proc d win2');
    const cert = calc.certifyConfluence(st, SAX_DISCIPLINE);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'duplicate-destination');
    assert.equal(cert.witness.pred, 'proc');
  });

  it('a guard coexisting with its written cell is refused (write-once violated)', () => {
    const st = initialOf('!cell d vunit * hole d * proc d wun');
    const cert = calc.certifyConfluence(st, SAX_DISCIPLINE);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'guard-cell-coexistence');
  });

  it('explore under the certificate: one committed path, the SAME final state', () => {
    const st = initialOf(
      '!cell (p1 c) vin1 * !cell (p2 c) vin2 * !cell c vpair * ' +
      'hole d * hole (p1 d) * hole (p2 d) * ' +
      'proc d wpr * proc (p1 d) (fwd (p2 c)) * proc (p2 d) (fwd (p1 c))');
    const cert = calc.certifyConfluence(st, SAX_DISCIPLINE);
    assert.equal(cert.confluent, true, JSON.stringify(cert.witness || {}));

    const full = calc.explore(st, { maxDepth: 64 });
    const fullLeaves = getAllLeaves(full).filter(l => l.type === 'leaf');
    const fullStates = new Set(fullLeaves.map(l => stateHashStr(toObject(l.state))));
    assert.equal(fullStates.size, 1, 'baseline: empirically confluent');

    const pruned = calc.explore(st, { maxDepth: 64, confluence: cert });
    const prunedLeaves = getAllLeaves(pruned).filter(l => l.type === 'leaf');
    assert.equal(prunedLeaves.length, 1, 'certificate: exactly one interleaving explored');
    assert.equal(stateHashStr(toObject(prunedLeaves[0].state)), [...fullStates][0],
      'the committed path reaches the common final state');
    assert.ok(fullLeaves.length > prunedLeaves.length,
      'the certificate actually pruned interleavings');
  });

  it('a stale certificate throws instead of pruning', () => {
    const st = initialOf('hole d * proc d wun');
    const cert = calc.certifyConfluence(st, SAX_DISCIPLINE);
    assert.throws(
      () => calc.explore(st, { confluence: { ...cert, rulesDigest: cert.rulesDigest ^ 1 } }),
      /rule-set digest mismatch/);
    const other = initialOf('hole d * proc d win1');
    assert.throws(
      () => calc.explore(other, { confluence: cert }),
      /initial-state digest mismatch/);
    assert.throws(
      () => calc.explore(st, { confluence: { confluent: false, witness: {} } }),
      /not a confluent certificate/);
  });
});

describe('certifyConfluence: adversarial refusals (ILL fragment)', () => {
  // Tiny keyed token programs under the ILL config — each violating
  // exactly one discipline condition.
  function loadProg(text) {
    Store.clear();
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'confl-'));
    const file = path.join(tmpDir, 'p.ill');
    fs.writeFileSync(file, text);
    try {
      return illmde.load(file, { cache: false });
    } finally {
      for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
      fs.rmdirSync(tmpDir);
    }
  }
  const DISC = { dest: { cf_tok: 0, cf_out: 0 }, dispatch: 'cf_tok' };
  const HEADER =
    'cf_tok: (d: bin) -> (v: bin) -> type.\n' +
    'cf_out: (d: bin) -> (v: bin) -> type.\n';

  it('a well-formed keyed ILL fragment certifies (the discipline is calculus-agnostic)', () => {
    const calc = loadProg(HEADER +
      'r1: cf_tok D 1 -o { cf_out D 1 * cf_tok D 2 }.\n' +
      'r2: cf_tok D 2 -o { cf_tok D 3 }.\n' +
      '#symex cf_tok 7 1 * cf_out 7 9.\n');
    const st = illmde.decomposeQuery(illmde.parseExpr('cf_tok 7 1', illmde.illConfig.loader));
    const cert = calc.certifyConfluence(st, DISC);
    assert.equal(cert.confluent, true, JSON.stringify(cert.witness || {}));
  });

  it('overlapping dispatch patterns are refused', () => {
    const calc = loadProg(HEADER +
      'r1: cf_tok D X -o { cf_out D X }.\n' +
      'r2: cf_tok D X -o { cf_tok D X }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'overlapping-dispatch');
  });

  it('internal choice (⊕ consequent) is refused', () => {
    const calc = loadProg(HEADER +
      'r1: cf_tok D 1 -o { cf_out D 1 + cf_out D 2 }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'internal-choice');
  });

  it('an unkeyed pattern is refused', () => {
    const calc = loadProg(HEADER + 'cf_gate: type.\n' +
      'r1: cf_tok D 1 * cf_gate -o { cf_out D 1 }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'unkeyed-pattern');
  });

  it('a two-destination rule is refused', () => {
    const calc = loadProg(HEADER +
      'r1: cf_tok D 1 * cf_out E 1 -o { cf_out D 2 }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'multi-destination');
  });

  it('production outside a consumed slot is refused', () => {
    const calc = loadProg(HEADER +
      'r2: cf_tok D 9 * cf_out D 1 -o { cf_tok D 8 }.\n' + // cf_out consumed somewhere → not a sink
      'r1: cf_tok D 1 -o { cf_tok D 2 * cf_out D 1 }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'non-slot-reuse-production');
  });

  it('an undetermined witness variable is refused', () => {
    const calc = loadProg(HEADER +
      'cf_lk: (a: bin) -> (b: bin) -> type.\n' +
      'r1: cf_tok D 1 * !cf_lk D V -o { cf_out D V }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'underdetermined-instance');
    // ...and DECLARING the lookup single-writer readmits it (D3 closure)
    const cert2 = calc.certifyConfluence({ linear: {}, persistent: {} },
      { ...DISC, persistentUnique: { cf_lk: { keys: [0], values: [1] } } });
    assert.equal(cert2.confluent, true, JSON.stringify(cert2.witness || {}));
  });

  it('dynamic-rule production (loli consequent) is refused', () => {
    const calc = loadProg(HEADER +
      'r1: cf_tok D 1 -o { cf_tok D 2 -o { cf_out D 2 } }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'dynamic-rule-production');
  });
});
