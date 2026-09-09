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
import tillConfig from '../../calculus/till/calculus-config.js';
import illmde from '../../calculus/ill/index.js';
import { certifyConfluence as rawCertify } from '../../lib/engine/certify-confluence.js';
import { freshMetavar as mv } from '../../lib/kernel/fresh.js';
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

  it('an existential consequent (fresh-name nondeterminism) is refused', () => {
    const calc = loadProg(HEADER +
      'r1: cf_tok D 1 -o { exists X. cf_out D X }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'existential-consequent');
  });

  it('a rule with no dispatch pattern is refused (dispatch-arity)', () => {
    const calc = loadProg(HEADER +
      'r1: cf_out D 1 -o { cf_out D 2 }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'dispatch-arity');
  });

  it('two dispatch patterns in one rule are refused (dispatch-arity)', () => {
    const calc = loadProg(HEADER +
      'r1: cf_tok D 1 * cf_tok D 2 -o { cf_tok D 1 * cf_tok D 2 }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'dispatch-arity');
  });

  it('production of a consumed-but-unkeyed predicate is refused', () => {
    // cf_x is consumed by r2 (so it is no sink) but has no dest entry;
    // r1 (first in rule order) trips the production-side check.
    const calc = loadProg(HEADER + 'cf_x: (d: bin) -> type.\n' +
      'r1: cf_tok D 1 -o { cf_tok D 2 * cf_x D }.\n' +
      'r2: cf_tok D 2 * cf_x D -o { cf_tok D 3 }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'unkeyed-production');
  });

  const CELL_DISC = {
    dest: { cf_tok: 0, cf_out: 0, cf_gd: 0 },
    dispatch: 'cf_tok',
    persistentUnique: { cf_cell: { keys: [0], values: [1] } },
  };
  const CELL_HEADER = HEADER +
    'cf_gd: (d: bin) -> type.\n' +
    'cf_cell: (a: bin) -> (b: bin) -> type.\n';

  it('producing a guard predicate is refused', () => {
    const calc = loadProg(CELL_HEADER +
      'r1: cf_tok D 1 * cf_gd D -o { cf_tok D 2 * cf_gd D }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} },
      { ...CELL_DISC, guards: { cf_cell: 'cf_gd' } });
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'guard-production');
  });

  it('a cell produced with no guard mapping is refused', () => {
    const calc = loadProg(CELL_HEADER +
      'r1: cf_tok D 1 * cf_gd D -o { cf_tok D 2 * !cf_cell D 1 }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} }, CELL_DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'unguarded-cell-production');
  });

  it('a cell produced without consuming its guard at the key is refused', () => {
    const calc = loadProg(CELL_HEADER +
      'r1: cf_tok D 1 -o { cf_tok D 2 * !cf_cell D 1 }.\n');
    const cert = calc.certifyConfluence({ linear: {}, persistent: {} },
      { ...CELL_DISC, guards: { cf_cell: 'cf_gd' } });
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'unguarded-cell-production');
  });

  it('a dynamic rule (loli fact) in the initial state is refused', () => {
    const calc = loadProg(HEADER + 'r1: cf_tok D 1 -o { cf_tok D 2 }.\n');
    const st = illmde.decomposeQuery(
      illmde.parseExpr('(cf_tok 7 1 -o cf_out 7 1)', illmde.illConfig.loader));
    const cert = calc.certifyConfluence(st, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'dynamic-rule-in-state');
  });

  it('an unkeyed (non-predicate) state fact is refused', () => {
    // A bare unconsumed atom is an inert sink (predHead treats atoms as
    // nullary predicates) — the non-predicate case is a CONNECTIVE-tagged
    // fact, e.g. an external-choice formula sitting in the linear state.
    const calc = loadProg(HEADER +
      'r1: cf_tok D 1 -o { cf_tok D 2 }.\n');
    const st = illmde.decomposeQuery(
      illmde.parseExpr('(cf_out 7 1 & cf_out 7 2) * cf_tok 7 1', illmde.illConfig.loader));
    const cert = calc.certifyConfluence(st, DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'unkeyed-state-fact');
  });

  it('two cells at one key with distinct values are refused', () => {
    const calc = loadProg(CELL_HEADER + 'r1: cf_tok D 1 -o { cf_tok D 2 }.\n');
    const st = illmde.decomposeQuery(
      illmde.parseExpr('!cf_cell 7 1 * !cf_cell 7 2', illmde.illConfig.loader));
    const cert = calc.certifyConfluence(st, CELL_DISC);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'duplicate-persistent-value');
  });
});

describe('certifyConfluence: equality is modulo the equational theories', () => {
  // The kernel matcher unifies cross-tag (binlit 3 ~ i(i e)); the
  // certificate must reason at that level — hash-level equality would
  // grant false certificates (D2 values) or miss duplicate
  // destinations/keys (D6). ILL's loader CANONICALIZES i/o/e trees to
  // binlits at parse time, so program TEXT cannot exhibit the mixed
  // representations — but runtime states can (clause-derived i/o/e
  // trees meeting binlit facts), and calculi without canonicalization
  // feed the certifier directly. These pins therefore build rule data
  // and states at the STORE level, with the binlit theory registered
  // (any ILL load registers it), and call the raw certifier.
  let toy;
  before(() => {
    Store.clear();
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'confl-th-'));
    const file = path.join(tmpDir, 'p.ill');
    fs.writeFileSync(file, 'cf_tok: (d: bin) -> (v: bin) -> type.\nr1: cf_tok D 1 -o { cf_tok D 2 }.\n');
    try {
      toy = illmde.load(file, { cache: false }); // registers the binlit theory
    } finally {
      for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
      fs.rmdirSync(tmpDir);
    }
  });

  const bl = (n) => Store.put1('binlit', BigInt(n));
  const tree3 = () => Store.put('i', [Store.put('i', [Store.put('atom', ['e'])])]);
  const rule = (name, lin, goals, outLin) => ({
    name, hash: 0,
    antecedent: { linear: lin, persistent: goals },
    consequentAlts: [{ linear: outLin, persistent: [] }],
  });
  const OPTS = {
    rc: {}, dest: { cfs_tok: 0 }, dispatch: 'cfs_tok',
    persistentUnique: { cfs_cell: { keys: [0], values: [1] } },
  };
  const EMPTY = { linear: {}, persistent: {} };

  it('D2: theory-equal cell values are NOT a contradiction (binlit 3 ~ i(i e))', () => {
    // Identical dispatch patterns; the two rules demand the cell at the
    // same key with values i(i e) and binlit 3 — THE SAME value modulo
    // binlit. Hash-level 'distinct grounds ⇒ excluded' would grant a
    // false certificate here; the theory-aware check must refuse.
    const D1 = mv(), D2 = mv();
    const r1 = rule('r1', [Store.put('cfs_tok', [D1, bl(1)])],
      [Store.put('cfs_cell', [D1, tree3()])], [Store.put('cfs_tok', [D1, bl(2)])]);
    const r2 = rule('r2', [Store.put('cfs_tok', [D2, bl(1)])],
      [Store.put('cfs_cell', [D2, bl(3)])], [Store.put('cfs_tok', [D2, bl(3)])]);
    const cert = rawCertify([r1, r2], EMPTY, OPTS);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'overlapping-dispatch');
  });

  it('D2: genuinely distinct cell values still exclude (the SAX pattern survives)', () => {
    const D1 = mv(), D2 = mv();
    const r1 = rule('r1', [Store.put('cfs_tok', [D1, bl(1)])],
      [Store.put('cfs_cell', [D1, bl(3)])], [Store.put('cfs_tok', [D1, bl(2)])]);
    const r2 = rule('r2', [Store.put('cfs_tok', [D2, bl(1)])],
      [Store.put('cfs_cell', [D2, bl(4)])], [Store.put('cfs_tok', [D2, bl(3)])]);
    const cert = rawCertify([r1, r2], EMPTY, OPTS);
    assert.equal(cert.confluent, true, JSON.stringify(cert.witness || {}));
  });

  it('D6: theory-equal duplicate destinations are refused', () => {
    const D1 = mv();
    const r1 = rule('r1', [Store.put('cfs_tok', [D1, bl(1)])], [],
      [Store.put('cfs_tok', [D1, bl(2)])]);
    const f1 = Store.put('cfs_tok', [bl(3), bl(1)]);
    const f2 = Store.put('cfs_tok', [tree3(), bl(1)]);
    assert.notEqual(f1, f2, 'the two representations are hash-distinct');
    const cert = rawCertify([r1], { linear: { [f1]: 1, [f2]: 1 }, persistent: {} }, OPTS);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'duplicate-destination');
  });

  it('D6: theory-equal duplicate cell keys are refused', () => {
    const D1 = mv();
    const r1 = rule('r1', [Store.put('cfs_tok', [D1, bl(1)])], [],
      [Store.put('cfs_tok', [D1, bl(2)])]);
    const c1 = Store.put('cfs_cell', [bl(3), bl(1)]);
    const c2 = Store.put('cfs_cell', [tree3(), bl(1)]);
    assert.notEqual(c1, c2, 'the two representations are hash-distinct');
    const cert = rawCertify([r1],
      { linear: {}, persistent: { [c1]: true, [c2]: true } }, OPTS);
    assert.equal(cert.confluent, false);
    assert.equal(cert.witness.reason, 'duplicate-persistent-value');
  });
});

describe('certifyConfluence: precondition refusals (direct-call surface)', () => {
  it('a missing rc refuses (no-connective-info) — D5 must never silently no-op', () => {
    const r = rawCertify([], { linear: {}, persistent: {} }, { dispatch: 'x', dest: {} });
    assert.equal(r.confluent, false);
    assert.equal(r.witness.reason, 'no-connective-info');
  });

  it('a missing dispatch declaration refuses (no-dispatch-declared)', () => {
    const r = rawCertify([], { linear: {}, persistent: {} }, { rc: {} });
    assert.equal(r.confluent, false);
    assert.equal(r.witness.reason, 'no-dispatch-declared');
  });
});

describe('certifyConfluence: timed features are refused', () => {
  it('a delayed-consequent till rule is refused (timed-feature)', () => {
    Store.clear();
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'confl-td-'));
    const file = path.join(tmpDir, 'p.till');
    fs.writeFileSync(file,
      't_tok: (d: bin) -> (v: bin) -> type.\n' +
      'r1: t_tok D 1 -o { t_tok D 2 }@(1).\n');
    try {
      const calc = mde.load(file, { calculusConfig: tillConfig, cache: false });
      const cert = calc.certifyConfluence({ linear: {}, persistent: {} },
        { dest: { t_tok: 0 }, dispatch: 't_tok' });
      assert.equal(cert.confluent, false);
      assert.equal(cert.witness.reason, 'timed-feature');
    } finally {
      for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
      fs.rmdirSync(tmpDir);
    }
  });
});
