/**
 * Template rules in the .rules DSL — TODO_0265 Phase 6b Stage 1 (D1),
 * theory-premise surface TODO_0273.
 *
 * A rule becomes a TEMPLATE rule when it carries theory premises,
 * @template true, or a compound premise formula. Template rules match their
 * principal (and, for left rules, the conclusion succedent) by one-way
 * unification — pattern metavars bind, sequent content is rigid — then
 * discharge THEORY PREMISES (`<- !pred args` lines, no turnstile) through
 * the calculus's theory engine, and instantiate premise formulas by
 * substitution. Index-based rules (all of ill.rules) are untouched: no
 * theory premise / @template / compound premise ⇒ descriptor is
 * byte-identical to before (the D13 zero-delta gate).
 *
 * Theory premises replace the former @grade annotation (TODO_0273): grade
 * side conditions are goals over the numeric theory (`!qsub F E H` binds H
 * to F ⊖ E, underivable out of fence; `!le A B` / `!eq A B` are guards).
 * Variables not bound by the conclusion are OUTPUT vars, bound by the
 * derivation and visible to later goals and the sequent premises.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import calculus from '../lib/calculus/index.js';
import Store from '../lib/kernel/store.js';
import { buildParser } from '../lib/calculus/builders.js';
import { parseRules2 } from '../lib/rules/rules2-parser.js';
import { tillGradeUnit } from '../calculus/till/calculus-config.js';

const TILL_CALC = path.join(import.meta.dirname, '../calculus/till/till.calc');

describe('.rules template extension (theory premises)', () => {
  let parse;

  before(() => {
    const cs = calculus.load(TILL_CALC).constructors;
    parse = buildParser(cs, {
      multiCharFreevars: true, numbers: true,
      gradeUnit: tillGradeUnit,
    });
  });

  const rules = (text) => parseRules2('@formulas A, B, C\n\n' + text, parse);
  const mv = (name) => Store.put('metavar', [name]);

  it('a theory-premise rule compiles to a template descriptor', () => {
    const r = rules(
      'bang_l3: G ; D, !_K A |- C\n' +
      '  <- G ; D, A, !_J A |- C\n' +
      '  <- !qsub K 1 J.\n');
    const d = r.bang_l3.descriptor;
    assert.strictEqual(d.connective, 'bang');
    assert.strictEqual(d.side, 'l');
    assert.ok(d.template, 'template record present');
    assert.strictEqual(Store.tag(d.template.principal), 'bang');
    assert.strictEqual(Store.tag(d.template.succedent), 'metavar');
    assert.strictEqual(d.template.theoryGoals.length, 1);
    const tg = d.template.theoryGoals[0];
    assert.strictEqual(Store.tag(tg.goal), 'qsub');
    // K comes from the conclusion; J is an OUTPUT var bound by the proof
    assert.deepStrictEqual(tg.outs, [mv('J')]);
    assert.strictEqual(d.template.premises.length, 1);
    assert.strictEqual(d.template.premises[0].linear.length, 2);
    // theory goals do not count as sequent premises
    assert.strictEqual(r.bang_l3.numPremises, 1);
  });

  it('@template true forces template mode without theory goals (ω rules)', () => {
    const r = rules(
      'bang_l: G ; D, !A |- C\n' +
      '  <- G ; D, A |- C\n' +
      '  @template true.\n');
    const t = r.bang_l.descriptor.template;
    assert.ok(t);
    assert.strictEqual(t.theoryGoals.length, 0);
    // the ω grade is part of the pattern — structural restriction
    assert.strictEqual(Store.child(t.principal, 0), Store.put('atom', ['gw']));
  });

  it('a compound premise formula forces template mode', () => {
    const r = rules(
      'bang_r2: G ; D, D\' |- !_K A\n' +
      '  <- G ; D |- A\n' +
      '  <- G ; D\' |- !_J A\n' +
      '  <- !qsub K 1 J.\n');
    assert.ok(r.bang_r2.descriptor.template);
    assert.ok(r.bang_r2.descriptor.contextSplit, 'split context flow preserved');
    // right rule: the principal IS the succedent — no separate pattern
    assert.strictEqual(r.bang_r2.descriptor.template.succedent, null);
  });

  it('@side l overrides principal detection (monadic succedent stays a pattern)', () => {
    const r = rules(
      'monad_l: G ; D, {A}@E |- {C}@F\n' +
      '  <- G ; D, A |- {C}@H\n' +
      '  <- !qsub F E H\n' +
      '  @side l.\n');
    const d = r.monad_l.descriptor;
    assert.strictEqual(d.side, 'l');
    assert.strictEqual(d.connective, 'monad');
    assert.strictEqual(Store.tag(d.template.principal), 'monad');
    assert.strictEqual(Store.tag(d.template.succedent), 'monad');
    // F, E are conclusion-bound inputs; H is the derivation's output
    assert.deepStrictEqual(d.template.theoryGoals[0].outs, [mv('H')]);
  });

  it('a zero-premise rule with a theory goal stays a template axiom', () => {
    const r = rules(
      'at_l: G ; D, A@T1 |- A@T2\n' +
      '  <- !le T1 T2\n' +
      '  @side l.\n');
    const d = r.at_l.descriptor;
    assert.ok(d.template);
    assert.strictEqual(r.at_l.numPremises, 0);
    assert.strictEqual(d.template.theoryGoals.length, 1);
    assert.deepStrictEqual(d.template.theoryGoals[0].outs, []);
  });

  it('literals in theory goals parse through the formula parser', () => {
    const r = rules(
      'bang_l4: G ; D, !_K A |- C\n' +
      '  <- G ; D |- C\n' +
      '  <- !eq K 0.\n');
    const tg = r.bang_l4.descriptor.template.theoryGoals[0];
    assert.strictEqual(Store.tag(Store.child(tg.goal, 1)), 'binlit');
  });

  it('plain rules stay index-based (zero-delta): no template field', () => {
    const r = rules(
      'tensor_l: G ; D, A * B |- C\n' +
      '  <- G ; D, A, B |- C.\n');
    assert.strictEqual(r.tensor_l.descriptor.template, undefined);
    assert.deepStrictEqual(r.tensor_l.descriptor.premises, [{ linear: [0, 1] }]);
  });

  describe('load-time validation (loud errors)', () => {
    it('rejects a premise variable bound nowhere', () => {
      // Z occurs only in the premise (a bare uppercase token would be read
      // as a context var, so the loose var sits inside a compound pattern)
      assert.throws(() => rules(
        'bad: G ; D, A * B |- C\n' +
        '  <- G ; D, !_Z A |- C.\n'), /unbound/);
    });

    it('a theory output var satisfies premise boundness', () => {
      // same shape as above, but !_J A is grounded by the qsub derivation
      const r = rules(
        'ok: G ; D, !_K A |- C\n' +
        '  <- G ; D, !_J A |- C\n' +
        '  <- !qsub K 1 J.\n');
      assert.ok(r.ok.descriptor.template);
    });

    it('rejects the removed @grade annotation with a migration hint', () => {
      assert.throws(() => rules(
        'bad: G ; D, !_K A |- C\n' +
        '  <- G ; D |- C\n' +
        '  @grade K = 0.\n'), /@grade was removed.*theory premise/);
    });

    it('rejects malformed theory premises', () => {
      assert.throws(() => rules(
        'bad: G ; D, !_K A |- C\n' +
        '  <- G ; D |- C\n' +
        '  <- !K bogus.\n'), /malformed theory premise/);
      assert.throws(() => rules(
        'bad: G ; D, !_K A |- C\n' +
        '  <- G ; D |- C\n' +
        '  <- !qsub.\n'), /malformed theory premise/);
    });
  });
});
