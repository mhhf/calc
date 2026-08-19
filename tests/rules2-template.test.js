/**
 * Template rules in the .rules DSL — TODO_0265 Phase 6b Stage 1 (D1).
 *
 * A rule becomes a TEMPLATE rule when it carries @grade lines, @template
 * true, or a compound premise formula. Template rules match their principal
 * (and, for left rules, the conclusion succedent) by one-way unification —
 * pattern metavars bind, sequent content is rigid — then evaluate grade
 * side conditions through the calculus's grade-algebra record (D13: the
 * SAME record the timed scheduler reads), and instantiate premise formulas
 * by substitution. Index-based rules (all of ill.rules) are untouched: no
 * @grade / @template / compound premise ⇒ descriptor is byte-identical to
 * before (the D13 zero-delta gate).
 *
 * @grade forms:  X := A + B / X := A - B  (definition; monus — a negative
 * result makes the rule inapplicable, grades are ℚ≥0 in v1) and
 * A OP B with OP ∈ {=, <, >, <=, >=} (guard; non-numeric grades — the ω/0
 * ATOMS — fail guards, they are matched structurally by writing !A).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import calculus from '../lib/calculus/index.js';
import Store from '../lib/kernel/store.js';
import { buildParser } from '../lib/calculus/builders.js';
import { parseRules2 } from '../lib/rules/rules2-parser.js';
import { tillGrades, tillGradeUnit } from '../calculus/till/calculus-config.js';

const TILL_CALC = path.join(import.meta.dirname, '../calculus/till/till.calc');

describe('.rules template extension (graded side conditions)', () => {
  let parse;

  before(() => {
    const cs = calculus.load(TILL_CALC).constructors;
    parse = buildParser(cs, {
      multiCharFreevars: true, numbers: true,
      timedAnnotations: true, gradeUnit: tillGradeUnit,
    });
  });

  const rules = (text, opts = { grades: tillGrades }) =>
    parseRules2('@formulas A, B, C\n\n' + text, parse, opts);

  it('a @grade rule compiles to a template descriptor', () => {
    const r = rules(
      'bang_l3: G ; D, !_K A |- C\n' +
      '  <- G ; D, A, !_J A |- C\n' +
      '  @grade K >= 1\n' +
      '  @grade J := K - 1.\n');
    const d = r.bang_l3.descriptor;
    assert.strictEqual(d.connective, 'bang');
    assert.strictEqual(d.side, 'l');
    assert.ok(d.template, 'template record present');
    assert.strictEqual(Store.tag(d.template.principal), 'bang');
    assert.strictEqual(Store.tag(d.template.succedent), 'metavar');
    assert.strictEqual(d.template.steps.length, 2);
    assert.strictEqual(d.template.steps[0].kind, 'guard');
    assert.strictEqual(d.template.steps[1].kind, 'def');
    assert.strictEqual(d.template.premises.length, 1);
    assert.strictEqual(d.template.premises[0].linear.length, 2);
  });

  it('@template true forces template mode without grade steps (ω rules)', () => {
    const r = rules(
      'bang_l: G ; D, !A |- C\n' +
      '  <- G ; D, A |- C\n' +
      '  @template true.\n');
    const t = r.bang_l.descriptor.template;
    assert.ok(t);
    assert.strictEqual(t.steps.length, 0);
    // the ω grade is part of the pattern — structural restriction
    assert.strictEqual(Store.child(t.principal, 0), Store.put('atom', ['gw']));
  });

  it('a compound premise formula forces template mode', () => {
    const r = rules(
      'bang_r2: G ; D, D\' |- !_K A\n' +
      '  <- G ; D |- A\n' +
      '  <- G ; D\' |- !_J A\n' +
      '  @grade K >= 1\n' +
      '  @grade J := K - 1.\n');
    assert.ok(r.bang_r2.descriptor.template);
    assert.ok(r.bang_r2.descriptor.contextSplit, 'split context flow preserved');
    // right rule: the principal IS the succedent — no separate pattern
    assert.strictEqual(r.bang_r2.descriptor.template.succedent, null);
  });

  it('@side l overrides principal detection (monadic succedent stays a pattern)', () => {
    const r = rules(
      'gmonad_l: G ; D, {A}@E |- {C}@F\n' +
      '  <- G ; D, A |- {C}@H\n' +
      '  @side l\n' +
      '  @grade H := F - E.\n');
    const d = r.gmonad_l.descriptor;
    assert.strictEqual(d.side, 'l');
    assert.strictEqual(d.connective, 'gmonad');
    assert.strictEqual(Store.tag(d.template.principal), 'gmonad');
    assert.strictEqual(Store.tag(d.template.succedent), 'gmonad');
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

    it('rejects a def that shadows a bound variable', () => {
      assert.throws(() => rules(
        'bad: G ; D, !_K A |- C\n' +
        '  <- G ; D |- C\n' +
        '  @grade K := K - 1.\n'), /already bound/);
    });

    it('rejects a guard over an unknown variable', () => {
      assert.throws(() => rules(
        'bad: G ; D, !_K A |- C\n' +
        '  <- G ; D |- C\n' +
        '  @grade Z >= 1.\n'), /unbound|unknown/);
    });

    it('rejects @grade without a grade algebra', () => {
      assert.throws(() => rules(
        'bad: G ; D, !_K A |- C\n' +
        '  <- G ; D |- C\n' +
        '  @grade K = 0.\n', {}), /grade algebra|grades/);
    });

    it('rejects malformed @grade lines', () => {
      assert.throws(() => rules(
        'bad: G ; D, !_K A |- C\n' +
        '  <- G ; D |- C\n' +
        '  @grade K bogus 1.\n'), /@grade/);
    });
  });
});
