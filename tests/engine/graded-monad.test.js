/**
 * Graded monad support in shared machinery — TODO_0265 Phase 2.
 *
 * The one shape every monad-aware site reads:
 *   roles.computation = { tag, bodyIdx, gradeIdx }
 *     ILL:  { 'monad',  bodyIdx: 0, gradeIdx: null }
 *     till: { 'gmonad', bodyIdx: 1, gradeIdx: 0 }
 * plus the grade classification record { grade0, gradeOmega } (functions —
 * recompute-on-demand invariant) carried on the resolved connectives.
 *
 * These tests drive every generalized site with a 2-ary computation
 * connective (via the gtoy fixture calculus and hand-built connective
 * tables) AND pin the ILL default shapes as regressions. The full ILL
 * suite passing bit-identically is the other half of the gate (D13).
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import Seq from '../../lib/kernel/sequent.js';
import calculus from '../../lib/calculus/index.js';
import { computationRole, resolveConn, flattenAnte, unwrapComp } from '../../lib/engine/formula-utils.js';
import { grade0, gradeW, defaultGradeConfig } from '../../lib/engine/grades.js';
import { monadRules } from '../../lib/calculus/modes.js';
import { compileRule } from '../../lib/engine/compile.js';
import { earleyGrammarFromTables, parserFromGrammar } from '../../lib/parser/earley-grammar.js';
import { desugarPreserved } from '../../lib/engine/convert.js';
import { makeClauseTermBuilder, buildClauseTerm } from '../../lib/engine/ill/backchain-ill.js';
import { rightFocus } from '../../lib/prover/bridge.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { createChecker } from '../../lib/prover/check-term.js';
import { ILL_CONNECTIVES } from '../../lib/engine/ill/connectives.js';

const FIXTURE = path.join(import.meta.dirname, '../fixtures/graded-comp.calc');

const GCOMP = { tag: 'gmonad', bodyIdx: 1, gradeIdx: 0 };
const ICOMP = { tag: 'monad', bodyIdx: 0, gradeIdx: null };

// A 2-ary-monad connective table (till shape: ILL connectives, graded monad)
const TILL_CT = {
  tensor: { category: 'multiplicative', arity: 2, polarity: 'positive' },
  loli: { category: 'multiplicative', arity: 2, polarity: 'negative' },
  bang: { category: 'exponential', arity: 2 },
  gmonad: { category: 'monad', arity: 2 },
};

const atom = (n) => Store.put('atom', [n]);
const gm = (g, b) => Store.put('gmonad', [g, b]);

describe('computationRole / resolveConn', () => {
  it('derives the record by arity; other arities get no role', () => {
    assert.deepEqual(computationRole('monad', 1), ICOMP);
    assert.deepEqual(computationRole('gmonad', 2), GCOMP);
    assert.equal(computationRole('weird', 3), null);
    assert.equal(computationRole('weird', 0), null);
  });

  it('resolveConn: ILL yields the unary record + default grade functions', () => {
    const rc = resolveConn(ILL_CONNECTIVES);
    assert.deepEqual(rc.computation, ICOMP);
    assert.equal(rc.grade0, defaultGradeConfig.grade0);
    assert.equal(rc.grade0(), grade0());
    assert.equal(rc.gradeOmega(), gradeW());
  });

  it('resolveConn: 2-ary monad yields the graded record; custom gradeConfig sticks', () => {
    const g0 = () => atom('tg0');
    const gw = () => atom('tgw');
    const rc = resolveConn(TILL_CT, { grade0: g0, gradeOmega: gw });
    assert.deepEqual(rc.computation, GCOMP);
    assert.equal(rc.product, 'tensor');
    assert.equal(rc.grade0(), atom('tg0'));
    assert.equal(rc.gradeOmega(), atom('tgw'));
  });
});

describe('walkers: unwrapComp / flattenAnte', () => {
  it('unwrapComp reads bodyIdx from the record', () => {
    const rcI = resolveConn(ILL_CONNECTIVES);
    const rcG = resolveConn(TILL_CT);
    const b = atom('b');
    assert.equal(unwrapComp(Store.put('monad', [b]), rcI), b);
    assert.equal(unwrapComp(gm(atom('g'), b), rcG), b);
    assert.equal(unwrapComp(b, rcG), b); // non-computation unchanged
  });

  it('flattenAnte classifies bang grades via the rc grade functions', () => {
    const rc = resolveConn(TILL_CT, {
      grade0: () => atom('tg0'), gradeOmega: () => atom('tgw'),
    });
    const a = atom('a'), b = atom('b'), c = atom('c');
    const h = Store.put('tensor', [
      Store.put('bang', [atom('tg0'), a]),
      Store.put('tensor', [Store.put('bang', [atom('tgw'), b]), c]),
    ]);
    const flat = flattenAnte(h, rc);
    assert.deepEqual(flat.grade0, [a]);
    assert.deepEqual(flat.persistent, [b]);
    assert.deepEqual(flat.linear, [c]);
  });

  it('flattenAnte default grades are ILL atoms (regression)', () => {
    const rc = resolveConn(ILL_CONNECTIVES);
    const a = atom('a');
    const flat = flattenAnte(Store.put('bang', [grade0(), a]), rc);
    assert.deepEqual(flat.grade0, [a]);
  });
});

describe('monadRules descriptors', () => {
  it('default is ILL, bit-identical to the historical shape', () => {
    const r = monadRules();
    assert.deepEqual(Object.keys(r), ['monad_r', 'monad_l']);
    assert.deepEqual(r.monad_r.descriptor, {
      connective: 'monad', side: 'r', arity: 1,
      copyContext: false, emptyLinear: false, contextSplit: false,
      contextFlow: 'axiom', modeShift: true,
      premises: [],
    });
    assert.deepEqual(r.monad_l.descriptor, {
      connective: 'monad', side: 'l', arity: 1,
      copyContext: false, emptyLinear: false, contextSplit: false,
      contextFlow: 'preserved',
      requiresSuccedentTag: 'monad',
      premises: [{ linear: [0] }],
    });
  });

  it('graded computation: names, arity, sticky tag, body premise index follow the record', () => {
    const r = monadRules(GCOMP);
    assert.deepEqual(Object.keys(r), ['gmonad_r', 'gmonad_l']);
    assert.equal(r.gmonad_r.descriptor.connective, 'gmonad');
    assert.equal(r.gmonad_r.descriptor.arity, 2);
    assert.equal(r.gmonad_r.descriptor.modeShift, true);
    assert.equal(r.gmonad_l.descriptor.requiresSuccedentTag, 'gmonad');
    assert.deepEqual(r.gmonad_l.descriptor.premises, [{ linear: [1] }]);
  });
});

describe('compileRule with a graded computation', () => {
  it('unwraps the graded consequent and compiles triggers normally', () => {
    const X = Store.put('metavar', ['X']);
    const p = Store.put('p', [X]);
    const q = Store.put('q', [X]);
    const rHead = Store.put('r', [X]);
    const hash = Store.put('loli', [
      Store.put('tensor', [p, q]),
      gm(atom('g'), rHead),
    ]);
    const rule = {
      name: 'toy', hash,
      antecedent: Store.child(hash, 0),
      consequent: Store.child(hash, 1),
    };
    const compiled = compileRule(rule, { connectives: TILL_CT });
    assert.deepEqual(compiled.triggerPreds.sort(), ['p', 'q']);
    assert.equal(compiled.consequentAlts.length, 1);
    assert.deepEqual(compiled.consequentAlts[0].linear, [rHead]);
  });
});

describe('grammar: { ... } builds the configured computation node', () => {
  it('2-ary computation with gradeUnit hook (ATOM form and loli-monad form)', () => {
    const unit = () => atom('u0');
    const tables = {
      operators: [], nullary: {}, unaryPrefix: {},
      forwardRules: true,
      computation: GCOMP, gradeUnit: unit,
    };
    const parse = parserFromGrammar(earleyGrammarFromTables(tables));
    const h = parse('{ b }');
    assert.equal(Store.tag(h), 'gmonad');
    assert.equal(Store.child(h, 0), atom('u0'));
    assert.equal(Store.tag(Store.child(h, 1)), 'atom');

    const fwd = parse('a -o { b }');
    assert.equal(Store.tag(fwd), 'loli');
    const conseq = Store.child(fwd, 1);
    assert.equal(Store.tag(conseq), 'gmonad');
    assert.equal(Store.child(conseq, 0), atom('u0'));
  });

  it('graded computation without gradeUnit throws a clear error', () => {
    const tables = {
      operators: [], nullary: {}, unaryPrefix: {},
      computation: GCOMP,
    };
    const parse = parserFromGrammar(earleyGrammarFromTables(tables));
    assert.throws(() => parse('{ b }'), /gradeUnit/);
  });

  it('default tables still build ILL unary monad (regression)', () => {
    const parse = parserFromGrammar(earleyGrammarFromTables(
      { operators: [], nullary: {}, unaryPrefix: {} }));
    const h = parse('{ b }');
    assert.equal(Store.tag(h), 'monad');
    assert.equal(Store.arity(h), 1);
  });
});

describe('desugarPreserved threads the grade (D7: timed-$)', () => {
  it('graded: $p * a -o {b}@g keeps the grade and injects p into the body', () => {
    const p = atom('p'), a = atom('a'), b = atom('b'), g = atom('g');
    const h = Store.put('loli', [
      Store.put('tensor', [Store.put('preserved', [p]), a]),
      gm(g, b),
    ]);
    const out = desugarPreserved(h, GCOMP);
    const conseq = Store.child(out, 1);
    assert.equal(Store.tag(conseq), 'gmonad');
    assert.equal(Store.child(conseq, 0), g, 'grade preserved');
    assert.equal(Store.child(conseq, 1), Store.put('tensor', [p, b]));
    assert.equal(Store.child(out, 0), Store.put('tensor', [p, a]));
  });

  it('default stays unary monad (regression)', () => {
    const p = atom('p'), b = atom('b');
    const h = Store.put('loli', [
      Store.put('preserved', [p]),
      Store.put('monad', [b]),
    ]);
    const out = desugarPreserved(h);
    assert.equal(out, Store.put('loli', [p, Store.put('monad', [Store.put('tensor', [p, b])])]));
  });
});

describe('clause term builder', () => {
  it('default instance is the ILL shape (regression)', () => {
    const prem = atom('pr'), head = atom('hd');
    const idTerm = { rule: 'id', principal: prem, subterms: [] };
    const t = buildClauseTerm([prem], [idTerm], head);
    assert.equal(t.rule, 'copy');
    const loliApp = t.subterms[0];
    assert.equal(loliApp.rule, 'loli_l');
    assert.equal(loliApp.subterms[1].rule, 'monad_l');
    assert.equal(Store.tag(loliApp.subterms[1].principal), 'monad');
  });

  it('graded builder constructs <tag>(unit, head) and names <tag>_l', () => {
    const build = makeClauseTermBuilder({
      computation: GCOMP, gradeUnit: () => atom('u0'),
    });
    const prem = atom('pr'), head = atom('hd');
    const idTerm = { rule: 'id', principal: prem, subterms: [] };
    const t = build([prem], [idTerm], head);
    const monadBody = t.subterms[0].subterms[1];
    assert.equal(monadBody.rule, 'gmonad_l');
    assert.equal(Store.tag(monadBody.principal), 'gmonad');
    assert.equal(Store.child(monadBody.principal, 0), atom('u0'));
    assert.equal(Store.child(monadBody.principal, 1), head);
  });

  it('graded builder without gradeUnit throws', () => {
    assert.throws(() => makeClauseTermBuilder({ computation: GCOMP })([], [], atom('h')),
      /gradeUnit/);
  });
});

describe('gtoy fixture calculus (end-to-end: loader → kernel → checker)', () => {
  let gtoy;

  before(() => {
    calculus.clearCache();
    gtoy = calculus.load(FIXTURE);
  });

  it('derives the graded computation role and injects <tag>_r/<tag>_l rules', () => {
    assert.deepEqual(gtoy.roles.computation, GCOMP);
    assert.ok(gtoy.rules.gmonad_r, 'gmonad_r injected');
    assert.ok(gtoy.rules.gmonad_l, 'gmonad_l injected');
    assert.equal(gtoy.rules.monad_r, undefined, 'no ILL-named monad rules');
    assert.equal(gtoy.rules.gmonad_r.descriptor.arity, 2);
    assert.deepEqual(gtoy.rules.gmonad_l.descriptor.premises, [{ linear: [1] }]);
  });

  it('kernel verifies the mode-switch step against the graded succedent tag', () => {
    const kernel = createKernel(gtoy);
    const node = gm(atom('g'), atom('b'));
    const good = kernel.verifyStep(Seq.fromArrays([], [], node), 'gmonad_r', [], null);
    assert.equal(good.valid, true);
    assert.equal(good.unverified, 'modeSwitch');

    const bad = kernel.verifyStep(
      Seq.fromArrays([], [], Store.put('tensor', [atom('a'), atom('b')])),
      'gmonad_r', [], null);
    assert.equal(bad.valid, false);
    assert.match(bad.error, /succedent is not monadic/);
  });

  it('checkTerm accepts a hand-built graded monad_r/monad_l instance', () => {
    const { check } = createChecker(gtoy);
    const b = atom('b');
    const node = gm(atom('g'), b);
    // ⊢ {b}@g from {b}@g: gmonad_r whose evidence opens the linear copy
    // via gmonad_l and closes with id on the body.
    const term = {
      rule: 'gmonad_r', principal: null, subterms: [],
      evidence: {
        rule: 'gmonad_l', principal: node,
        subterms: [{ rule: 'id', principal: b, subterms: [] }],
      },
    };
    const res = check(term, Seq.fromArrays([node], [], node));
    assert.equal(res.valid, true, res.error);
    assert.equal(res.unverified, undefined, 'fully verified, no opaque gap');
  });

  it('checker enforces lax stickiness for the graded left rule', () => {
    const { check } = createChecker(gtoy);
    const b = atom('b');
    const node = gm(atom('g'), b);
    // gmonad_l at top level (outside gmonad_r) must fail — |-_lax only.
    const term = {
      rule: 'gmonad_l', principal: node,
      subterms: [{ rule: 'id', principal: b, subterms: [] }],
    };
    const res = check(term, Seq.fromArrays([node], [], b));
    assert.equal(res.valid, false);
    assert.match(res.error, /not in lax mode/);
  });

  it('rightFocus rejects the graded computation node as async (by role record)', () => {
    const node = gm(atom('g'), atom('b'));
    assert.equal(rightFocus({ [node]: 1 }, {}, node, gtoy.roles), null);
    // plain atoms still decompose
    const a = atom('a');
    assert.deepEqual(rightFocus({ [a]: 1 }, {}, a, gtoy.roles), {});
  });
});
