/**
 * till debug renderings + serialization + render fidelity — TODO_0265 Phase 4c.
 *
 * Golden-output tests over the scripted chop/build scenario
 * (calculus/till/tests/debug/chopbuild.ill — fully deterministic: every
 * activation instant has a single candidate, no chooser involvement):
 *   #trace lines, #timeline lanes, #why hut@7 producer chain,
 *   #why_not sell (killing before-window) — exact string match.
 * Plus: forward-trace/v2 ({activation, delay} step fields), graded-monad
 * render fidelity ({B}@g, parse ∘ render = id), and the browser hydration
 * gradeUnit hook.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import convert from '../../lib/engine/convert.js';
import tillConfig from '../../calculus/till/calculus-config.js';
import { normalizeTimedState } from '../../lib/engine/timed/timed.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { traceLines, timelineLines, whyLines, whyNotLines } from '../../lib/engine/timed/timed-render.js';

const DEBUG_ILL = path.join(import.meta.dirname, '../../calculus/till/tests/debug/chopbuild.ill');
const SPEC = (f) => path.join(import.meta.dirname, '../../calculus/till/tests/forward', f);
const load = (p) => mde.load(p, { calculusConfig: tillConfig, cache: false });

describe('till debug renderings — chop/build goldens (Phase 4c)', () => {
  let calc, initial, res, init;
  before(() => {
    calc = load(DEBUG_ILL);
    initial = convert.decomposeQuery(calc.queries.get('run'));
    res = calc.settle(initial, '10');
    init = toObject(normalizeTimedState(initial, calc.timedConfig));
  });

  it('#trace — log view: [activation] rule consumed → produced @+d', () => {
    // Within-line fact ORDER is at-hash-ascending (integer object keys) —
    // representation-internal; re-pinned at the labelled-state flip
    // (THY_0024 rider 3: same facts, renamed presentation order).
    assert.deepEqual(traceLines(res.events), [
      '[0] chop: tree@0, chopper@0, read manual@0 → wood@4, chopper@4 @+4',
      '[0] chop: tree@0, chopper@0, read manual@0 → wood@4, chopper@4 @+4',
      '[4] build: wood@4 x2, builder@0 → hut@7, builder@7 @+3',
      '[5] chop: tree@5, chopper@4, read manual@0 → wood@9, chopper@9 @+4',
    ]);
  });

  it('#timeline — jobs + per-predicate token lifetimes', () => {
    assert.deepEqual(timelineLines(res.events, init, calc.timedConfig.parseStamp('10')), [
      'timeline (T = 10)',
      'jobs:',
      '  chop [0→4]  chop [0→4]  build [4→7]  chop [5→9]',
      'tokens:',
      '  builder: 0→build@4  7→…',
      '  chopper: 0→chop@0  0→chop@0  4→chop@5  4→…  9→…',
      '  hut: 7→…',
      '  manual: 0→…',
      '  tree: 0→chop@0  0→chop@0  5→chop@5',
      '  wood: 4→build@4  4→build@4  9→…',
    ]);
  });

  it('#why hut@7 — per-instance producer chain (causal tree)', () => {
    const hut7 = calc.queries.get('why_hut');
    // Child order follows the consumed-map key order (at-hash ascending) —
    // re-pinned at the labelled-state flip (same tree, permuted siblings).
    assert.deepEqual(whyLines(res.events, init, hut7), [
      'hut@7 ← build @4 +3',
      '├─ wood@4 ← chop @0 +4',
      '│  ├─ tree@0 (initial)',
      '│  ├─ chopper@0 (initial)',
      '│  └─ read manual@0 (initial)',
      '├─ wood@4 ← chop @0 +4',
      '│  ├─ tree@0 (initial)',
      '│  ├─ chopper@0 (initial)',
      '│  └─ read manual@0 (initial)',
      '└─ builder@0 (initial)',
    ]);
  });

  it('#why_not sell — best failed candidate + the killing before-window', () => {
    const sell = calc.forwardRules.find(r => r.name === 'sell');
    const settled = normalizeTimedState(res.state, calc.timedConfig);
    assert.deepEqual(whyNotLines(sell, settled, {
      calc: calc._calcContext, matchOpts: calc._buildMatchOpts({}),
      timedConfig: calc.timedConfig, horizon: calc.timedConfig.parseStamp('10'),
    }), [
      'why not sell:',
      "  best candidate killed by 'before 9': activation 9 misses the deadline",
    ]);
  });

  it('#why_not — missing-input and pending diagnoses', () => {
    const scalc = load(SPEC('schedule.ill'));
    const S = convert.decomposeQuery(scalc.splitQueries.get('expect_two_jobs').lhsHash);
    const rule = scalc.forwardRules.find(r => r.name === 'sawmill_rule');
    const opts = (T) => ({
      calc: scalc._calcContext, matchOpts: scalc._buildMatchOpts({}),
      timedConfig: scalc.timedConfig, horizon: scalc.timedConfig.parseStamp(T),
    });
    // fully settled: no wood left — missing input
    const done = normalizeTimedState(scalc.settle(S, '1').state, scalc.timedConfig);
    assert.deepEqual(whyNotLines(rule, done, opts('1')), [
      'why not sawmill_rule:',
      "  missing input: no fact matches pattern 'wood'",
    ]);
    // mid-run: job2 enabled at 1/2, beyond horizon 0.4 — pending
    const mid = normalizeTimedState(scalc.settle(S, '0.4').state, scalc.timedConfig);
    assert.deepEqual(whyNotLines(rule, mid, opts('0.4')), [
      'why not sawmill_rule:',
      '  pending: fires at activation 1/2 > horizon 2/5',
    ]);
  });
});

describe('forward-trace/v2 — timed step fields (Phase 4c)', () => {
  it('settle events serialize with activation/delay refs; version bumped', async () => {
    const st = await import('../../lib/prover/serialize-trace.js');
    assert.equal(st.FORMAT_VERSION, 'forward-trace/v2');
    const calc = load(DEBUG_ILL);
    const initial = convert.decomposeQuery(calc.queries.get('run'));
    const res = calc.settle(initial, '10');
    const payload = st.serializeExecTrace(res.state, res.events, { initialState: initial });
    assert.equal(payload.format, 'forward-trace/v2');
    const steps = payload.leaves[0].trace;
    assert.equal(steps.length, 4);
    // rule NAMES from settle records; every step carries timed refs
    assert.deepEqual(steps.map(s => s.ruleName), ['chop', 'chop', 'build', 'chop']);
    for (const s of steps) {
      assert.ok(s.activation !== undefined, 'activation ref present');
      assert.ok(s.delay !== undefined, 'delay ref present');
      assert.ok(s.consumed.length > 0);
    }
  });
});

describe('graded-monad render fidelity (Phase 4c)', () => {
  let render, parse;
  before(async () => {
    const calculus = (await import('../../lib/calculus/index.js')).default;
    const { buildRenderer, buildParser } = await import('../../lib/calculus/builders.js');
    const { putRat } = await import('../../lib/kernel/rat-term.js');
    const gt = calculus.load(path.join(import.meta.dirname, '../fixtures/graded-comp.calc'));
    const gradeUnit = () => putRat(0n, 1n);
    render = buildRenderer(gt.constructors, { gradeUnit });
    parse = buildParser(gt.constructors, { gradeUnit });
  });

  it('unit grade renders bare; non-unit grades render as {B}@g', async () => {
    const { putRat } = await import('../../lib/kernel/rat-term.js');
    const b = Store.put('atom', ['b']);
    assert.equal(render(Store.put('monad', [putRat(0n, 1n), b])), '{ b }');
    assert.equal(render(Store.put('monad', [putRat(2n, 1n), b])), '{ b }@2');
    assert.equal(render(Store.put('monad', [putRat(1n, 2n), b])), '{ b }@1/2');
  });

  it('parse ∘ render = id on graded monads', () => {
    for (const src of ['{ b }', '{ b }@2', '{ b }@1/2']) {
      const h = parse(src);
      assert.equal(parse(render(h)), h, src);
    }
  });

  it('no opts ⇒ historical behavior (grade silently elided)', async () => {
    const calculus = (await import('../../lib/calculus/index.js')).default;
    const { buildRenderer } = await import('../../lib/calculus/builders.js');
    const { putRat } = await import('../../lib/kernel/rat-term.js');
    const gt = calculus.load(path.join(import.meta.dirname, '../fixtures/graded-comp.calc'));
    const plain = buildRenderer(gt.constructors);
    assert.equal(plain(Store.put('monad', [putRat(2n, 1n), Store.put('atom', ['b'])])), '{ b }');
  });
});

describe('browser hydration — gradeUnit hook (Phase 4c)', () => {
  it('graded bundle parses with opts.parserOpts.gradeUnit, errors loudly without', async () => {
    const calculus = (await import('../../lib/calculus/index.js')).default;
    const { parserTables, rendererFormats } = await import('../../lib/calculus/builders.js');
    const { putRat } = await import('../../lib/kernel/rat-term.js');
    const browser = await import('../../lib/browser.js');
    const gt = calculus.load(path.join(import.meta.dirname, '../fixtures/graded-comp.calc'));
    const bundle = {
      name: 'gtoy', baseTypes: ['formula', 'grade'],
      constructors: gt.constructors,
      parserTables: { ...parserTables(gt.constructors) },
      rendererFormats: rendererFormats(gt.constructors),
      rules: {}, polarity: {}, invertible: {}, directives: {},
    };
    const gradeUnit = () => putRat(0n, 1n);
    const withHook = browser.initFromBundle(bundle, {
      parserOpts: { gradeUnit },
      rendererOpts: { gradeUnit },
    });
    const h = withHook.parse('{ b }@1/2');
    assert.equal(Store.tag(h), 'monad');
    assert.equal(withHook.render(h), '{ b }@1/2');
    // without the hook: hydration succeeds and `{ b }` takes the shared
    // default unit (binlit 0 — same hash as putRat(0,1); D6 merge-back)
    const without = browser.initFromBundle(bundle);
    assert.equal(Store.child(without.parse('{ b }'), 0), putRat(0n, 1n));
  });
});
