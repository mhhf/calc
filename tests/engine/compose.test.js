/**
 * Tests for grade-0 cut elimination (TODO 156).
 * L1: composePair, L2: buildPredicateMap, L3: composeGrade0
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { GRADE_0, GRADE_W } = require('../../lib/engine/grades');
const { ILL_CONNECTIVES } = require('../../lib/engine/ill/connectives');
const { resolveConnectives, compileRule, flattenAntecedent, unwrapComputation } = require('../../lib/engine/compile');
const { getPredicateHead } = require('../../lib/kernel/ast');
const { composePair, buildPredicateMap, composeGrade0 } = require('../../lib/engine/compose');
const { getModes } = require('../../lib/engine/opt/ffi');

const COMPILE_OPTS = { connectives: ILL_CONNECTIVES, getModes };

/**
 * Helper: build and compile a raw forward rule from Store hashes.
 * @param {string} name - Rule name
 * @param {number} anteHash - Antecedent formula hash
 * @param {number} conseqBodyHash - Consequent body (unwrapped from monad)
 * @returns {Object} compiled rule
 */
function makeRule(name, anteHash, conseqBodyHash) {
  const conseqHash = Store.put('monad', [conseqBodyHash]);
  const hash = Store.put('loli', [anteHash, conseqHash]);
  return compileRule(
    { name, hash, antecedent: anteHash, consequent: conseqHash },
    COMPILE_OPTS
  );
}

/**
 * Helper: tensor from array of hashes.
 */
function tensor(...hashes) {
  if (hashes.length === 0) return Store.put('one', []);
  if (hashes.length === 1) return hashes[0];
  let acc = hashes[hashes.length - 1];
  for (let i = hashes.length - 2; i >= 0; i--) {
    acc = Store.put('tensor', [hashes[i], acc]);
  }
  return acc;
}

// ─── L2: buildPredicateMap ──────────────────────────────────────────────────

describe('compose L2: buildPredicateMap', () => {
  beforeEach(() => Store.clear());

  it('single producer + single consumer correctly classified', () => {
    // Producer: a -o { !_0 step X }
    const a = Store.put('atom', ['a']);
    const X = Store.put('metavar', ['X']);
    const stepX = Store.put('step', [X]);
    const bang0step = Store.put('bang', [GRADE_0, stepX]);

    const producer = makeRule('prod', a, bang0step);

    // Consumer: !_0 step Y -o { b }
    const Y = Store.put('metavar', ['Y']);
    const stepY = Store.put('step', [Y]);
    const bang0stepY = Store.put('bang', [GRADE_0, stepY]);
    const b = Store.put('atom', ['b']);

    const consumer = makeRule('cons', bang0stepY, b);

    const map = buildPredicateMap([producer, consumer]);
    assert.equal(map.size, 1);
    assert.ok(map.has('step'));
    const entry = map.get('step');
    assert.equal(entry.producers.length, 1);
    assert.equal(entry.consumers.length, 1);
    assert.equal(entry.bridges.length, 0);
    assert.equal(entry.producers[0].name, 'prod');
    assert.equal(entry.consumers[0].name, 'cons');
  });

  it('bridge rule detected (consumes pred A, produces pred B)', () => {
    // Bridge: !_0 raw OP -o { !_0 step OP }
    const OP = Store.put('metavar', ['OP']);
    const rawOP = Store.put('raw', [OP]);
    const bang0raw = Store.put('bang', [GRADE_0, rawOP]);
    const stepOP = Store.put('step', [OP]);
    const bang0step = Store.put('bang', [GRADE_0, stepOP]);

    const bridge = makeRule('bridge', bang0raw, bang0step);

    const map = buildPredicateMap([bridge]);
    assert.equal(map.size, 2);
    assert.ok(map.has('raw'));
    assert.ok(map.has('step'));
    assert.equal(map.get('raw').consumers.length, 1);
    assert.equal(map.get('step').producers.length, 1);
    // Bridge detected for both preds
    assert.equal(map.get('raw').bridges.length, 1);
    assert.equal(map.get('step').bridges.length, 1);
  });

  it('non-grade0 rules are ignored', () => {
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);
    const normal = makeRule('normal', a, b);
    const map = buildPredicateMap([normal]);
    assert.equal(map.size, 0);
  });
});

// ─── L1: composePair ────────────────────────────────────────────────────────

describe('compose L1: composePair', () => {
  let rc;
  beforeEach(() => {
    Store.clear();
    rc = resolveConnectives(ILL_CONNECTIVES);
  });

  it('basic two-rule composition', () => {
    // Producer: a X -o { !_0 mid X }
    const X = Store.put('metavar', ['X']);
    const aX = Store.put('a', [X]);
    const midX = Store.put('mid', [X]);
    const bang0mid = Store.put('bang', [GRADE_0, midX]);
    const producer = makeRule('prod', aX, bang0mid);

    // Consumer: !_0 mid Y * b Y -o { c Y }
    const Y = Store.put('metavar', ['Y']);
    const midY = Store.put('mid', [Y]);
    const bang0midY = Store.put('bang', [GRADE_0, midY]);
    const bY = Store.put('b', [Y]);
    const cY = Store.put('c', [Y]);
    const consumer = makeRule('cons', tensor(bang0midY, bY), cY);

    const result = composePair(producer, consumer, 'mid', rc);
    assert.ok(result, 'should produce a composed rule');
    assert.equal(result.name, 'cons:prod');

    // Verify the composed rule flattens correctly
    const anteFlat = flattenAntecedent(result.antecedent, rc);
    const conseqFlat = flattenAntecedent(unwrapComputation(result.consequent, rc), rc);

    // Antecedent should have: a(?) and b(?) — no grade-0
    assert.equal(anteFlat.grade0.length, 0, 'no grade-0 in composed ante');
    assert.equal(anteFlat.linear.length, 2, 'two linear patterns in ante');
    assert.equal(anteFlat.persistent.length, 0, 'no persistent in ante');

    // Consequent should have: c(?) — no grade-0
    assert.equal(conseqFlat.grade0.length, 0, 'no grade-0 in composed conseq');
    assert.equal(conseqFlat.linear.length, 1, 'one linear in conseq');
  });

  it('composed rule hash matches longhand', () => {
    // This is the key property: compose(prod, cons) ≡ longhand
    //
    // Producer: p X -o { !_0 mid X }
    // Consumer: !_0 mid Y -o { q Y }
    // Longhand: p Z -o { q Z }
    //
    // Composed should produce the same flattened structure.

    const X = Store.put('metavar', ['X']);
    const pX = Store.put('p', [X]);
    const midX = Store.put('mid', [X]);
    const producer = makeRule('prod', pX, Store.put('bang', [GRADE_0, midX]));

    const Y = Store.put('metavar', ['Y']);
    const midY = Store.put('mid', [Y]);
    const qY = Store.put('q', [Y]);
    const consumer = makeRule('cons', Store.put('bang', [GRADE_0, midY]), qY);

    const composed = composePair(producer, consumer, 'mid', rc);
    assert.ok(composed);

    // Build longhand: p Z -o { q Z }
    const Z = Store.put('metavar', ['Z']);
    const pZ = Store.put('p', [Z]);
    const qZ = Store.put('q', [Z]);
    const longhand = makeRule('longhand', pZ, qZ);

    // The composed rule's antecedent should have one linear pattern with pred 'p'
    // NOTE: composed returns raw hashes; longhand is compiled — derive raw from .hash
    const cAnteFlat = flattenAntecedent(composed.antecedent, rc);
    const lAnteFlat = flattenAntecedent(Store.child(longhand.hash, 0), rc);
    assert.equal(cAnteFlat.linear.length, lAnteFlat.linear.length);
    assert.equal(getPredicateHead(cAnteFlat.linear[0]), getPredicateHead(lAnteFlat.linear[0]));

    const cConseqFlat = flattenAntecedent(unwrapComputation(composed.consequent, rc), rc);
    const lConseqFlat = flattenAntecedent(unwrapComputation(Store.child(longhand.hash, 1), rc), rc);
    assert.equal(cConseqFlat.linear.length, lConseqFlat.linear.length);
    assert.equal(getPredicateHead(cConseqFlat.linear[0]), getPredicateHead(lConseqFlat.linear[0]));
  });

  it('persistent hypotheses pass through', () => {
    // Producer: !foo * a -o { !_0 mid }
    const foo = Store.put('atom', ['foo']);
    const bangFoo = Store.put('bang', [GRADE_W, foo]);
    const a = Store.put('atom', ['a']);
    const mid = Store.put('atom', ['mid']);
    const bang0mid = Store.put('bang', [GRADE_0, mid]);
    const producer = makeRule('prod', tensor(bangFoo, a), bang0mid);

    // Consumer: !_0 mid -o { b }
    const b = Store.put('atom', ['b']);
    const consumer = makeRule('cons', Store.put('bang', [GRADE_0, mid]), b);

    const result = composePair(producer, consumer, 'mid', rc);
    assert.ok(result);

    const anteFlat = flattenAntecedent(result.antecedent, rc);
    assert.equal(anteFlat.persistent.length, 1, 'persistent hypothesis preserved');
    assert.equal(anteFlat.persistent[0], foo, 'persistent is foo');
    assert.equal(anteFlat.linear.length, 1, 'one linear (a)');
    assert.equal(anteFlat.grade0.length, 0, 'no grade-0');
  });

  it('alpha-renaming prevents metavar collision', () => {
    // Both rules use metavar 'X' — alpha-renaming in producer prevents capture.
    // Producer: p X -o { !_0 mid X }
    // Consumer: !_0 mid X * q X -o { r X }
    // Without alpha-rename: X in producer and X in consumer are the SAME hash,
    // so unify(mid(X), mid(X)) would always succeed but q X wouldn't get
    // the producer's X value.

    const X = Store.put('metavar', ['X']);
    const pX = Store.put('p', [X]);
    const midX = Store.put('mid', [X]);
    const producer = makeRule('prod', pX, Store.put('bang', [GRADE_0, midX]));

    const qX = Store.put('q', [X]);
    const rX = Store.put('r', [X]);
    const consumer = makeRule('cons',
      tensor(Store.put('bang', [GRADE_0, midX]), qX),
      rX
    );

    const result = composePair(producer, consumer, 'mid', rc);
    assert.ok(result, 'composition should succeed');

    // The composed rule should have two linear ante patterns (p and q)
    const anteFlat = flattenAntecedent(result.antecedent, rc);
    assert.equal(anteFlat.linear.length, 2);

    // They should reference DIFFERENT metavars (one fresh, one original)
    const pred0 = getPredicateHead(anteFlat.linear[0]);
    const pred1 = getPredicateHead(anteFlat.linear[1]);
    const preds = new Set([pred0, pred1]);
    assert.ok(preds.has('p'), 'should have p');
    assert.ok(preds.has('q'), 'should have q');
  });

  it('unification failure returns null', () => {
    // Producer: a -o { !_0 mid 1 }   (ground: mid(1))
    // Consumer: !_0 mid 2 -o { b }   (ground: mid(2))
    // These can't unify (1 ≠ 2).

    const one = Store.put('atom', ['one_val']);
    const two = Store.put('atom', ['two_val']);
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);
    const mid1 = Store.put('mid', [one]);
    const mid2 = Store.put('mid', [two]);
    const producer = makeRule('prod', a, Store.put('bang', [GRADE_0, mid1]));
    const consumer = makeRule('cons', Store.put('bang', [GRADE_0, mid2]), b);

    const result = composePair(producer, consumer, 'mid', rc);
    assert.equal(result, null, 'unification failure should return null');
  });

  it('composition with existentials in consumer consequent', () => {
    // Producer: a X -o { !_0 mid X }
    // Consumer: !_0 mid Y -o { exists(b(Y)) }
    // Compose preserves the exists node; de Bruijn opening happens
    // in compileRule (second compile pass), not composePair.

    const X = Store.put('metavar', ['X']);
    const aX = Store.put('a', [X]);
    const midX = Store.put('mid', [X]);
    const producer = makeRule('prod', aX, Store.put('bang', [GRADE_0, midX]));

    const Y = Store.put('metavar', ['Y']);
    const midY = Store.put('mid', [Y]);
    const bY = Store.put('b', [Y]);
    const existsNode = Store.put('exists', [bY]);

    const consumer = makeRule('cons', Store.put('bang', [GRADE_0, midY]), existsNode);

    const result = composePair(producer, consumer, 'mid', rc);
    assert.ok(result, 'should compose with exists in consequent');

    const conseqFlat = flattenAntecedent(unwrapComputation(result.consequent, rc), rc);
    assert.equal(conseqFlat.grade0.length, 0, 'no grade-0 residual');
    assert.equal(conseqFlat.linear.length, 1, 'one opaque node');
    assert.equal(Store.tag(conseqFlat.linear[0]), 'exists', 'exists preserved');
  });

  it('persistent facts in producer consequent are preserved', () => {
    // Producer: a -o { !_0 mid * !bar }
    // Consumer: !_0 mid -o { c }
    // Composed: a -o { c * !bar }

    const a = Store.put('atom', ['a']);
    const mid = Store.put('atom', ['mid']);
    const bar = Store.put('atom', ['bar']);
    const bang0mid = Store.put('bang', [GRADE_0, mid]);
    const bangBar = Store.put('bang', [GRADE_W, bar]);
    const c = Store.put('atom', ['c']);

    const producer = makeRule('prod', a, tensor(bang0mid, bangBar));
    const consumer = makeRule('cons', Store.put('bang', [GRADE_0, mid]), c);

    const result = composePair(producer, consumer, 'mid', rc);
    assert.ok(result);

    const conseqFlat = flattenAntecedent(unwrapComputation(result.consequent, rc), rc);
    assert.equal(conseqFlat.persistent.length, 1, 'persistent bar preserved in conseq');
    assert.equal(conseqFlat.persistent[0], bar);
    assert.equal(conseqFlat.linear.length, 1, 'one linear (c)');
    assert.equal(conseqFlat.grade0.length, 0, 'no grade-0');
  });
});

// ─── L3: composeGrade0 ─────────────────────────────────────────────────────

describe('compose L3: composeGrade0', () => {
  beforeEach(() => Store.clear());

  it('composes single producer + single consumer', () => {
    const X = Store.put('metavar', ['X']);
    const aX = Store.put('a', [X]);
    const midX = Store.put('mid', [X]);
    const bang0mid = Store.put('bang', [GRADE_0, midX]);
    const producer = makeRule('prod', aX, bang0mid);

    const Y = Store.put('metavar', ['Y']);
    const midY = Store.put('mid', [Y]);
    const bY = Store.put('b', [Y]);
    const consumer = makeRule('cons', Store.put('bang', [GRADE_0, midY]), bY);

    const result = composeGrade0([producer, consumer], ILL_CONNECTIVES);
    assert.equal(result.diagnostics.errors.length, 0, 'no errors');
    assert.equal(result.composedRules.length, 1, 'one composed rule');
    assert.equal(result.diagnostics.pairsAttempted, 1);
    assert.equal(result.diagnostics.pairsSucceeded, 1);
    assert.equal(result.diagnostics.pairsSkipped, 0);
  });

  it('N producers × M consumers → N×M composed rules', () => {
    // Two producers for 'mid', one consumer → 2 composed rules
    const X = Store.put('metavar', ['X']);
    const a1 = Store.put('a1', [X]);
    const a2 = Store.put('a2', [X]);
    const midX = Store.put('mid', [X]);
    const bang0mid = Store.put('bang', [GRADE_0, midX]);

    const prod1 = makeRule('prod1', a1, bang0mid);
    const prod2 = makeRule('prod2', a2, bang0mid);

    const Y = Store.put('metavar', ['Y']);
    const midY = Store.put('mid', [Y]);
    const bY = Store.put('b', [Y]);
    const consumer = makeRule('cons', Store.put('bang', [GRADE_0, midY]), bY);

    const result = composeGrade0([prod1, prod2, consumer], ILL_CONNECTIVES);
    assert.equal(result.diagnostics.errors.length, 0);
    assert.equal(result.composedRules.length, 2, '2 composed rules (2×1)');
    assert.equal(result.diagnostics.pairsAttempted, 2);
    assert.equal(result.diagnostics.pairsSucceeded, 2);
  });

  it('error on producer-only grade-0 predicate', () => {
    const a = Store.put('atom', ['a']);
    const mid = Store.put('mid', [Store.put('metavar', ['X'])]);
    const producer = makeRule('prod', a, Store.put('bang', [GRADE_0, mid]));

    const result = composeGrade0([producer], ILL_CONNECTIVES);
    assert.equal(result.diagnostics.errors.length, 1);
    assert.ok(result.diagnostics.errors[0].includes('never consumed'));
    assert.equal(result.composedRules.length, 0);
  });

  it('error on consumer-only grade-0 predicate', () => {
    const mid = Store.put('mid', [Store.put('metavar', ['X'])]);
    const b = Store.put('atom', ['b']);
    const consumer = makeRule('cons', Store.put('bang', [GRADE_0, mid]), b);

    const result = composeGrade0([consumer], ILL_CONNECTIVES);
    assert.equal(result.diagnostics.errors.length, 1);
    assert.ok(result.diagnostics.errors[0].includes('never produced'));
    assert.equal(result.composedRules.length, 0);
  });

  it('error on bridge rules (v1 single-stage)', () => {
    const OP = Store.put('metavar', ['OP']);
    const rawOP = Store.put('raw', [OP]);
    const stepOP = Store.put('step', [OP]);

    // Source: x -o { !_0 raw X }
    const x = Store.put('atom', ['x']);
    const source = makeRule('source', x, Store.put('bang', [GRADE_0, rawOP]));

    // Bridge: !_0 raw Y -o { !_0 step Y }
    const Y = Store.put('metavar', ['Y']);
    const rawY = Store.put('raw', [Y]);
    const stepY = Store.put('step', [Y]);
    const bridge = makeRule('bridge',
      Store.put('bang', [GRADE_0, rawY]),
      Store.put('bang', [GRADE_0, stepY])
    );

    // Sink: !_0 step Z -o { result Z }
    const Z = Store.put('metavar', ['Z']);
    const stepZ = Store.put('step', [Z]);
    const resultZ = Store.put('result', [Z]);
    const sink = makeRule('sink', Store.put('bang', [GRADE_0, stepZ]), resultZ);

    const result = composeGrade0([source, bridge, sink], ILL_CONNECTIVES);
    assert.ok(result.diagnostics.errors.length > 0, 'should have bridge errors');
    assert.ok(result.diagnostics.errors.some(e => e.includes('bridge')));
    assert.equal(result.composedRules.length, 0);
  });

  it('error on multi-predicate producer (grade-0 residuals)', () => {
    // Producer outputs !_0 mid * !_0 other — two different grade-0 predicates.
    // Single-pass can't compose both; composed rules have residuals → error.
    const X = Store.put('metavar', ['X']);
    const aX = Store.put('a', [X]);
    const midX = Store.put('mid', [X]);
    const otherX = Store.put('other', [X]);
    const bang0mid = Store.put('bang', [GRADE_0, midX]);
    const bang0other = Store.put('bang', [GRADE_0, otherX]);
    const producer = makeRule('prod', aX, tensor(bang0mid, bang0other));

    const Y = Store.put('metavar', ['Y']);
    const midY = Store.put('mid', [Y]);
    const bY = Store.put('b', [Y]);
    const midConsumer = makeRule('mid_cons', Store.put('bang', [GRADE_0, midY]), bY);

    const Z = Store.put('metavar', ['Z']);
    const otherZ = Store.put('other', [Z]);
    const cZ = Store.put('c', [Z]);
    const otherConsumer = makeRule('other_cons', Store.put('bang', [GRADE_0, otherZ]), cZ);

    const result = composeGrade0([producer, midConsumer, otherConsumer], ILL_CONNECTIVES);
    assert.ok(result.diagnostics.errors.length > 0, 'should have residual errors');
    assert.ok(result.diagnostics.errors.some(e => e.includes('grade-0 content')));
    assert.equal(result.composedRules.length, 0, 'defective rules filtered out');
  });

  it('composed rules have hasGrade0: false', () => {
    const X = Store.put('metavar', ['X']);
    const aX = Store.put('a', [X]);
    const midX = Store.put('mid', [X]);
    const producer = makeRule('prod', aX, Store.put('bang', [GRADE_0, midX]));

    const Y = Store.put('metavar', ['Y']);
    const midY = Store.put('mid', [Y]);
    const bY = Store.put('b', [Y]);
    const consumer = makeRule('cons', Store.put('bang', [GRADE_0, midY]), bY);

    const result = composeGrade0([producer, consumer], ILL_CONNECTIVES);
    assert.equal(result.composedRules.length, 1);

    // Compile the composed raw rule and check hasGrade0
    const compiled = compileRule(result.composedRules[0], COMPILE_OPTS);
    assert.equal(compiled.hasGrade0, false, 'composed rule should have hasGrade0: false');
  });

  it('unification failures counted in diagnostics', () => {
    // Producer: a -o { !_0 mid 1 }
    // Consumer1: !_0 mid 1 -o { b }  — matches
    // Consumer2: !_0 mid 2 -o { c }  — doesn't match

    const one = Store.put('atom', ['one_val']);
    const two = Store.put('atom', ['two_val']);
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);
    const c = Store.put('atom', ['c']);

    const mid1 = Store.put('mid', [one]);
    const mid2 = Store.put('mid', [two]);

    const producer = makeRule('prod', a, Store.put('bang', [GRADE_0, mid1]));
    const cons1 = makeRule('cons1', Store.put('bang', [GRADE_0, Store.put('mid', [one])]), b);
    const cons2 = makeRule('cons2', Store.put('bang', [GRADE_0, mid2]), c);

    const result = composeGrade0([producer, cons1, cons2], ILL_CONNECTIVES);
    assert.equal(result.diagnostics.errors.length, 0);
    assert.equal(result.diagnostics.pairsAttempted, 2);
    assert.equal(result.diagnostics.pairsSucceeded, 1);
    assert.equal(result.diagnostics.pairsSkipped, 1);
    assert.equal(result.composedRules.length, 1);
  });

  it('no-op when no grade-0 rules exist', () => {
    const a = Store.put('atom', ['a']);
    const b = Store.put('atom', ['b']);
    const normal = makeRule('normal', a, b);

    const result = composeGrade0([normal], ILL_CONNECTIVES);
    assert.equal(result.composedRules.length, 0);
    assert.equal(result.diagnostics.grade0Predicates.length, 0);
  });
});

// ─── Integration: composed rules pass runtime filter ────────────────────────

describe('compose integration', () => {
  it('composed rules pass runtime filter, originals filtered out', () => {
    Store.clear();
    const fs = require('fs');
    const os = require('os');
    const path = require('path');
    const mde = require('../../lib/engine/index');
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'compose-'));

    // Write a program with grade-0 composition.
    // Use unique type names to avoid tag registry pollution from unit tests.
    fs.writeFileSync(path.join(tmpDir, 'compose_test.ill'),
      'alpha_src : type.\n' +
      'alpha_mid : type.\n' +
      'alpha_dst : type.\n' +
      'prod: alpha_src -o { !_0 alpha_mid }.\n' +
      'cons: !_0 alpha_mid -o { alpha_dst }.\n' +
      '#symex alpha_src.\n'
    );

    const calc = mde.load(path.join(tmpDir, 'compose_test.ill'), { cache: false });

    // Grade-0 originals should be filtered from forwardRules (public API)
    const prodRule = calc.forwardRules.find(r => r.name === 'prod');
    const consRule = calc.forwardRules.find(r => r.name === 'cons');
    assert.ok(!prodRule, 'prod (grade-0) filtered from forwardRules');
    assert.ok(!consRule, 'cons (grade-0) filtered from forwardRules');

    // There should be a composed rule (not grade-0)
    const composedRule = calc.forwardRules.find(r => r.name === 'cons:prod');
    assert.ok(composedRule, 'composed rule cons:prod exists');
    assert.equal(composedRule.hasGrade0, false, 'composed rule passes filter');

    // Execution should produce 'b' from initial state 'a'
    // Use the calc's own queries — parsed during load with correct Store state.
    const queryHash = calc.queries.get('symex');
    assert.ok(queryHash, 'should have a symex query');
    const state = mde.decomposeQuery(queryHash);
    const result = calc.exec(state, { maxSteps: 5, trace: true });
    assert.ok(result.steps > 0, 'should execute');

    // Trace should contain the composed rule, not the originals
    if (result.trace) {
      for (const entry of result.trace) {
        const name = typeof entry === 'string' ? entry : entry.rule;
        assert.ok(!name || name !== 'prod', 'prod should not fire directly');
        assert.ok(!name || name !== 'cons', 'cons should not fire directly');
      }
    }

    // Cleanup
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  });

  it('conservative extension: composed system equals expanded system', () => {
    Store.clear();
    const fs = require('fs');
    const os = require('os');
    const path = require('path');
    const mde = require('../../lib/engine/index');
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'compose-ce-'));

    // Composed version (with grade-0 intermediate).
    // Use unique type names to avoid tag registry pollution from unit tests.
    fs.writeFileSync(path.join(tmpDir, 'composed.ill'),
      'ce_counter : bin -> type.\n' +
      'ce_mid : bin -> type.\n' +
      'ce_done : bin -> type.\n' +
      'step1: ce_counter X -o { !_0 ce_mid X }.\n' +
      'step2: !_0 ce_mid X -o { ce_done X }.\n' +
      '#symex ce_counter 1.\n'
    );

    // Expanded version (longhand, no grade-0)
    fs.writeFileSync(path.join(tmpDir, 'expanded.ill'),
      'ce_counter : bin -> type.\n' +
      'ce_done : bin -> type.\n' +
      'direct: ce_counter X -o { ce_done X }.\n' +
      '#symex ce_counter 1.\n'
    );

    const calcComposed = mde.load(path.join(tmpDir, 'composed.ill'), { cache: false });
    const calcExpanded = mde.load(path.join(tmpDir, 'expanded.ill'), { cache: false });

    // Use queries from the loaded calcs (parsed with correct Store state)
    const stateC = mde.decomposeQuery(calcComposed.queries.get('symex'));
    const stateE = mde.decomposeQuery(calcExpanded.queries.get('symex'));

    // Collect leaves from explore tree (branches have children with { rule, child } shape)
    function collectLeaves(node) {
      if (!node) return [];
      if (node.type === 'leaf' || node.type === 'cycle' ||
          node.type === 'bound' || node.type === 'memo') return [node];
      if (node.children) {
        return node.children.flatMap(c => collectLeaves(c.child || c));
      }
      return [node];
    }

    const resultC = calcComposed.explore(stateC, { maxDepth: 10 });
    const resultE = calcExpanded.explore(stateE, { maxDepth: 10 });

    const leavesC = collectLeaves(resultC);
    const leavesE = collectLeaves(resultE);

    // Both should reach the same number of leaf states
    assert.equal(leavesC.length, leavesE.length,
      `leaf count should match: composed=${leavesC.length} vs expanded=${leavesE.length}`);

    // Both should have at least one leaf
    assert.ok(leavesC.length > 0, 'composed should reach at least one leaf');

    // All composed leaves should be type 'leaf' (not stuck)
    for (const l of leavesC) {
      assert.equal(l.type, 'leaf', `composed leaf type should be 'leaf', got '${l.type}'`);
    }

    // Cleanup
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  });
});
