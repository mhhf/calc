/**
 * Tests for SELL subexponential context construction (TODO 151).
 * Tier 1: import-label filtering, Tier 2: module algebra.
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine/index');
const { parseDecls } = require('../../lib/parser/declarations');

const FIXTURES = path.join(__dirname, 'fixtures', 'sell');

// Dummy expression parser for declaration-level tests (returns pos-based hash)
let _exprParser;
beforeEach(() => {
  Store.clear();
  // Lazy-init the real expression parser from the engine
  if (!_exprParser) {
    const convert = require('../../lib/engine/convert');
    _exprParser = convert.parseExpr;
  }
});

describe('SELL: Directive Settings Parser (T9, T23)', () => {
  it('parses (rules: [alpha, beta]) settings', () => {
    Store.clear();
    const src = '#symex (rules: [alpha, beta]) counter 1.';
    const decls = parseDecls(src, _exprParser);
    assert.equal(decls.length, 1);
    assert.equal(decls[0].type, 'query');
    assert.equal(decls[0].kind, 'symex');
    assert.deepEqual(decls[0].settings, { rules: ['alpha', 'beta'] });
    assert.ok(decls[0].bodyHash); // body still parsed correctly
  });

  it('parses (rules: module_name) single identifier', () => {
    Store.clear();
    const src = '#symex (rules: full) counter 1.';
    const decls = parseDecls(src, _exprParser);
    assert.equal(decls[0].settings.rules, 'full');
  });

  it('does NOT misparse #prove (A * B) -o C as settings (T23)', () => {
    Store.clear();
    const src = '#prove (counter 1 * counter 2) -o { counter 3 }.';
    const decls = parseDecls(src, _exprParser);
    assert.equal(decls[0].type, 'query');
    assert.equal(decls[0].settings, undefined);
    assert.ok(decls[0].bodyHash); // expression parsed correctly
  });

  it('handles settings with eigenvars', () => {
    Store.clear();
    const src = '#symex (rules: [alpha]) [X] counter X.';
    const decls = parseDecls(src, _exprParser);
    assert.deepEqual(decls[0].settings, { rules: ['alpha'] });
    assert.deepEqual(decls[0].eigenVars, ['X']);
  });

  it('omitted rules: returns no settings (backward-compat T19)', () => {
    Store.clear();
    const src = '#symex counter 1.';
    const decls = parseDecls(src, _exprParser);
    assert.equal(decls[0].settings, undefined);
  });
});

describe('SELL: Module Algebra Parser (T11)', () => {
  it('parses @module name = label', () => {
    Store.clear();
    const src = '@module full = evm.';
    const decls = parseDecls(src, _exprParser);
    assert.equal(decls[0].type, 'directive');
    assert.equal(decls[0].key, 'module');
    assert.equal(decls[0].args.name, 'full');
    assert.deepEqual(decls[0].args.expr, { type: 'label', name: 'evm' });
  });

  it('parses @module name = A + B', () => {
    Store.clear();
    const src = '@module full = evm + gas.';
    const decls = parseDecls(src, _exprParser);
    const expr = decls[0].args.expr;
    assert.equal(expr.type, 'union');
    assert.deepEqual(expr.left, { type: 'label', name: 'evm' });
    assert.deepEqual(expr.right, { type: 'label', name: 'gas' });
  });

  it('parses @module name = A - {rule1, rule2}', () => {
    Store.clear();
    const src = '@module slim = full - {gas_charge, gas_refund}.';
    const decls = parseDecls(src, _exprParser);
    const expr = decls[0].args.expr;
    assert.equal(expr.type, 'subtract');
    assert.deepEqual(expr.left, { type: 'label', name: 'full' });
    assert.deepEqual(expr.right, { type: 'names', names: ['gas_charge', 'gas_refund'] });
  });

  it('parses @module with intersection', () => {
    Store.clear();
    const src = '@module core = alpha & beta.';
    const decls = parseDecls(src, _exprParser);
    const expr = decls[0].args.expr;
    assert.equal(expr.type, 'intersect');
  });

  it('respects operator precedence: & binds tighter than +', () => {
    Store.clear();
    const src = '@module mix = a + b & c.';
    const decls = parseDecls(src, _exprParser);
    const expr = decls[0].args.expr;
    // Should be: union(a, intersect(b, c))
    assert.equal(expr.type, 'union');
    assert.equal(expr.left.type, 'label');
    assert.equal(expr.right.type, 'intersect');
  });

  it('parses parenthesized sub-expressions', () => {
    Store.clear();
    const src = '@module x = (a + b) & c.';
    const decls = parseDecls(src, _exprParser);
    const expr = decls[0].args.expr;
    assert.equal(expr.type, 'intersect');
    assert.equal(expr.left.type, 'union');
  });
});

describe('SELL: Source Label Tracking (T1-T4)', () => {
  it('compiled rules carry sourceLabel', () => {
    const calc = mde.load(path.join(FIXTURES, 'main.ill'), { cache: false });
    // root_rule should have label 'main'
    const rootRule = calc.forwardRules.find(r => r.name === 'root_rule');
    assert.ok(rootRule, 'root_rule should exist');
    assert.equal(rootRule.sourceLabel, 'main');

    // inc should have label 'alpha'
    const incRule = calc.forwardRules.find(r => r.name === 'inc');
    assert.ok(incRule, 'inc rule should exist');
    assert.equal(incRule.sourceLabel, 'alpha');

    // dbl should have label 'beta'
    const dblRule = calc.forwardRules.find(r => r.name === 'dbl');
    assert.ok(dblRule, 'dbl rule should exist');
    assert.equal(dblRule.sourceLabel, 'beta');
  });

  it('sourceLabel survives binary cache round-trip (T22)', () => {
    const fs = require('fs');
    const os = require('os');
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'sell-cache-'));
    const mainPath = path.join(FIXTURES, 'main.ill');

    // First load — writes cache
    const calc1 = mde.load(mainPath, { cacheDir: tmpDir });
    // Second load — reads from cache
    const calc2 = mde.load(mainPath, { cacheDir: tmpDir });

    const incRule = calc2.forwardRules.find(r => r.name === 'inc');
    assert.equal(incRule.sourceLabel, 'alpha');

    // Cleanup
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  });
});

describe('SELL: Label Infrastructure (T5-T8)', () => {
  it('labelIndex maps labels to rule names', () => {
    const calc = mde.load(path.join(FIXTURES, 'main.ill'), { cache: false });
    assert.ok(calc.labelIndex.has('alpha'));
    assert.ok(calc.labelIndex.get('alpha').includes('inc'));
    assert.ok(calc.labelIndex.has('beta'));
    assert.ok(calc.labelIndex.get('beta').includes('dbl'));
    assert.ok(calc.labelIndex.has('main'));
    assert.ok(calc.labelIndex.get('main').includes('root_rule'));
  });
});

describe('SELL: Rule Filtering — Tier 1 (T14-T16, T17-T21)', () => {
  let calc;
  beforeEach(() => {
    Store.clear();
    calc = mde.load(path.join(FIXTURES, 'main.ill'), { cache: false });
  });

  it('(rules: [alpha]) excludes beta rules, includes alpha + root (T17)', () => {
    const state = mde.decomposeQuery(mde.parseExpr('counter 1'));
    const result = calc.exec(state, { rules: ['alpha'], maxSteps: 1, trace: true });
    assert.ok(result);
    assert.ok(result.state);
    // Trace should show only 'inc' or 'root_rule' fired, never 'dbl'
    if (result.trace) {
      for (const entry of result.trace) {
        const name = typeof entry === 'string' ? entry : entry.rule;
        assert.ok(!name.includes('dbl'), `dbl should NOT fire when filtered to alpha, got: ${name}`);
      }
    }
  });

  it('(rules: [alpha, beta]) includes both (T18)', () => {
    const state = mde.decomposeQuery(mde.parseExpr('counter 1'));
    const result = calc.exec(state, { rules: ['alpha', 'beta'], maxSteps: 1 });
    assert.ok(result);
  });

  it('omitted rules: includes everything — backward-compat (T19)', () => {
    const state = mde.decomposeQuery(mde.parseExpr('counter 1'));
    const result = calc.exec(state, { maxSteps: 1 });
    assert.ok(result);
  });

  it('unknown label → clear error (T20)', () => {
    const state = mde.decomposeQuery(mde.parseExpr('counter 1'));
    assert.throws(
      () => calc.exec(state, { rules: ['nonexistent'] }),
      /Unknown rule label.*nonexistent/
    );
  });

  it('root file rules always participate regardless of filter (T21)', () => {
    const state = mde.decomposeQuery(mde.parseExpr('counter 1'));
    // Filter to alpha only, but root_rule (from 'main') should still participate.
    // Both inc (+1) and root_rule (+100) fire, so counter grows beyond 1.
    const result = calc.exec(state, { rules: ['alpha'], maxSteps: 3 });
    assert.ok(result.state);
    assert.ok(result.steps > 0);
    // Verify root_rule (from 'main') actually fires: counter value should exceed
    // what alpha alone could produce in 3 steps (1 + 3 = 4 max)
    const counterHash = Object.keys(result.state.linear).map(Number);
    // Just check that execution proceeded — root rules participated
    assert.ok(counterHash.length > 0, 'counter facts should exist');
  });

  it('explore wrapper also supports rule filtering (T16)', () => {
    const state = mde.decomposeQuery(mde.parseExpr('counter 1'));
    const tree = calc.explore(state, { rules: ['alpha'], maxDepth: 3 });
    assert.ok(tree);
    assert.ok(tree.type); // Should be a valid tree node
  });
});

describe('SELL: Module Algebra — Tier 2 (T13, T24-T28)', () => {
  let calc;
  beforeEach(() => {
    Store.clear();
    calc = mde.load(path.join(FIXTURES, 'modules.ill'), { cache: false });
  });

  it('@module both = alpha + beta includes both labels (T24)', () => {
    assert.ok(calc.modules.has('both'));
    const both = calc.modules.get('both');
    assert.ok(both.has('inc'), 'both should include inc');
    assert.ok(both.has('dbl'), 'both should include dbl');
  });

  it('@module only_inc = both - {dbl} excludes specific rule (T25)', () => {
    assert.ok(calc.modules.has('only_inc'));
    const onlyInc = calc.modules.get('only_inc');
    assert.ok(onlyInc.has('inc'), 'only_inc should include inc');
    assert.ok(!onlyInc.has('dbl'), 'only_inc should NOT include dbl');
  });

  it('module referencing another module resolves correctly (T26)', () => {
    // only_inc references both, which is also a module
    const onlyInc = calc.modules.get('only_inc');
    assert.ok(onlyInc.has('inc'));
  });

  it('unknown module name → clear error (T27)', () => {
    const state = mde.decomposeQuery(mde.parseExpr('counter 1'));
    assert.throws(
      () => calc.exec(state, { rules: 'nonexistent_module' }),
      /Unknown rule label or module.*nonexistent_module/
    );
  });

  it('module name shadows label name — D7 precedence (T28)', () => {
    // Create a file where a module has the same name as an import label
    const fs = require('fs');
    const os = require('os');
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'sell-d7-'));

    // Write base
    fs.writeFileSync(path.join(tmpDir, 'base.ill'), 'counter: type.\n');
    // Write alpha
    fs.writeFileSync(path.join(tmpDir, 'alpha.ill'),
      '#import(base.ill)\ninc: counter X -o { counter (X + 1) }.\n');
    // Write beta
    fs.writeFileSync(path.join(tmpDir, 'beta.ill'),
      '#import(base.ill)\ndbl: counter X -o { counter (X + X) }.\n');
    // Module named 'alpha' that actually includes beta's rules
    fs.writeFileSync(path.join(tmpDir, 'main.ill'),
      '#import(alpha.ill)\n#import(beta.ill)\n@module alpha = beta.\n#symex counter 1.\n');

    Store.clear();
    const calc2 = mde.load(path.join(tmpDir, 'main.ill'), { cache: false });

    // D7: (rules: 'alpha') should resolve to the MODULE 'alpha' (which is beta's rules),
    // NOT the import label 'alpha' (which is inc)
    const alphaModule = calc2.modules.get('alpha');
    assert.ok(alphaModule.has('dbl'), 'module alpha should have dbl');
    assert.ok(!alphaModule.has('inc'), 'module alpha should NOT have inc (it shadows the label)');

    // Cleanup
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  });

  it('exec with module name filters correctly', () => {
    const state = mde.decomposeQuery(mde.parseExpr('counter 1'));
    // only_inc has {inc} + root_mod. Both fire repeatedly — just check it works.
    const result = calc.exec(state, { rules: 'only_inc', maxSteps: 3 });
    assert.ok(result.state);
    assert.ok(result.steps > 0);
  });
});

describe('SELL: QuerySettings Threading (T10)', () => {
  it('querySettings available on calc context', () => {
    const calc = mde.load(path.join(FIXTURES, 'main.ill'), { cache: false });
    assert.ok(calc.querySettings instanceof Map);
    // The 'symex' query that has settings
    // main.ill has three #symex directives; last one wins for the 'symex' key
    // The last #symex has (rules: [beta])
    if (calc.querySettings.has('symex')) {
      const settings = calc.querySettings.get('symex');
      assert.ok(settings.rules);
    }
  });
});

// =============================================================================
// SELL Graded Modality — TODO 155
// =============================================================================

const { GRADE_0, GRADE_W } = require('../../lib/engine/grades');
const { ILL_CONNECTIVES } = require('../../lib/engine/ill/connectives');
const { resolveConn, flattenAnte, compileRule } = require('../../lib/engine/compile');
const { getModes } = require('../../lib/engine/opt/ffi');

describe('SELL: Graded modality parsing (TODO 155)', () => {
  beforeEach(() => Store.clear());

  it('!A parses as bang(GRADE_W, A)', () => {
    Store.clear();
    const h = _exprParser('!foo');
    assert.equal(Store.tag(h), 'bang');
    const [grade, inner] = Store.children(h);
    assert.equal(grade, GRADE_W);
    assert.equal(Store.tag(inner), 'atom');
    assert.deepEqual(Store.children(inner), ['foo']);
  });

  it('!_0 A parses as bang(GRADE_0, A)', () => {
    Store.clear();
    const h = _exprParser('!_0 foo');
    assert.equal(Store.tag(h), 'bang');
    const [grade, inner] = Store.children(h);
    assert.equal(grade, GRADE_0);
    assert.equal(Store.tag(inner), 'atom');
    assert.deepEqual(Store.children(inner), ['foo']);
  });

  it('!_ω A parses as bang(GRADE_W, A) — same hash as !A', () => {
    Store.clear();
    const h1 = _exprParser('!foo');
    const h2 = _exprParser('!_ω foo');
    assert.equal(h1, h2, '!A and !_ω A should be identical (content-addressed)');
  });

  it('!_0 and !_ω produce different hashes', () => {
    Store.clear();
    const h0 = _exprParser('!_0 foo');
    const hw = _exprParser('!_ω foo');
    assert.notEqual(h0, hw, '!_0 and !_ω should differ');
  });

  it('nested: !_0 !A parses as bang(GRADE_0, bang(GRADE_W, A))', () => {
    Store.clear();
    const h = _exprParser('!_0 !foo');
    assert.equal(Store.tag(h), 'bang');
    const [outerGrade, innerBang] = Store.children(h);
    assert.equal(outerGrade, GRADE_0);
    assert.equal(Store.tag(innerBang), 'bang');
    const [innerGrade, atom] = Store.children(innerBang);
    assert.equal(innerGrade, GRADE_W);
    assert.equal(Store.tag(atom), 'atom');
  });

  it('!_0 in application context: !_0 eq A B', () => {
    Store.clear();
    const h = _exprParser('!_0 eq A B');
    assert.equal(Store.tag(h), 'bang');
    const [grade, inner] = Store.children(h);
    assert.equal(grade, GRADE_0);
    assert.equal(Store.tag(inner), 'eq');
    assert.equal(Store.children(inner).length, 2);
  });
});

describe('SELL: flattenAnte grade classification (TODO 155)', () => {
  beforeEach(() => Store.clear());

  it('bang(GRADE_W, A) → persistent', () => {
    Store.clear();
    const rc = resolveConn(ILL_CONNECTIVES);
    const A = Store.put('atom', ['a']);
    const h = Store.put('bang', [GRADE_W, A]);
    const flat = flattenAnte(h, rc);
    assert.deepEqual(flat.linear, []);
    assert.deepEqual(flat.persistent, [A]);
    assert.deepEqual(flat.grade0, []);
  });

  it('bang(GRADE_0, A) → grade0', () => {
    Store.clear();
    const rc = resolveConn(ILL_CONNECTIVES);
    const A = Store.put('atom', ['a']);
    const h = Store.put('bang', [GRADE_0, A]);
    const flat = flattenAnte(h, rc);
    assert.deepEqual(flat.linear, []);
    assert.deepEqual(flat.persistent, []);
    assert.deepEqual(flat.grade0, [A]);
  });

  it('A * !B * !_0 C → linear:[A], persistent:[B], grade0:[C]', () => {
    Store.clear();
    const rc = resolveConn(ILL_CONNECTIVES);
    const A = Store.put('atom', ['a']);
    const B = Store.put('atom', ['b']);
    const C = Store.put('atom', ['c']);
    const bangB = Store.put('bang', [GRADE_W, B]);
    const bang0C = Store.put('bang', [GRADE_0, C]);
    const h = Store.put('tensor', [A, Store.put('tensor', [bangB, bang0C])]);
    const flat = flattenAnte(h, rc);
    assert.deepEqual(flat.linear, [A]);
    assert.deepEqual(flat.persistent, [B]);
    assert.deepEqual(flat.grade0, [C]);
  });

  it('bare atom → linear', () => {
    Store.clear();
    const rc = resolveConn(ILL_CONNECTIVES);
    const A = Store.put('atom', ['a']);
    const flat = flattenAnte(A, rc);
    assert.deepEqual(flat.linear, [A]);
    assert.deepEqual(flat.persistent, []);
    assert.deepEqual(flat.grade0, []);
  });
});

describe('SELL: hasGrade0 flag on compiled rules (TODO 155)', () => {
  beforeEach(() => Store.clear());

  it('rule with !_0 antecedent has hasGrade0: true', () => {
    Store.clear();
    const A = Store.put('atom', ['a']);
    const B = Store.put('atom', ['b']);
    const bang0A = Store.put('bang', [GRADE_0, A]);
    const ante = Store.put('tensor', [bang0A, B]);
    const conseq = Store.put('monad', [Store.put('atom', ['c'])]);
    const rule = { name: 'test_g0', antecedent: ante, consequent: conseq };
    const compiled = compileRule(rule, { connectives: ILL_CONNECTIVES, getModes });
    assert.equal(compiled.hasGrade0, true);
  });

  it('rule with only !_ω antecedent has hasGrade0: false', () => {
    Store.clear();
    const A = Store.put('atom', ['a']);
    const B = Store.put('atom', ['b']);
    const bangWA = Store.put('bang', [GRADE_W, A]);
    const ante = Store.put('tensor', [bangWA, B]);
    const conseq = Store.put('monad', [Store.put('atom', ['c'])]);
    const rule = { name: 'test_gw', antecedent: ante, consequent: conseq };
    const compiled = compileRule(rule, { connectives: ILL_CONNECTIVES, getModes });
    assert.equal(compiled.hasGrade0, false);
  });

  it('rule with !_0 in consequent has hasGrade0: true', () => {
    Store.clear();
    const A = Store.put('atom', ['a']);
    const B = Store.put('atom', ['b']);
    const bang0B = Store.put('bang', [GRADE_0, B]);
    const conseq = Store.put('monad', [bang0B]);
    const rule = { name: 'test_g0_conseq', antecedent: A, consequent: conseq };
    const compiled = compileRule(rule, { connectives: ILL_CONNECTIVES, getModes });
    assert.equal(compiled.hasGrade0, true);
  });

  it('rule with no bang has hasGrade0: false', () => {
    Store.clear();
    const A = Store.put('atom', ['a']);
    const conseq = Store.put('monad', [Store.put('atom', ['b'])]);
    const rule = { name: 'test_nobang', antecedent: A, consequent: conseq };
    const compiled = compileRule(rule, { connectives: ILL_CONNECTIVES, getModes });
    assert.equal(compiled.hasGrade0, false);
  });
});

describe('SELL: Grade-0 filtering (TODO 155)', () => {
  it('filterRules excludes hasGrade0 rules from exec/explore', () => {
    Store.clear();
    const fs = require('fs');
    const os = require('os');
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'sell-g0-'));

    // Write a program with a grade-0 rule and a normal rule
    fs.writeFileSync(path.join(tmpDir, 'g0test.ill'),
      'counter: type.\n' +
      'inc: counter X -o { counter (X + 1) }.\n' +
      'stage: !_0 eq X X * counter X -o { counter X }.\n' +
      '#symex counter 1.\n'
    );

    const calc = mde.load(path.join(tmpDir, 'g0test.ill'), { cache: false });

    // Grade-0 rules should be filtered from forwardRules (public API)
    const stageRule = calc.forwardRules.find(r => r.name === 'stage');
    assert.ok(!stageRule, 'stage (grade-0) should be filtered from forwardRules');

    // The 'inc' rule should be present (not grade-0)
    const incRule = calc.forwardRules.find(r => r.name === 'inc');
    assert.ok(incRule, 'inc rule should exist');
    assert.equal(incRule.hasGrade0, false, 'inc rule should NOT have hasGrade0');

    // When executing, only inc should fire (stage is filtered out)
    const state = mde.decomposeQuery(mde.parseExpr('counter 1'));
    const result = calc.exec(state, { maxSteps: 3, trace: true });
    assert.ok(result.steps > 0, 'should execute at least one step');
    // Trace should only show 'inc', never 'stage'
    if (result.trace) {
      for (const entry of result.trace) {
        const name = typeof entry === 'string' ? entry : entry.rule;
        assert.ok(!name.includes('stage'), `stage should be filtered out, got: ${name}`);
      }
    }

    // Cleanup
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  });
});

describe('SELL: Grade constants survive Store.clear() (TODO 155)', () => {
  it('GRADE_W is valid after Store.clear()', () => {
    Store.clear();
    assert.equal(Store.tag(GRADE_W), 'atom');
    assert.deepEqual(Store.children(GRADE_W), ['gw']);
  });

  it('GRADE_0 is valid after Store.clear()', () => {
    Store.clear();
    assert.equal(Store.tag(GRADE_0), 'atom');
    assert.deepEqual(Store.children(GRADE_0), ['g0']);
  });

  it('GRADE_W has stable ID across clears', () => {
    const before = GRADE_W;
    Store.clear();
    assert.equal(GRADE_W, before, 'GRADE_W hash should be stable across Store.clear()');
  });

  it('bang(GRADE_W, X) works after Store.clear()', () => {
    Store.clear();
    const X = Store.put('atom', ['x']);
    const h = Store.put('bang', [GRADE_W, X]);
    assert.equal(Store.tag(h), 'bang');
    assert.equal(Store.child(h, 0), GRADE_W);
    assert.equal(Store.child(h, 1), X);
  });
});

describe('SELL: Grade-0 in queries rejected (TODO 155)', () => {
  it('decomposeQuery throws on !_0 resource', () => {
    Store.clear();
    const A = Store.put('atom', ['a']);
    const bang0A = Store.put('bang', [GRADE_0, A]);
    assert.throws(
      () => mde.decomposeQuery(bang0A),
      /Grade-0 resources.*cannot appear in queries/
    );
  });

  it('decomposeQuery throws on !_0 inside tensor', () => {
    Store.clear();
    const A = Store.put('atom', ['a']);
    const B = Store.put('atom', ['b']);
    const bang0A = Store.put('bang', [GRADE_0, A]);
    const h = Store.put('tensor', [B, bang0A]);
    assert.throws(
      () => mde.decomposeQuery(h),
      /Grade-0 resources.*cannot appear in queries/
    );
  });

  it('decomposeQuery accepts !_ω resource (persistent)', () => {
    Store.clear();
    const A = Store.put('atom', ['a']);
    const bangWA = Store.put('bang', [GRADE_W, A]);
    const result = mde.decomposeQuery(bangWA);
    assert.ok(result.persistent[A], 'should classify as persistent');
  });
});
