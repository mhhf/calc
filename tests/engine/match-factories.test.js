/**
 * Protocol factory unit tests (TODO_0209).
 *
 * Each factory is a pure function that maps a record of inputs to a record of
 * output fields with a stable shape. These tests pin down the shape contract
 * so regressions that widen/narrow the matchOpts hidden class are caught at
 * unit-test granularity (not via whole-engine integration).
 *
 * Properties tested:
 *   1. Shape stability — factory always returns the same keys, regardless of input.
 *   2. Default semantics — missing/falsy inputs produce the documented defaults.
 *   3. Freeze — buildMatchOpts's output is frozen (V8 shape pinned).
 *   4. Identity — EMPTY_MATCH_OPTS has full shape, matching a populated matchOpts.
 *   5. Single source of truth — exported FIELD constants match factory outputs.
 */

const { describe, it } = require('node:test');
const assert = require('node:assert');
const match = require('../../lib/engine/match');

const {
  buildGenericProtocol, buildLnlProtocol, buildOptProtocol,
  buildFfiProtocol, buildMatchOpts,
  GENERIC_FIELDS, LNL_FIELDS, OPT_FIELDS, FFI_FIELDS,
  EMPTY_MATCH_OPTS,
} = match;

/** Sorted keys — order-independent shape comparison. */
function shape(obj) {
  return Object.keys(obj).sort();
}

describe('protocol factory shape stability', () => {
  it('buildGenericProtocol has stable shape regardless of input', () => {
    const empty = shape(buildGenericProtocol());
    const partial = shape(buildGenericProtocol({ evidence: true }));
    const full = shape(buildGenericProtocol({
      optimizePreserved: true, evidence: true,
      canonicalize: x => x, onProveFail: () => {}, onProveSuccess: () => {},
      provePersistent: () => {},
    }));
    assert.deepStrictEqual(empty, partial);
    assert.deepStrictEqual(empty, full);
    assert.deepStrictEqual(empty, [...GENERIC_FIELDS].sort());
  });

  it('buildLnlProtocol has stable shape regardless of input', () => {
    const empty = shape(buildLnlProtocol());
    const full = shape(buildLnlProtocol({
      matchLoli: () => {}, resolveEx: () => {}, drainLolis: () => {},
      rc: { implication: 'loli' }, backchainUseFFI: true,
    }));
    assert.deepStrictEqual(empty, full);
    assert.deepStrictEqual(empty, [...LNL_FIELDS].sort());
  });

  it('buildOptProtocol has stable shape regardless of input', () => {
    const empty = shape(buildOptProtocol());
    const full = shape(buildOptProtocol({
      execPS: () => {}, execExStep: () => {},
      tryCCDispatch: () => {}, useCompiledSteps: true,
    }));
    assert.deepStrictEqual(empty, full);
    assert.deepStrictEqual(empty, [...OPT_FIELDS].sort());
  });

  it('buildFfiProtocol has stable shape regardless of input', () => {
    const empty = shape(buildFfiProtocol(null));
    const full = shape(buildFfiProtocol({
      parsedModes: {}, meta: {}, get: () => {}, isFFIGround: () => {},
    }));
    assert.deepStrictEqual(empty, full);
    assert.deepStrictEqual(empty, [...FFI_FIELDS].sort());
  });

});

describe('protocol factory default semantics', () => {
  it('buildGenericProtocol defaults callbacks to null, prover to baseline, flags to false', () => {
    const g = buildGenericProtocol();
    assert.strictEqual(g.canonicalize, null);
    assert.strictEqual(g.onProveFail, null);
    assert.strictEqual(g.onProveSuccess, null);
    // provePersistent defaults to the generic-layer baseline (state-only prover),
    // not null — so every matchOpts is semantically complete out of the box.
    assert.strictEqual(g.provePersistent, match.stateProvePersistent);
    assert.strictEqual(typeof g.provePersistent, 'function');
    // Flags default to false (two-valued; no undefined tri-state).
    assert.strictEqual(g.optimizePreserved, false);
    assert.strictEqual(g.evidence, false);
  });

  it('buildGenericProtocol passes provePersistent through', () => {
    const prove = () => 'p';
    const g = buildGenericProtocol({ provePersistent: prove });
    assert.strictEqual(g.provePersistent, prove);
  });

  it('buildLnlProtocol defaults callbacks to null, rc to null', () => {
    const l = buildLnlProtocol();
    assert.strictEqual(l.matchDynamicRule, null);
    assert.strictEqual(l.resolveEx, null);
    assert.strictEqual(l.drainLolis, null);
    assert.strictEqual(l.connectives, null);
    assert.strictEqual(l.dynamicRuleTag, null);
    // Factory default is false — the platonic empty record supplies no FFI
    // provider. The production pragmatic default (FFI-on unless opted out)
    // lives at index.js:_buildMatchOpts, not in this factory.
    assert.strictEqual(l.backchainUseFFI, false);
  });

  it('buildLnlProtocol accepts explicit backchainUseFFI=true (production mode)', () => {
    const l = buildLnlProtocol({ backchainUseFFI: true });
    assert.strictEqual(l.backchainUseFFI, true);
  });

  it('buildLnlProtocol maps rc.implication → dynamicRuleTag', () => {
    const l = buildLnlProtocol({ rc: { implication: 'loli' } });
    assert.strictEqual(l.dynamicRuleTag, 'loli');
    assert.deepStrictEqual(l.connectives, { implication: 'loli' });
  });

  it('buildOptProtocol defaults callbacks to null, flags to false', () => {
    const o = buildOptProtocol();
    assert.strictEqual(o.execPS, null);
    assert.strictEqual(o.execExStep, null);
    assert.strictEqual(o.tryCCDispatch, null);
    assert.strictEqual(o.useCompiledSteps, false);
  });

  it('buildFfiProtocol defaults all fields to null when ffiCtx is null', () => {
    const f = buildFfiProtocol(null);
    assert.strictEqual(f.ffiParsedModes, null);
    assert.strictEqual(f.ffiMeta, null);
    assert.strictEqual(f.ffiGet, null);
    assert.strictEqual(f.ffiIsGround, null);
  });

  it('buildFfiProtocol passes through ffiCtx fields', () => {
    const getFn = () => 42;
    const ctx = { parsedModes: { p: [] }, meta: { x: 1 }, get: getFn, isFFIGround: () => true };
    const f = buildFfiProtocol(ctx);
    assert.deepStrictEqual(f.ffiParsedModes, { p: [] });
    assert.deepStrictEqual(f.ffiMeta, { x: 1 });
    assert.strictEqual(f.ffiGet, getFn);
    assert.strictEqual(typeof f.ffiIsGround, 'function');
  });

  it('boolean fields preserve explicit false', () => {
    const g = buildGenericProtocol({ optimizePreserved: false, evidence: false });
    assert.strictEqual(g.optimizePreserved, false);
    assert.strictEqual(g.evidence, false);

    const l = buildLnlProtocol({ backchainUseFFI: false });
    assert.strictEqual(l.backchainUseFFI, false);

    const o = buildOptProtocol({ useCompiledSteps: false });
    assert.strictEqual(o.useCompiledSteps, false);
  });
});

describe('buildMatchOpts and EMPTY_MATCH_OPTS', () => {
  it('buildMatchOpts freezes its output', () => {
    const m = buildMatchOpts({ ...buildGenericProtocol() });
    assert.ok(Object.isFrozen(m), 'matchOpts must be frozen');
    // Strict-mode assignment must throw on frozen objects (function-scoped directive).
    function strictAssign() {
      'use strict';
      m.canonicalize = x => x;
    }
    assert.throws(strictAssign, /read only|assign.*read.only|Cannot/i);
  });

  it('EMPTY_MATCH_OPTS is frozen', () => {
    assert.ok(Object.isFrozen(EMPTY_MATCH_OPTS));
  });

  it('EMPTY_MATCH_OPTS has full shape (all factory fields present)', () => {
    const expected = [
      ...GENERIC_FIELDS, ...LNL_FIELDS, ...OPT_FIELDS, ...FFI_FIELDS,
    ].sort();
    assert.deepStrictEqual(shape(EMPTY_MATCH_OPTS), expected);
  });

  it('EMPTY_MATCH_OPTS matches shape of fully-populated matchOpts', () => {
    const populated = buildMatchOpts({
      ...buildGenericProtocol({
        optimizePreserved: true, evidence: true,
        canonicalize: x => x, onProveFail: () => {}, onProveSuccess: () => {},
        provePersistent: () => {},
      }),
      ...buildLnlProtocol({
        matchLoli: () => {}, resolveEx: () => {}, drainLolis: () => {},
        rc: { implication: 'loli' }, backchainUseFFI: true,
      }),
      ...buildOptProtocol({
        execPS: () => {}, execExStep: () => {},
        tryCCDispatch: () => {}, useCompiledSteps: true,
      }),
      ...buildFfiProtocol({ parsedModes: {}, meta: {}, get: () => {}, isFFIGround: () => {} }),
    });
    assert.deepStrictEqual(shape(EMPTY_MATCH_OPTS), shape(populated));
  });
});

describe('FIELD constants (single source of truth)', () => {
  it('all FIELD constants are disjoint (no field owned by two factories)', () => {
    const all = [GENERIC_FIELDS, LNL_FIELDS, OPT_FIELDS, FFI_FIELDS];
    const seen = new Map();
    for (let i = 0; i < all.length; i++) {
      for (const f of all[i]) {
        if (seen.has(f)) {
          assert.fail(`Field '${f}' is produced by factories #${seen.get(f)} and #${i}`);
        }
        seen.set(f, i);
      }
    }
  });

  it('FIELD constants are frozen', () => {
    assert.ok(Object.isFrozen(GENERIC_FIELDS));
    assert.ok(Object.isFrozen(LNL_FIELDS));
    assert.ok(Object.isFrozen(OPT_FIELDS));
    assert.ok(Object.isFrozen(FFI_FIELDS));
  });
});

describe('S7 — iteration order (V8 hidden-class stability)', () => {
  /**
   * The field iteration order on a matchOpts object is part of its hidden-class
   * identity. Changing the order (by reordering factories or fields within a
   * factory) will construct a different hidden class, risking polymorphic IC
   * transitions on hot call sites. Pin the order mechanically.
   *
   * Canonical order: generic → lnl → opt → ffi, each factory in declaration order.
   */
  const EXPECTED_ORDER = [
    // GENERIC_FIELDS (in buildGenericProtocol order)
    'optimizePreserved', 'evidence', 'canonicalize',
    'onProveFail', 'onProveSuccess', 'provePersistent',
    // LNL_FIELDS (in buildLnlProtocol order)
    'matchDynamicRule', 'resolveEx', 'drainLolis',
    'connectives', 'dynamicRuleTag', 'backchainUseFFI',
    // OPT_FIELDS (in buildOptProtocol order)
    'execPS', 'execExStep', 'tryCCDispatch', 'useCompiledSteps',
    // FFI_FIELDS (in buildFfiProtocol order)
    'ffiParsedModes', 'ffiMeta', 'ffiGet', 'ffiIsGround',
  ];

  it('buildMatchOpts preserves canonical field order (empty)', () => {
    const m = buildMatchOpts({
      ...buildGenericProtocol(),
      ...buildLnlProtocol(),
      ...buildOptProtocol(),
      ...buildFfiProtocol(null),
    });
    assert.deepStrictEqual(Object.keys(m), EXPECTED_ORDER);
  });

  it('buildMatchOpts preserves canonical field order (populated)', () => {
    const m = buildMatchOpts({
      ...buildGenericProtocol({
        optimizePreserved: true, evidence: true,
        canonicalize: x => x, onProveFail: () => {}, onProveSuccess: () => {},
        provePersistent: () => {},
      }),
      ...buildLnlProtocol({
        matchLoli: () => {}, resolveEx: () => {}, drainLolis: () => {},
        rc: { implication: 'loli' }, backchainUseFFI: true,
      }),
      ...buildOptProtocol({
        execPS: () => {}, execExStep: () => {},
        tryCCDispatch: () => {}, useCompiledSteps: true,
      }),
      ...buildFfiProtocol({ parsedModes: {}, meta: {}, get: () => {}, isFFIGround: () => {} }),
    });
    assert.deepStrictEqual(Object.keys(m), EXPECTED_ORDER);
  });

  it('EMPTY_MATCH_OPTS has canonical field order', () => {
    assert.deepStrictEqual(Object.keys(EMPTY_MATCH_OPTS), EXPECTED_ORDER);
  });

  it('expected order totals exactly 20 fields (20-field shape contract)', () => {
    assert.strictEqual(EXPECTED_ORDER.length, 20);
    assert.strictEqual(
      GENERIC_FIELDS.length + LNL_FIELDS.length + OPT_FIELDS.length + FFI_FIELDS.length,
      20
    );
  });
});

describe('U — usage coverage (every field has a consumer)', () => {
  /**
   * Every matchOpts field must be accessed by at least one file in lib/engine/.
   * A field without any consumer is dead weight: it widens the hidden class
   * and every call site pays allocation + IC cost for no semantic gain.
   *
   * Detection: grep for `matchOpts.<field>` and `opts.<field>` where `opts`
   * is the conventional local name for the matchOpts parameter. We accept
   * either pattern since cached field extractions at function entry
   * (`const { foo } = matchOpts`) are the canonical low-cost access pattern.
   */
  const fs = require('fs');
  const path = require('path');

  function walkJs(dir) {
    const out = [];
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const full = path.join(dir, entry.name);
      if (entry.isDirectory()) out.push(...walkJs(full));
      else if (entry.isFile() && entry.name.endsWith('.js')) out.push(full);
    }
    return out;
  }

  const ENGINE_DIR = path.resolve(__dirname, '..', '..', 'lib', 'engine');
  const engineFiles = walkJs(ENGINE_DIR);
  const corpus = engineFiles.map(f => fs.readFileSync(f, 'utf8')).join('\n');

  const ALL_FIELDS = [
    ...GENERIC_FIELDS, ...LNL_FIELDS, ...OPT_FIELDS, ...FFI_FIELDS,
  ];

  for (const field of ALL_FIELDS) {
    it(`${field} is consumed by at least one engine file`, () => {
      // Accept either `matchOpts.field` or destructured `{ field }` from matchOpts.
      // The destructuring pattern is conservative: any `{ ..., field, ... } = matchOpts`
      // or similar alias counts. To avoid brittleness we just check the field
      // name appears as a property access or as a bare identifier in the corpus.
      const dotAccess = new RegExp(`\\.${field}\\b`);
      const destructured = new RegExp(`\\{[^}]*\\b${field}\\b[^}]*\\}\\s*=\\s*(?:matchOpts|opts|mo|_mo)\\b`);
      const ok = dotAccess.test(corpus) || destructured.test(corpus);
      assert.ok(ok, `Field '${field}' has no consumer in lib/engine/ — candidate for removal`);
    });
  }
});
