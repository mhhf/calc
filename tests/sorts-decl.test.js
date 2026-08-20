/**
 * Declaration parse forms for rung-1 sorts (TODO_0011):
 *   A <: B.                 — subsort declaration
 *   f: (s <: q) SIG.        — bounded sort variable on a signature
 *   r: (x: C) BODY.         — classifier-quantified rule binder
 *
 * Structure-level tests: parseDecls only splits and records; sort SEMANTICS
 * (classifier existence, edge validity) live in the engine layer and are
 * tested in tests/engine/till-sorts.test.js.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { parseDecls } from '../lib/parser/declarations.js';
import Store from '../lib/kernel/store.js';

// Stub expression parser: records the exact text handed to it, so tests can
// assert what survived binder stripping without a full grammar.
const stub = (text) => Store.put('strlit', [text]);
const textOf = (h) => Store.child(h, 0);

describe('subsort declaration form (A <: B.)', () => {
  it('parses a single subsort declaration', () => {
    const decls = parseDecls('bin <: q.', stub);
    assert.equal(decls.length, 1);
    assert.deepEqual(decls[0], { type: 'subsort', sub: 'bin', sup: 'q' });
  });

  it('parses multiple subsort declarations with comments', () => {
    const decls = parseDecls(
      '% the numeric tower\nbin <: q.  % naturals embed\ndelay <: q.\n', stub);
    assert.deepEqual(decls.map(d => [d.sub, d.sup]),
      [['bin', 'q'], ['delay', 'q']]);
  });

  it('mixes with ordinary declarations', () => {
    const decls = parseDecls('q: type.\nbin <: q.\ne: bin.', stub);
    assert.deepEqual(decls.map(d => d.type),
      ['declaration', 'subsort', 'declaration']);
  });

  it('rejects a malformed subsort declaration', () => {
    assert.throws(() => parseDecls('bin <: .', stub), /subsort/i);
  });
});

describe('leading binder groups on declaration bodies', () => {
  it('extracts a bounded sort variable, keeping the signature intact', () => {
    const decls = parseDecls('sub: (s <: q) (a: s) -> (b: s) -> (r: s) -> type.', stub);
    assert.equal(decls.length, 1);
    const d = decls[0];
    assert.deepEqual(d.binders, [{ name: 's', rel: '<:', sort: 'q' }]);
    assert.equal(textOf(d.bodyHash), '(a: s) -> (b: s) -> (r: s) -> type');
  });

  it('extracts a classifier binder from a rule body', () => {
    const decls = parseDecls('spoil: (r: resource) wood * r -o { I }.', stub);
    const d = decls[0];
    assert.deepEqual(d.binders, [{ name: 'r', rel: ':', sort: 'resource' }]);
    assert.equal(textOf(d.bodyHash), 'wood * r -o { I }');
  });

  it('extracts multiple classifier binders', () => {
    const decls = parseDecls('tax: (r: resource) (b: building) r * b -o { I }.', stub);
    assert.deepEqual(decls[0].binders, [
      { name: 'r', rel: ':', sort: 'resource' },
      { name: 'b', rel: ':', sort: 'building' },
    ]);
    assert.equal(textOf(decls[0].bodyHash), 'r * b -o { I }');
  });

  it('does NOT treat a named-arg arrow signature as a binder', () => {
    const decls = parseDecls('mid: (n: bin) -> type.', stub);
    assert.equal(decls[0].binders, undefined);
    assert.equal(textOf(decls[0].bodyHash), '(n: bin) -> type');
  });

  it('does NOT strip a lone parenthesized group with nothing after it', () => {
    const decls = parseDecls('odd: (a: bin).', stub);
    assert.equal(decls[0].binders, undefined);
    assert.equal(textOf(decls[0].bodyHash), '(a: bin)');
  });

  it('leaves parenthesized formulas alone (no colon)', () => {
    const decls = parseDecls('r: (a * b) -o { c }.', stub);
    assert.equal(decls[0].binders, undefined);
    assert.equal(textOf(decls[0].bodyHash), '(a * b) -o { c }');
  });

  it('comments between binders are stripped first', () => {
    const decls = parseDecls('spoil: (r: resource) % over every resource\n  r -o { I }.', stub);
    assert.deepEqual(decls[0].binders, [{ name: 'r', rel: ':', sort: 'resource' }]);
    assert.equal(textOf(decls[0].bodyHash), 'r -o { I }');
  });
});
