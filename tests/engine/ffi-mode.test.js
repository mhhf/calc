/**
 * Direct tests for ill/ffi/mode.js
 *
 * Covers: parseMode, checkMode — mode classification for FFI.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');

// mode.js uses isGround from ill/ffi/convert — needs ILL atoms registered
let parseMode, checkMode;

describe('ffi/mode', () => {
  before(() => {
    Store.clear();
    // Register ILL atoms needed by isGround (binlit theory)
    require('../../lib/engine/ill/backchain-ill').initILL();
    ({ parseMode, checkMode } = require('../../lib/engine/ill/ffi/mode'));
  });

  describe('parseMode', () => {
    it('parses simple mode string', () => {
      assert.deepEqual(parseMode('+ + -'), ['+', '+', '-']);
    });

    it('parses single mode', () => {
      assert.deepEqual(parseMode('+'), ['+']);
    });

    it('parses all output modes', () => {
      assert.deepEqual(parseMode('- - -'), ['-', '-', '-']);
    });

    it('caches parsed results', () => {
      const a = parseMode('+ -');
      const b = parseMode('+ -');
      assert.equal(a, b); // same reference
    });
  });

  describe('checkMode', () => {
    it('returns true when all + args are ground', () => {
      const a = Store.put('atom', ['x']);
      const b = Store.put('atom', ['y']);
      assert.equal(checkMode([a, b], '+ +'), true);
    });

    it('returns false when + arg is a metavar', () => {
      const mv = Store.put('metavar', ['X']);
      const a = Store.put('atom', ['y']);
      assert.equal(checkMode([mv, a], '+ +'), false);
    });

    it('allows metavar in - position (output)', () => {
      const a = Store.put('atom', ['x']);
      const mv = Store.put('metavar', ['Y']);
      assert.equal(checkMode([a, mv], '+ -'), true);
    });

    it('returns false on arity mismatch', () => {
      const a = Store.put('atom', ['x']);
      assert.equal(checkMode([a], '+ +'), false);
    });

    it('returns true when all modes are output', () => {
      const mv1 = Store.put('metavar', ['X']);
      const mv2 = Store.put('metavar', ['Y']);
      assert.equal(checkMode([mv1, mv2], '- -'), true);
    });
  });
});
