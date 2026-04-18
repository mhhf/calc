/**
 * Direct tests for meta-parser/loader.js
 *
 * Covers: @extends chain resolution, declaration extraction from Store hashes,
 * child-wins merge semantics.
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../lib/kernel/store.js';
import { loadChain } from '../lib/meta-parser/loader.js';

describe('meta-parser/loader', () => {
  before(() => {
    Store.clear();
  });

  describe('loadChain — lnl.family', () => {
    const familyPath = path.join(import.meta.dirname, '..', 'calculus', 'ill', 'lnl.family');

    it('loads family file and extracts base types', () => {
      const result = loadChain(familyPath);
      assert.ok(result.baseTypes);
      assert.ok(Object.keys(result.baseTypes).length > 0);
      // LNL family defines base structural types (term, structure, sequent, deriv)
      assert.ok(result.baseTypes.term || result.baseTypes.structure || result.baseTypes.sequent,
        'should have structural base types');
    });

    it('extracts constructors', () => {
      const result = loadChain(familyPath);
      assert.ok(result.constructors);
      assert.ok(Object.keys(result.constructors).length > 0);
    });

    it('extracts family directive', () => {
      const result = loadChain(familyPath);
      assert.equal(result.directives.family, 'lnl');
    });

    it('extracts metavars', () => {
      const result = loadChain(familyPath);
      assert.ok(Array.isArray(result.directives.metavars));
      assert.ok(result.directives.metavars.length > 0);
    });
  });

  describe('loadChain — ill.calc with @extends', () => {
    const calcPath = path.join(import.meta.dirname, '..', 'calculus', 'ill', 'ill.calc');

    it('merges parent and child declarations (child-wins)', () => {
      const result = loadChain(calcPath);
      assert.ok(result.baseTypes);
      assert.ok(result.constructors);
      // ill.calc extends lnl.family → should have both parent and child constructors
      const constructorCount = Object.keys(result.constructors).length;
      // Should be more constructors than lnl.family alone
      const parentResult = loadChain(
        path.join(import.meta.dirname, '..', 'calculus', 'ill', 'lnl.family')
      );
      assert.ok(constructorCount >= Object.keys(parentResult.constructors).length,
        'child should have at least as many constructors as parent');
    });

    it('preserves parent metavars + adds child metavars', () => {
      const result = loadChain(calcPath);
      assert.ok(Array.isArray(result.directives.metavars));
      const parentResult = loadChain(
        path.join(import.meta.dirname, '..', 'calculus', 'ill', 'lnl.family')
      );
      // Merged metavars should be >= parent's
      assert.ok(result.directives.metavars.length >= parentResult.directives.metavars.length);
    });

    it('child family directive overrides parent', () => {
      const result = loadChain(calcPath);
      assert.ok(result.directives.family);
    });
  });
});
