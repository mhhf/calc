/**
 * Direct tests for meta-parser/loader.js
 *
 * Covers: @extends chain resolution, declaration extraction from Store hashes,
 * child-wins merge semantics.
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import fs from 'fs';
import Store from '../lib/kernel/store.js';
import { loadChain } from '../lib/meta-parser/loader.js';

describe('meta-parser/loader', () => {
  before(() => {
    Store.clear();
  });

  describe('loadChain — lnl.family', () => {
    const familyPath = path.join(import.meta.dirname, '..', 'family', 'lnl', 'lnl.family');

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
        path.join(import.meta.dirname, '..', 'family', 'lnl', 'lnl.family')
      );
      assert.ok(constructorCount >= Object.keys(parentResult.constructors).length,
        'child should have at least as many constructors as parent');
    });

    it('preserves parent metavars + adds child metavars', () => {
      const result = loadChain(calcPath);
      assert.ok(Array.isArray(result.directives.metavars));
      const parentResult = loadChain(
        path.join(import.meta.dirname, '..', 'family', 'lnl', 'lnl.family')
      );
      // Merged metavars should be >= parent's
      assert.ok(result.directives.metavars.length >= parentResult.directives.metavars.length);
    });

    it('child family directive overrides parent', () => {
      const result = loadChain(calcPath);
      assert.ok(result.directives.family);
    });
  });

  describe('resolveExtends probe tiers (TODO_0086)', () => {
    it('resolves @extends via the family/<name>/ tier from a non-calculus dir', () => {
      // A .calc two directory levels below the repo root with no same-dir
      // lnl.family and no sibling lnl/ calculus dir can ONLY resolve
      // @extends lnl through the third probe tier (dir/../../family/lnl/).
      const fixture = path.join(import.meta.dirname, 'fixtures', 'extends-family-tier.calc');
      fs.writeFileSync(fixture, '@extends lnl.\n@family famtier.\n');
      try {
        const result = loadChain(fixture);
        // Inheriting the lnl sequent constructor proves the family file loaded.
        assert.ok(result.constructors.seq, 'lnl seq constructor inherited');
        assert.equal(result.directives.family, 'famtier');
      } finally {
        fs.unlinkSync(fixture);
      }
    });

    it('throws loudly when all three probe tiers miss', () => {
      const fixture = path.join(import.meta.dirname, 'fixtures', 'extends-missing.calc');
      fs.writeFileSync(fixture, '@extends truly_nonexistent_xyz.\n@family broken.\n');
      try {
        assert.throws(() => loadChain(fixture), /no such family\/calculus/);
      } finally {
        fs.unlinkSync(fixture);
      }
    });
  });
});
