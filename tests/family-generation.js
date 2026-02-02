/**
 * Tests for family-based ll.json generation
 *
 * Verifies that the generator correctly handles:
 * - .family file parsing
 * - @role annotations
 * - Infrastructure + logic merging
 */

const { describe, it } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const generator = require('../lib/celf/generator');

describe('Family Infrastructure', () => {

  describe('extractFamilyInfrastructure', () => {
    it('should extract role registry from family AST', async () => {
      const tsParser = require('../lib/celf/ts-parser');
      await tsParser.init();

      const familyPath = path.join(__dirname, '../calculus/lnl.family');
      const result = await tsParser.parseFile(familyPath);
      assert.ok(result.success, `Parse failed: ${result.error}`);

      const { roleRegistry, connectives, directives } = generator.extractFamilyInfrastructure(result.ast);

      // Check role registry
      assert.ok(roleRegistry.judgment, 'Should have judgment role');
      assert.strictEqual(roleRegistry.judgment.name, 'deriv');

      assert.ok(roleRegistry.sequent, 'Should have sequent role');
      assert.strictEqual(roleRegistry.sequent.name, 'seq');

      assert.ok(roleRegistry.context_concat, 'Should have context_concat role');
      // Minimal design: single comma for both modes
      assert.strictEqual(roleRegistry.context_concat.name, 'comma');

      assert.ok(roleRegistry.hypothesis, 'Should have hypothesis role');
      // Minimal design: hyp replaces struct/labeled
      assert.strictEqual(roleRegistry.hypothesis.name, 'hyp');

      assert.ok(roleRegistry.unit, 'Should have unit role');
      // Minimal design: single empty
      assert.strictEqual(roleRegistry.unit.name, 'empty');
    });

    it('should extract directives', async () => {
      const tsParser = require('../lib/celf/ts-parser');
      await tsParser.init();

      const familyPath = path.join(__dirname, '../calculus/lnl.family');
      const result = await tsParser.parseFile(familyPath);
      assert.ok(result.success);

      const { directives } = generator.extractFamilyInfrastructure(result.ast);

      assert.strictEqual(directives.family, 'lnl');
      assert.ok(directives.metavars.length > 0, 'Should have metavars');

      const formulaMetavar = directives.metavars.find(m => m.type === 'formula');
      assert.ok(formulaMetavar, 'Should have formula metavar');
      assert.strictEqual(formulaMetavar.prefix, 'F?');
    });

    it('should extract schema directives', async () => {
      const tsParser = require('../lib/celf/ts-parser');
      await tsParser.init();

      const familyPath = path.join(__dirname, '../calculus/lnl.family');
      const result = await tsParser.parseFile(familyPath);
      assert.ok(result.success);

      const { directives } = generator.extractFamilyInfrastructure(result.ast);

      assert.ok(directives.schema.bin_factorization, 'Should have bin_factorization schema');
      // Minimal design: formula and structure (single type for both modes)
      assert.ok(
        directives.schema.bin_factorization.includes('formula'),
        'bin_factorization should include formula'
      );
      assert.ok(
        directives.schema.bin_factorization.includes('structure'),
        'bin_factorization should include structure'
      );
    });
  });

  describe('Generation with family', () => {
    it('should generate ll.json using family + calc', async () => {
      const calcPath = path.join(__dirname, '../calculus/ill.calc');
      const rulesPath = path.join(__dirname, '../calculus/ill.rules');
      const familyPath = path.join(__dirname, '../calculus/lnl.family');

      const llJson = await generator.generate({
        calcPath,
        rulesPath,
        familyPath
      });

      // Verify structure includes family infrastructure
      assert.ok(llJson.calc_structure.Structure, 'Should have Structure from family');
      assert.ok(llJson.calc_structure.Term, 'Should have Term from family');
      assert.ok(llJson.calc_structure.Sequent, 'Should have Sequent from family');

      // Verify logic connectives are included
      assert.ok(llJson.calc_structure.Formula, 'Should have Formula from calc');
      // New minimal design: no separate Bin_Op, connectives directly in Formula
      assert.ok(llJson.calc_structure.Formula.Formula_Tensor, 'Should have Formula_Tensor');
    });

    it('should work with legacy API (backwards compatible)', async () => {
      const calcPath = path.join(__dirname, '../calculus/ill.calc');
      const rulesPath = path.join(__dirname, '../calculus/ill.rules');

      // Legacy API: generate(calcPath, rulesPath, options) - still auto-resolves @extends
      const llJson = await generator.generate(calcPath, rulesPath);

      assert.ok(llJson.calc_structure, 'Should generate calc_structure');
      assert.ok(llJson.rules, 'Should generate rules');
    });

    it('should auto-resolve family via @extends directive', async () => {
      const calcPath = path.join(__dirname, '../calculus/ill.calc');
      const rulesPath = path.join(__dirname, '../calculus/ill.rules');

      // No familyPath provided - should auto-resolve from @extends directive
      const llJson = await generator.generate({ calcPath, rulesPath });

      // Verify family infrastructure is present
      assert.ok(llJson.calc_structure.Structure, 'Should have Structure from auto-resolved family');
      assert.ok(llJson.calc_structure.Term, 'Should have Term from auto-resolved family');
      assert.ok(llJson.calc_structure.Sequent, 'Should have Sequent from auto-resolved family');

      // Verify calc connectives are present (new minimal design - directly in Formula)
      assert.ok(llJson.calc_structure.Formula.Formula_Tensor, 'Should have Formula_Tensor');
      assert.ok(llJson.calc_structure.Formula.Formula_Loli, 'Should have Formula_Loli');

      // calc_name should come from family's @family directive
      assert.strictEqual(llJson.calc_name, 'lnl');
    });
  });
});
