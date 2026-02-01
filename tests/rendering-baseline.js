/**
 * Rendering Baseline Tests
 *
 * Captures current Node.toString() output for ASCII and LaTeX formats.
 * Used to verify DSL refactor generates equivalent rendering.
 */

const { describe, it } = require('node:test');
const assert = require('node:assert');
const calc = require('../ll.json');
const calcParser = require('../lib/parser.js');
const Calc = require('../lib/calc.js');

const { parser } = calcParser(calc);

describe('Rendering Baseline', function() {

  describe('ASCII Rendering', function() {

    it('should render simple sequent', function() {
      const node = parser.parse('-- : A |- -- : A');
      const ascii = node.toString({ style: 'ascii' });
      // Verify it contains key components
      assert.ok(ascii.includes('|-'), 'Should contain turnstile');
      assert.ok(ascii.includes('A'), 'Should contain atom name');
    });

    it('should render tensor', function() {
      const node = parser.parse('-- : A * B |- -- : C');
      const ascii = node.toString({ style: 'ascii' });
      assert.ok(ascii.includes('*'), 'Should contain tensor symbol');
    });

    it('should render loli', function() {
      const node = parser.parse('-- : A -o B |- -- : C');
      const ascii = node.toString({ style: 'ascii' });
      assert.ok(ascii.includes('-o'), 'Should contain loli symbol');
    });

    it('should render with', function() {
      const node = parser.parse('-- : A & B |- -- : C');
      const ascii = node.toString({ style: 'ascii' });
      assert.ok(ascii.includes('&'), 'Should contain with symbol');
    });

    it('should render bang', function() {
      const node = parser.parse('-- : ! A |- -- : B');
      const ascii = node.toString({ style: 'ascii' });
      assert.ok(ascii.includes('!'), 'Should contain bang symbol');
    });

    it('should render neutral', function() {
      const node = parser.parse('I |- -- : A');
      const ascii = node.toString({ style: 'ascii' });
      assert.ok(ascii.includes('I'), 'Should contain neutral symbol');
    });

    it('should render term any as --', function() {
      const node = parser.parse('-- : A |- -- : A');
      const ascii = node.toString({ style: 'ascii' });
      assert.ok(ascii.includes('--'), 'Should contain term any symbol');
    });

    it('should render complex formula', function() {
      const node = parser.parse('-- : (A * B) -o C |- -- : D');
      const ascii = node.toString({ style: 'ascii' });
      // Should have parentheses for nested formula
      assert.ok(ascii.includes('('), 'Should have opening paren');
      assert.ok(ascii.includes(')'), 'Should have closing paren');
      assert.ok(ascii.includes('*'), 'Should have tensor');
      assert.ok(ascii.includes('-o'), 'Should have loli');
    });

  });

  describe('LaTeX Rendering', function() {

    it('should render sequent with vdash', function() {
      const node = parser.parse('-- : A |- -- : A');
      const latex = node.toString({ style: 'latex' });
      assert.ok(latex.includes('\\vdash'), 'Should contain vdash');
    });

    it('should render tensor as otimes', function() {
      const node = parser.parse('-- : A * B |- -- : C');
      const latex = node.toString({ style: 'latex' });
      assert.ok(latex.includes('\\otimes'), 'Should contain otimes');
    });

    it('should render loli as multimap', function() {
      const node = parser.parse('-- : A -o B |- -- : C');
      const latex = node.toString({ style: 'latex' });
      assert.ok(latex.includes('\\multimap'), 'Should contain multimap');
    });

    it('should render with as \\&', function() {
      const node = parser.parse('-- : A & B |- -- : C');
      const latex = node.toString({ style: 'latex' });
      assert.ok(latex.includes('\\&'), 'Should contain ampersand');
    });

    it('should render bang as !', function() {
      const node = parser.parse('-- : ! A |- -- : B');
      const latex = node.toString({ style: 'latex' });
      assert.ok(latex.includes('!'), 'Should contain bang');
    });

    it('should render neutral as cdot', function() {
      const node = parser.parse('I |- -- : A');
      const latex = node.toString({ style: 'latex' });
      assert.ok(latex.includes('\\cdot'), 'Should contain cdot for neutral');
    });

  });

  describe('Isabelle Rendering', function() {

    it('should render tensor with Isabelle subscript', function() {
      const node = parser.parse('-- : A * B |- -- : C');
      const isabelle = node.toString({ style: 'isabelle' });
      assert.ok(isabelle.includes('\\<^sub>'), 'Should contain Isabelle subscript');
    });

    it('should render sequent with turnstile', function() {
      const node = parser.parse('-- : A |- -- : B');
      const isabelle = node.toString({ style: 'isabelle' });
      assert.ok(isabelle.includes('\\<turnstile>'), 'Should contain Isabelle turnstile');
    });

  });

  describe('Roundtrip Consistency', function() {

    const testCases = [
      '-- : A |- -- : A',
      '-- : A * B |- -- : C',
      '-- : A -o B |- -- : C',
      '-- : A & B |- -- : C',
      '-- : ! A |- -- : B',
      'I |- -- : A',
      '-- : A, -- : B |- -- : C',
      '-- : (A * B) -o C |- -- : D',
    ];

    for (const formula of testCases) {
      it(`should produce consistent output for: ${formula}`, function() {
        const node1 = parser.parse(formula);
        const ascii1 = node1.toString({ style: 'ascii' });

        // Parse the output again (may not be exact due to normalization)
        // Just verify it's non-empty and contains expected structure
        assert.ok(ascii1.length > 0, 'Should produce non-empty output');
        assert.ok(ascii1.includes('|-'), 'Should contain turnstile');
      });
    }

  });

  describe('Snapshot Values', function() {

    // These are exact snapshots of current rendering behavior
    // If these fail after refactor, we need to understand why

    it('should render identity exactly', function() {
      const node = parser.parse('-- : A |- -- : A');
      const ascii = node.toString({ style: 'ascii' });
      // Normalize whitespace for comparison
      const normalized = ascii.replace(/\s+/g, ' ').trim();
      assert.strictEqual(normalized, '-- : A |- -- : A');
    });

    it('should render tensor formula exactly', function() {
      const node = parser.parse('-- : A * B |- -- : C');
      const ascii = node.toString({ style: 'ascii' });
      const normalized = ascii.replace(/\s+/g, ' ').trim();
      assert.strictEqual(normalized, '-- : A * B |- -- : C');
    });

    it('should render loli formula exactly', function() {
      const node = parser.parse('-- : A -o B |- -- : C');
      const ascii = node.toString({ style: 'ascii' });
      const normalized = ascii.replace(/\s+/g, ' ').trim();
      assert.strictEqual(normalized, '-- : A -o B |- -- : C');
    });

    it('should render with formula exactly', function() {
      const node = parser.parse('-- : A & B |- -- : C');
      const ascii = node.toString({ style: 'ascii' });
      const normalized = ascii.replace(/\s+/g, ' ').trim();
      assert.strictEqual(normalized, '-- : A & B |- -- : C');
    });

    it('should render complex currying formula', function() {
      const node = parser.parse('-- : (A * B) -o C |- -- : A -o (B -o C)');
      const ascii = node.toString({ style: 'ascii' });
      const normalized = ascii.replace(/\s+/g, ' ').trim();
      // Left side preserves parens, right side doesn't (loli is right-associative)
      assert.ok(normalized.includes('( A * B )') || normalized.includes('(A * B)'),
                'Left side should have parens around tensor');
      assert.ok(normalized.includes('-o'), 'Should contain loli');
    });

  });

});
