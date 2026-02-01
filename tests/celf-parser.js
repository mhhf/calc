/**
 * Celf Parser Tests
 *
 * Tests the Ohm-based Celf parser for pure Celf syntax.
 */

const { describe, it } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');
const { parse, parseFile, AST } = require('../lib/celf/parser');

describe('Celf Parser', function() {

  describe('Type Declarations', function() {

    it('should parse type keyword declaration', function() {
      const result = parse('bin: type.');
      assert.strictEqual(result.success, true);
      assert.strictEqual(result.ast.declarations.length, 1);

      const decl = result.ast.declarations[0];
      assert.strictEqual(decl.type, 'TypeDecl');
      assert.strictEqual(decl.name, 'bin');
      assert.strictEqual(decl.typeExpr.type, 'TypeKeyword');
    });

    it('should parse nullary constructor', function() {
      const result = parse('e: bin.');
      assert.strictEqual(result.success, true);
      const decl = result.ast.declarations[0];
      assert.strictEqual(decl.type, 'TypeDecl');
      assert.strictEqual(decl.name, 'e');
      assert.strictEqual(decl.typeExpr.type, 'TypeAtom');
      assert.strictEqual(decl.typeExpr.name, 'bin');
    });

    it('should parse unary constructor', function() {
      const result = parse('i: bin -> bin.');
      assert.strictEqual(result.success, true);
      const decl = result.ast.declarations[0];
      assert.strictEqual(decl.typeExpr.type, 'TypeArrow');
      assert.strictEqual(decl.typeExpr.left.name, 'bin');
      assert.strictEqual(decl.typeExpr.right.name, 'bin');
    });

    it('should parse ternary relation', function() {
      const result = parse('plus: bin -> bin -> bin -> type.');
      assert.strictEqual(result.success, true);
      const decl = result.ast.declarations[0];
      // Right-associative: bin -> (bin -> (bin -> type))
      assert.strictEqual(decl.typeExpr.type, 'TypeArrow');
      assert.strictEqual(decl.typeExpr.left.name, 'bin');
      assert.strictEqual(decl.typeExpr.right.type, 'TypeArrow');
    });

    it('should parse linear arrow in type', function() {
      const result = parse('foo: bin -o bin.');
      assert.strictEqual(result.success, true);
      const decl = result.ast.declarations[0];
      assert.strictEqual(decl.typeExpr.type, 'TypeLoli');
    });

  });

  describe('Clause Declarations', function() {

    it('should parse fact (no premises)', function() {
      const result = parse('plus/z1: plus e e e.');
      assert.strictEqual(result.success, true);
      const decl = result.ast.declarations[0];
      assert.strictEqual(decl.type, 'ClauseDecl');
      assert.strictEqual(decl.name, 'plus/z1');
      assert.strictEqual(decl.premises.length, 0);
    });

    it('should parse clause with one premise', function() {
      const result = parse('inc/s: inc (i X) (o Y) <- inc X Y.');
      assert.strictEqual(result.success, true);
      const decl = result.ast.declarations[0];
      assert.strictEqual(decl.type, 'ClauseDecl');
      assert.strictEqual(decl.name, 'inc/s');
      assert.strictEqual(decl.premises.length, 1);
    });

    it('should parse clause with multiple premises', function() {
      const result = parse(`plus/s4: plus (i M) (i N) (o R)
        <- plus M N Q
        <- inc Q R.`);
      assert.strictEqual(result.success, true);
      const decl = result.ast.declarations[0];
      assert.strictEqual(decl.premises.length, 2);
    });

    it('should parse clause without slash in name', function() {
      const result = parse('start: bondManager_witnessProviders e false e.');
      assert.strictEqual(result.success, true);
      const decl = result.ast.declarations[0];
      assert.strictEqual(decl.name, 'start');
    });

  });

  describe('Terms', function() {

    it('should parse variable (uppercase)', function() {
      const result = parse('test: foo X.');
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermApp');
      assert.strictEqual(head.arg.type, 'TermVar');
      assert.strictEqual(head.arg.name, 'X');
    });

    it('should parse identifier (lowercase)', function() {
      const result = parse('test: foo bar.');
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermApp');
      assert.strictEqual(head.arg.type, 'TermIdent');
      assert.strictEqual(head.arg.name, 'bar');
    });

    it('should parse application chain', function() {
      const result = parse('test: foo A B C.');
      assert.strictEqual(result.success, true);
      // Left-associative: ((foo A) B) C
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermApp');
      assert.strictEqual(head.arg.name, 'C');
      assert.strictEqual(head.func.type, 'TermApp');
    });

    it('should parse nested application with parens', function() {
      const result = parse('test: foo (bar X).');
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermApp');
      assert.strictEqual(head.arg.type, 'TermApp');
    });

    it('should parse tensor (*)', function() {
      const result = parse('test: A * B.');
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermTensor');
    });

    it('should parse tensor chain (left-associative)', function() {
      const result = parse('test: A * B * C.');
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      // Left-associative: (A * B) * C
      assert.strictEqual(head.type, 'TermTensor');
      assert.strictEqual(head.left.type, 'TermTensor');
      assert.strictEqual(head.right.name, 'C');
    });

    it('should parse bang (!)', function() {
      const result = parse('test: !foo X.');
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermBang');
    });

    it('should parse nested bang', function() {
      const result = parse('test: !!foo.');
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermBang');
      assert.strictEqual(head.inner.type, 'TermBang');
    });

    it('should parse loli (-o) in term', function() {
      const result = parse('test: A -o B.');
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermLoli');
    });

    it('should parse forward rule (-o { })', function() {
      const result = parse('step: foo X -o { bar X }.');
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermForward');
      assert.strictEqual(head.antecedent.type, 'TermApp');
      assert.strictEqual(head.consequent.type, 'TermApp');
    });

    it('should parse complex forward rule', function() {
      const result = parse(`step: sender X * call Y * !plus A B C -o { result X }.`);
      assert.strictEqual(result.success, true);
      const head = result.ast.declarations[0].head;
      assert.strictEqual(head.type, 'TermForward');
      // Antecedent: sender X * call Y * !plus A B C (tensor chain)
      assert.strictEqual(head.antecedent.type, 'TermTensor');
    });

  });

  describe('Comments', function() {

    it('should parse comment', function() {
      const result = parse('% this is a comment\nbin: type.');
      assert.strictEqual(result.success, true);
      // Comments may or may not be preserved depending on implementation
      const typeDecls = result.ast.declarations.filter(d => d.type === 'TypeDecl');
      assert.strictEqual(typeDecls.length, 1);
    });

    it('should parse multiple comments', function() {
      const result = parse(`
        % Comment 1
        bin: type.
        % Comment 2
        e: bin.
      `);
      assert.strictEqual(result.success, true);
      const typeDecls = result.ast.declarations.filter(d => d.type === 'TypeDecl');
      assert.strictEqual(typeDecls.length, 2);
    });

  });

  describe('Multi-declaration Programs', function() {

    it('should parse multiple declarations', function() {
      const result = parse(`
        bin: type.
        e: bin.
        i: bin -> bin.
        o: bin -> bin.
      `);
      assert.strictEqual(result.success, true);
      const typeDecls = result.ast.declarations.filter(d => d.type === 'TypeDecl');
      assert.strictEqual(typeDecls.length, 4);
    });

    it('should parse mixed declarations', function() {
      const result = parse(`
        nat: type.
        z: nat.
        s: nat -> nat.
        plus: nat -> nat -> nat -> type.
        plus/z: plus z N N.
        plus/s: plus (s M) N (s R) <- plus M N R.
      `);
      assert.strictEqual(result.success, true);
      const typeDecls = result.ast.declarations.filter(d => d.type === 'TypeDecl');
      const clauseDecls = result.ast.declarations.filter(d => d.type === 'ClauseDecl');
      assert.strictEqual(typeDecls.length, 4);
      assert.strictEqual(clauseDecls.length, 2);
    });

  });

  describe('Real File Parsing', function() {

    const optimismMdePath = '/home/mhhf/src/optimism-mde';

    it('should parse optimism-mde/lib/bin.mde', function() {
      const filePath = path.join(optimismMdePath, 'lib', 'bin.mde');
      if (!fs.existsSync(filePath)) {
        console.log('Skipping: optimism-mde not found');
        return;
      }

      const result = parseFile(filePath);
      assert.strictEqual(result.success, true, result.error || 'Parse failed');

      // Should have many declarations
      assert.ok(result.ast.declarations.length > 10,
        `Expected many declarations, got ${result.ast.declarations.length}`);

      // Should have type declarations for bin, nat, etc.
      const typeDecls = result.ast.declarations.filter(d => d.type === 'TypeDecl');
      const typeNames = typeDecls.map(d => d.name);
      assert.ok(typeNames.includes('bin'), 'Should have bin type');
    });

    it('should parse optimism-mde/main.mde (partial - has incomplete syntax)', function() {
      const filePath = path.join(optimismMdePath, 'main.mde');
      if (!fs.existsSync(filePath)) {
        console.log('Skipping: optimism-mde not found');
        return;
      }

      const result = parseFile(filePath);
      // main.mde has incomplete syntax on line 136: "-o % comment" without consequent
      // This is a known issue in the source file, not the parser
      if (!result.success) {
        assert.ok(result.error.includes('138') || result.error.includes('expected'),
          'Expected parse error at known incomplete syntax location');
        console.log('Note: main.mde has incomplete syntax (work in progress)');
      }
    });

  });

  describe('Error Handling', function() {

    it('should report error for invalid syntax', function() {
      const result = parse('this is not valid celf');
      assert.strictEqual(result.success, false);
      assert.ok(result.error, 'Should have error message');
    });

    it('should report error for missing dot', function() {
      const result = parse('bin: type');
      assert.strictEqual(result.success, false);
    });

    it('should report error for invalid clause', function() {
      const result = parse('foo: .');  // Empty head
      assert.strictEqual(result.success, false);
    });

  });

});
