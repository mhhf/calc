/**
 * Tests for v2 Calculus loader
 *
 * Verifies that parser/AST/renderer are GENERATED from spec files,
 * not hardcoded.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const calculus = require('../lib/calculus');
const { GRADE_W } = require('../lib/engine/grades');

describe('v2 Calculus (generated from spec)', () => {
  let ill;

  before(async () => {
    ill = await calculus.loadILL();
  });

  describe('loading', () => {
    it('should load calculus name from @family directive', () => {
      assert.strictEqual(ill.name, 'lnl');
    });

    it('should load constructors from spec', () => {
      assert.ok(ill.constructors.tensor, 'tensor should be loaded');
      assert.ok(ill.constructors.loli, 'loli should be loaded');
      assert.ok(ill.constructors.bang, 'bang should be loaded');
      assert.ok(ill.constructors.with, 'with should be loaded');
      assert.ok(ill.constructors.one, 'one should be loaded');
      assert.ok(ill.constructors.atom, 'atom should be loaded');
    });

    it('should preserve annotations', () => {
      const tensor = ill.constructors.tensor;
      assert.strictEqual(tensor.annotations.ascii, '_ * _');
      // @polarity removed - now inferred
      assert.strictEqual(tensor.annotations.category, 'multiplicative');
    });

    it('should inherit from lnl.family via @extends', () => {
      assert.ok(ill.constructors.seq, 'seq should be inherited from lnl.family');
      assert.ok(ill.constructors.hyp, 'hyp should be inherited');
      assert.ok(ill.constructors.comma, 'comma should be inherited');
      assert.ok(ill.constructors.empty, 'empty should be inherited');
    });
  });

  describe('AST constructors', () => {
    it('should generate tensor constructor', () => {
      const A = ill.AST.freevar('A');
      const B = ill.AST.freevar('B');
      const t = ill.AST.tensor(A, B);
      assert.strictEqual(ill.AST.tag(t), 'tensor');
      assert.strictEqual(ill.AST.children(t).length, 2);
    });

    it('should generate nullary constructors', () => {
      const one = ill.AST.one();
      assert.strictEqual(ill.AST.tag(one), 'one');
      assert.strictEqual(ill.AST.children(one).length, 0);
    });

    it('should generate bang constructor (arity 2: grade + formula)', () => {
      const A = ill.AST.freevar('A');
      const { GRADE_W } = require('../lib/engine/grades');
      const bangA = ill.AST.bang(GRADE_W, A);
      assert.strictEqual(ill.AST.tag(bangA), 'bang');
      assert.strictEqual(ill.AST.children(bangA).length, 2);
    });

    it('should generate sequent constructor from family', () => {
      const G = ill.AST.empty();
      const D = ill.AST.freevar('D');
      const C = ill.AST.freevar('C');
      const s = ill.AST.seq(G, D, C);
      assert.strictEqual(ill.AST.tag(s), 'seq');
      assert.strictEqual(ill.AST.children(s).length, 3);
    });
  });

  describe('parser (generated)', () => {
    it('should parse atoms', () => {
      const ast = ill.parse('p');
      assert.strictEqual(ill.AST.tag(ast), 'atom');
      assert.strictEqual(ill.AST.child(ast, 0), 'p');
    });

    it('should parse freevars', () => {
      const ast = ill.parse('A');
      assert.strictEqual(ill.AST.tag(ast), 'freevar');
      assert.strictEqual(ill.AST.child(ast, 0), 'A');
    });

    it('should parse tensor from @ascii "_ * _"', () => {
      const ast = ill.parse('A * B');
      assert.strictEqual(ill.AST.tag(ast), 'tensor');
    });

    it('should parse loli from @ascii "_ -o _"', () => {
      const ast = ill.parse('A -o B');
      assert.strictEqual(ill.AST.tag(ast), 'loli');
    });

    it('should parse with from @ascii "_ & _"', () => {
      const ast = ill.parse('A & B');
      assert.strictEqual(ill.AST.tag(ast), 'with');
    });

    it('should parse bang from @ascii "! _"', () => {
      const ast = ill.parse('!A');
      assert.strictEqual(ill.AST.tag(ast), 'bang');
    });

    it('should parse one from @ascii "I"', () => {
      const ast = ill.parse('I');
      assert.strictEqual(ill.AST.tag(ast), 'one');
    });

    it('should respect precedence from @prec', () => {
      // tensor (60) binds tighter than loli (50)
      // "A * B -o C" should be "(A * B) -o C"
      const ast = ill.parse('A * B -o C');
      assert.strictEqual(ill.AST.tag(ast), 'loli');
      assert.strictEqual(ill.AST.tag(ill.AST.child(ast, 0)), 'tensor');
    });

    it('should handle parentheses', () => {
      const ast = ill.parse('A * (B -o C)');
      assert.strictEqual(ill.AST.tag(ast), 'tensor');
      assert.strictEqual(ill.AST.tag(ill.AST.child(ast, 1)), 'loli');
    });

    it('should handle complex formulas', () => {
      const ast = ill.parse('!A * B -o C & D');
      // Precedence: ! (80) > * (60) > -o (50) > & (70)
      // Actually & is 70 > -o 50, so it's (!A * B) -o (C & D)
      assert.strictEqual(ill.AST.tag(ast), 'loli');
    });

    it('should give & higher precedence than +', () => {
      // with (70) binds tighter than oplus (65)
      // "A + B & C" should be "A + (B & C)"
      const ast = ill.parse('A + B & C');
      assert.strictEqual(ill.AST.tag(ast), 'oplus');
      assert.strictEqual(ill.AST.tag(ill.AST.child(ast, 1)), 'with');
    });
  });

  describe('renderer (generated)', () => {
    it('should render with @ascii template', () => {
      const ast = ill.AST.tensor(ill.AST.freevar('A'), ill.AST.freevar('B'));
      const str = ill.render(ast, 'ascii');
      assert.strictEqual(str, 'A * B');
    });

    it('should render with @latex template', () => {
      const ast = ill.AST.tensor(ill.AST.freevar('A'), ill.AST.freevar('B'));
      const str = ill.render(ast, 'latex');
      assert.strictEqual(str, 'A \\otimes B');
    });

    it('should render bang correctly', () => {
      const ast = ill.AST.bang(GRADE_W, ill.AST.freevar('A'));
      assert.strictEqual(ill.render(ast, 'ascii'), '! A');
    });

    it('should render nullary correctly', () => {
      const ast = ill.AST.one();
      assert.strictEqual(ill.render(ast, 'ascii'), 'I');
    });
  });

  describe('extended parser (binders, multi-char freevars, numbers)', () => {
    let extParse;

    before(() => {
      const { buildParserFromTables, computeParserTables } = require('../lib/calculus/builders');
      const tables = computeParserTables(ill.constructors);
      tables.binders = { exists: 'exists', forall: 'forall' };
      tables.multiCharFreevars = true;
      tables.numbers = true;
      extParse = buildParserFromTables(tables);
    });

    it('should parse exists X. body as binder with de Bruijn', () => {
      const Store = require('../lib/kernel/store');
      const ast = extParse('exists X. X');
      assert.strictEqual(Store.tag(ast), 'exists');
      const body = Store.child(ast, 0);
      assert.strictEqual(Store.tag(body), 'bound');
      assert.strictEqual(Store.child(body, 0), 0n); // de Bruijn index 0
    });

    it('should handle nested binders', () => {
      const Store = require('../lib/kernel/store');
      const ast = extParse('forall Y. exists X. X');
      assert.strictEqual(Store.tag(ast), 'forall');
      const inner = Store.child(ast, 0);
      assert.strictEqual(Store.tag(inner), 'exists');
      const body = Store.child(inner, 0);
      assert.strictEqual(Store.tag(body), 'bound');
      assert.strictEqual(Store.child(body, 0), 0n); // X is innermost
    });

    it('should reference outer binder at depth 1', () => {
      const Store = require('../lib/kernel/store');
      const ast = extParse('forall Y. exists X. Y');
      const inner = Store.child(ast, 0);
      const body = Store.child(inner, 0);
      assert.strictEqual(Store.tag(body), 'bound');
      assert.strictEqual(Store.child(body, 0), 1n); // Y is one level out
    });

    it('should parse multi-char uppercase as metavar', () => {
      const Store = require('../lib/kernel/store');
      const ast = extParse('Sender');
      assert.strictEqual(Store.tag(ast), 'metavar');
      assert.strictEqual(Store.child(ast, 0), 'Sender');
    });

    it('should parse number literals', () => {
      const Store = require('../lib/kernel/store');
      const ast = extParse('42');
      assert.strictEqual(Store.tag(ast), 'binlit');
      assert.strictEqual(Store.child(ast, 0), 42n);
    });

    it('should parse hex literals', () => {
      const Store = require('../lib/kernel/store');
      const ast = extParse('0x60');
      assert.strictEqual(Store.tag(ast), 'binlit');
      assert.strictEqual(Store.child(ast, 0), 96n);
    });

    it('binder body extends to full expression', () => {
      const Store = require('../lib/kernel/store');
      // exists X. X * X should be exists(tensor(X, X))
      const ast = extParse('exists X. X * X');
      assert.strictEqual(Store.tag(ast), 'exists');
      const body = Store.child(ast, 0);
      assert.strictEqual(Store.tag(body), 'tensor');
    });

    it('unbound uppercase stays metavar (not bound)', () => {
      const Store = require('../lib/kernel/store');
      const ast = extParse('exists X. Y');
      const body = Store.child(ast, 0);
      assert.strictEqual(Store.tag(body), 'metavar');
      assert.strictEqual(Store.child(body, 0), 'Y');
    });
  });

  describe('extended parser (application, arrows, forward rules, binary norm)', () => {
    let engineParse;
    const Store = require('../lib/kernel/store');

    before(() => {
      const { buildParserFromTables, computeParserTables } = require('../lib/calculus/builders');
      const tables = computeParserTables(ill.constructors);
      tables.binders = { exists: 'exists', forall: 'forall' };
      tables.multiCharFreevars = true;
      tables.numbers = true;
      tables.application = true;
      tables.arrows = true;
      tables.forwardRules = true;
      tables.binaryNormalization = true;
      engineParse = buildParserFromTables(tables);
    });

    it('should parse application f x y as flat predicate', () => {
      const ast = engineParse('inc X Y');
      assert.strictEqual(Store.tag(ast), 'inc');
      assert.strictEqual(Store.arity(ast), 2);
      assert.strictEqual(Store.tag(Store.child(ast, 0)), 'metavar');
      assert.strictEqual(Store.tag(Store.child(ast, 1)), 'metavar');
    });

    it('should parse nested application: stack (s SH) A', () => {
      const ast = engineParse('stack (s SH) A');
      assert.strictEqual(Store.tag(ast), 'stack');
      assert.strictEqual(Store.arity(ast), 2);
      assert.strictEqual(Store.tag(Store.child(ast, 0)), 's');
    });

    it('should parse arrow: bin -> bin', () => {
      const ast = engineParse('bin -> bin');
      assert.strictEqual(Store.tag(ast), 'arrow');
      assert.strictEqual(Store.tag(Store.child(ast, 0)), 'atom');
      assert.strictEqual(Store.tag(Store.child(ast, 1)), 'atom');
    });

    it('should parse chained arrows: bin -> bin -> type', () => {
      const ast = engineParse('bin -> bin -> type');
      assert.strictEqual(Store.tag(ast), 'arrow');
      const right = Store.child(ast, 1);
      assert.strictEqual(Store.tag(right), 'arrow');
    });

    it('should parse lollipop: A -o B', () => {
      const ast = engineParse('A -o B');
      assert.strictEqual(Store.tag(ast), 'loli');
    });

    it('should parse forward rule: A -o { B }', () => {
      const ast = engineParse('A -o { B }');
      assert.strictEqual(Store.tag(ast), 'loli');
      const conseq = Store.child(ast, 1);
      assert.strictEqual(Store.tag(conseq), 'monad');
    });

    it('should normalize binary: e → binlit(0)', () => {
      const ast = engineParse('e');
      assert.strictEqual(Store.tag(ast), 'binlit');
      assert.strictEqual(Store.child(ast, 0), 0n);
    });

    it('should normalize binary: i e → binlit(1)', () => {
      const ast = engineParse('i e');
      assert.strictEqual(Store.tag(ast), 'binlit');
      assert.strictEqual(Store.child(ast, 0), 1n);
    });

    it('should normalize binary: o (i e) → binlit(2)', () => {
      const ast = engineParse('o (i e)');
      assert.strictEqual(Store.tag(ast), 'binlit');
      assert.strictEqual(Store.child(ast, 0), 2n);
    });

    it('should parse type keyword', () => {
      const ast = engineParse('type');
      assert.strictEqual(Store.tag(ast), 'type');
      assert.strictEqual(Store.arity(ast), 0);
    });

    it('should parse application with bang: !inc X Y', () => {
      const ast = engineParse('!inc X Y');
      assert.strictEqual(Store.tag(ast), 'bang');
      const inner = Store.child(ast, 1);
      assert.strictEqual(Store.tag(inner), 'inc');
    });

    it('should parse tensor with applications: pc PC * code PC 0x01', () => {
      const ast = engineParse('pc PC * code PC 0x01');
      assert.strictEqual(Store.tag(ast), 'tensor');
      const left = Store.child(ast, 0);
      const right = Store.child(ast, 1);
      assert.strictEqual(Store.tag(left), 'pc');
      assert.strictEqual(Store.tag(right), 'code');
    });
  });

  describe('declaration parser', () => {
    const { parseDeclarations } = require('../lib/parser/declarations');
    const Store = require('../lib/kernel/store');
    const id = (x) => Store.put('atom', [x]);

    it('should parse simple declaration', () => {
      const decls = parseDeclarations('foo: bar.', id);
      assert.strictEqual(decls.length, 1);
      assert.strictEqual(decls[0].type, 'declaration');
      assert.strictEqual(decls[0].name, 'foo');
    });

    it('should parse declaration with premises', () => {
      const decls = parseDeclarations('r: head <- p1 <- p2.', id);
      assert.strictEqual(decls.length, 1);
      assert.strictEqual(decls[0].premises.length, 2);
    });

    it('should parse comments', () => {
      const decls = parseDeclarations('% comment\nfoo: bar.', id);
      assert.strictEqual(decls.length, 1);
      assert.strictEqual(decls[0].name, 'foo');
    });

    it('should parse query directive', () => {
      const decls = parseDeclarations('#symex body.', id);
      assert.strictEqual(decls.length, 1);
      assert.strictEqual(decls[0].type, 'query');
      assert.strictEqual(decls[0].kind, 'symex');
    });

    it('should parse standalone directive', () => {
      const decls = parseDeclarations('@family lnl.', id);
      assert.strictEqual(decls.length, 1);
      assert.strictEqual(decls[0].type, 'directive');
      assert.strictEqual(decls[0].key, 'family');
    });

    it('should parse declaration with slash name', () => {
      const decls = parseDeclarations('eq/z: head.', id);
      assert.strictEqual(decls[0].name, 'eq/z');
    });

    it('should parse multiple declarations', () => {
      const decls = parseDeclarations('a: x.\nb: y.\nc: z.', id);
      assert.strictEqual(decls.length, 3);
    });

    it('should parse declarations with annotations', () => {
      const decls = parseDeclarations(
        'tensor: body @ascii "_ * _" @prec 60 left.',
        id, { annotations: true }
      );
      assert.strictEqual(decls[0].annotations.length, 2);
      assert.strictEqual(decls[0].annotations[0].key, 'ascii');
      assert.strictEqual(decls[0].annotations[0].value.value, '_ * _');
      assert.strictEqual(decls[0].annotations[1].key, 'prec');
      assert.strictEqual(decls[0].annotations[1].value.precedence, 60);
      assert.strictEqual(decls[0].annotations[1].value.associativity, 'left');
    });

    it('should handle import directives', () => {
      const decls = parseDeclarations('#import(bin.ill)\nfoo: bar.', id);
      assert.strictEqual(decls.length, 2);
      assert.strictEqual(decls[0].type, 'import');
      assert.strictEqual(decls[0].path, 'bin.ill');
    });
  });

  describe('roundtrip', () => {
    it('should parse and render to same AST', () => {
      // Test that parse(render(ast)) === ast
      // With content-addressed ASTs, same structure = same hash
      const formulas = ['A', 'A * B', 'A -o B', '!A', 'I'];
      for (const formula of formulas) {
        const ast1 = ill.parse(formula);
        const rendered = ill.render(ast1, 'ascii');
        const ast2 = ill.parse(rendered);
        // Content-addressed: equal structure = equal hash
        assert.strictEqual(ast1, ast2,
          `Roundtrip failed for: ${formula} -> ${rendered}`);
      }
    });
  });
});
