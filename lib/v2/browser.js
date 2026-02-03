/**
 * v2 Browser-Compatible API
 *
 * This module provides the same API as lib/v2/index.js but works in browsers
 * by loading from a pre-bundled JSON file instead of reading .calc/.rules files.
 *
 * Usage in browser:
 *   import * as calcV2 from '@lib/v2/browser';
 *
 *   // Initialize (call once)
 *   await calcV2.init();
 *
 *   // Then use the same API
 *   const result = await calcV2.proveString('A, A -o B |- B');
 */

const prover = require('./prover');
const Seq = require('./kernel/sequent');
const AST = require('./kernel/ast');
const { copy, apply, occurs } = require('./kernel/substitute');
const { unify, match } = require('./kernel/unify');

// Cached calculus instance (hydrated from bundle)
let calculus = null;
let bundleData = null;

/**
 * Initialize from pre-bundled data
 * @param {Object} bundle - Pre-processed ILL bundle (from ill-v2.json)
 */
function initFromBundle(bundle) {
  if (!bundle?.constructors) {
    throw new Error('Invalid bundle: missing constructors');
  }
  bundleData = bundle;
  calculus = hydrateCalculus(bundle);
  return calculus;
}

/**
 * Hydrate a calculus from bundle data
 * Recreates the runtime functions (parse, render, AST constructors)
 */
function hydrateCalculus(bundle) {
  const { constructors, rules, polarity, invertible, directives } = bundle;

  // Build AST constructor functions
  const ASTConstructors = buildAST(constructors);

  // Build parser
  const parse = buildParser(constructors);

  // Build renderer
  const render = buildRenderer(constructors);

  return {
    name: bundle.name,
    baseTypes: bundle.baseTypes,
    constructors,
    directives,
    rules,
    polarity,
    invertible,
    AST: ASTConstructors,
    parse,
    render,

    // Utility functions
    connectivesFor: (typeName) => {
      return Object.values(constructors).filter(c => c.returnType === typeName);
    },
    isPositive: (tag) => polarity[tag] === 'positive',
    isNegative: (tag) => polarity[tag] === 'negative',
    isInvertible: (ruleName) => invertible[ruleName] === true
  };
}

/**
 * Build AST constructor functions
 */
function buildAST(constructors) {
  const AST = {
    freevar: (name) => ({ tag: 'freevar', children: [name] })
  };

  for (const [name, constr] of Object.entries(constructors)) {
    const arity = constr.argTypes.length;

    if (arity === 0) {
      AST[name] = () => ({ tag: name, children: [] });
    } else if (arity === 1) {
      AST[name] = (a) => ({ tag: name, children: [a] });
    } else if (arity === 2) {
      AST[name] = (a, b) => ({ tag: name, children: [a, b] });
    } else if (arity === 3) {
      AST[name] = (a, b, c) => ({ tag: name, children: [a, b, c] });
    } else {
      AST[name] = (...args) => ({ tag: name, children: args });
    }
  }

  return AST;
}

/**
 * Build precedence-climbing parser
 */
function buildParser(constructors) {
  const operators = [];
  const nullary = {};
  const unaryPrefix = {};

  for (const [name, constr] of Object.entries(constructors)) {
    const ann = constr.annotations;
    if (!ann || !ann.ascii) continue;

    const ascii = ann.ascii;
    const prec = ann.prec;
    const precedence = typeof prec === 'object' ? prec.precedence : (prec || 100);
    const assoc = typeof prec === 'object' ? prec.associativity : 'left';

    if (constr.argTypes.length === 0) {
      nullary[ascii] = name;
    } else if (constr.argTypes.length === 1 && (ascii.startsWith('!') || ascii.match(/^[!@#$%^&*]+\s*_$/))) {
      const op = ascii.replace(/\s*_\s*$/, '').trim();
      unaryPrefix[op] = { name, precedence };
    } else if (constr.argTypes.length === 2 && ascii.includes('_')) {
      const op = ascii.replace(/_/g, '').trim();
      operators.push({ name, op, precedence, assoc, ascii });
    }
  }

  operators.sort((a, b) => a.precedence - b.precedence);

  return function parse(input) {
    let pos = 0;
    const src = input.trim();

    const ws = () => { while (pos < src.length && /\s/.test(src[pos])) pos++; };
    const consume = (s) => { if (src.slice(pos, pos + s.length) === s) { pos += s.length; ws(); return true; } return false; };

    const matchOp = () => {
      ws();
      for (const op of operators) {
        if (src.slice(pos, pos + op.op.length) === op.op) {
          return op;
        }
      }
      return null;
    };

    const parseExpr = (minPrec = 0) => {
      let left = parseAtom();

      while (true) {
        ws();
        const op = matchOp();
        if (!op || op.precedence < minPrec) break;

        pos += op.op.length;
        ws();

        const nextMinPrec = op.assoc === 'right' ? op.precedence : op.precedence + 1;
        const right = parseExpr(nextMinPrec);
        left = { tag: op.name, children: [left, right] };
      }

      return left;
    };

    const parseAtom = () => {
      ws();

      for (const [lit, name] of Object.entries(nullary)) {
        if (src.slice(pos, pos + lit.length) === lit &&
            (pos + lit.length >= src.length || !/\w/.test(src[pos + lit.length]))) {
          pos += lit.length;
          ws();
          return { tag: name, children: [] };
        }
      }

      for (const [op, info] of Object.entries(unaryPrefix)) {
        if (src.slice(pos, pos + op.length) === op) {
          pos += op.length;
          ws();
          const inner = parseAtom();
          return { tag: info.name, children: [inner] };
        }
      }

      if (consume('(')) {
        const inner = parseExpr(0);
        consume(')');
        return inner;
      }

      const idMatch = src.slice(pos).match(/^[A-Za-z_][A-Za-z0-9_]*/);
      if (idMatch) {
        const name = idMatch[0];
        pos += name.length;
        ws();

        if (name.length === 1 && /[A-Z]/.test(name)) {
          return { tag: 'freevar', children: [name] };
        }
        return { tag: 'atom', children: [name] };
      }

      throw new Error(`Parse error at position ${pos}: unexpected '${src.slice(pos, pos + 10)}'`);
    };

    const result = parseExpr(0);
    ws();
    if (pos < src.length) {
      throw new Error(`Parse error: unexpected '${src.slice(pos)}'`);
    }
    return result;
  };
}

/**
 * Build renderer
 */
function buildRenderer(constructors) {
  const formats = { ascii: {}, latex: {} };

  for (const [name, constr] of Object.entries(constructors)) {
    const ann = constr.annotations;
    if (!ann) continue;

    if (ann.ascii) {
      formats.ascii[name] = {
        template: ann.ascii,
        prec: typeof ann.prec === 'object' ? ann.prec.precedence : (ann.prec || 100)
      };
    }

    if (ann.latex) {
      formats.latex[name] = {
        template: ann.latex,
        prec: typeof ann.prec === 'object' ? ann.prec.precedence : (ann.prec || 100)
      };
    }
  }

  formats.ascii.freevar = { template: '_', prec: 100 };
  formats.latex.freevar = { template: '#1', prec: 100 };

  return function render(ast, format = 'ascii', parentPrec = 0) {
    if (!ast?.tag) return String(ast ?? '');

    const fmt = formats[format]?.[ast.tag];
    if (!fmt) return `${ast.tag}(${ast.children.map(c => render(c, format, 0)).join(', ')})`;

    let result = fmt.template;

    if (result.includes('_')) {
      for (const child of ast.children) {
        const childStr = render(child, format, fmt.prec);
        result = result.replace('_', childStr);
      }
    } else {
      ast.children.forEach((child, i) => {
        const childStr = render(child, format, fmt.prec);
        result = result.replace(new RegExp(`#${i + 1}`, 'g'), childStr);
      });
    }

    if (fmt.prec < parentPrec) {
      result = `(${result})`;
    }

    return result;
  };
}

/**
 * Create sequent parser for the loaded calculus
 */
function createSequentParser() {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');

  function parseSequent(input) {
    const src = input.trim();
    const parts = src.split('|-');
    if (parts.length !== 2) {
      throw new Error(`Invalid sequent: expected '|-' turnstile in "${src}"`);
    }

    const [antecedentStr, succedentStr] = parts.map(s => s.trim());
    const succedent = parseHyp(succedentStr);

    const linearFormulas = [];
    if (antecedentStr) {
      const hyps = splitTopLevel(antecedentStr, ',');
      for (const hyp of hyps) {
        const formula = parseHyp(hyp.trim());
        if (formula) linearFormulas.push(formula);
      }
    }

    return Seq.fromArrays(linearFormulas, [], succedent);
  }

  function parseHyp(input) {
    const trimmed = input.trim();
    if (!trimmed) return null;

    const colonIdx = trimmed.indexOf(':');
    if (colonIdx > 0) {
      const formulaStr = trimmed.slice(colonIdx + 1).trim();
      return calculus.parse(formulaStr);
    }

    return calculus.parse(trimmed);
  }

  function splitTopLevel(str, delim) {
    const parts = [];
    let depth = 0;
    let start = 0;

    for (let i = 0; i < str.length; i++) {
      const c = str[i];
      if (c === '(') depth++;
      else if (c === ')') depth--;
      else if (c === delim && depth === 0) {
        parts.push(str.slice(start, i));
        start = i + 1;
      }
    }

    parts.push(str.slice(start));
    return parts.filter(s => s.trim());
  }

  function formatSequent(seq, format = 'ascii') {
    const linear = Seq.getContext(seq, 'linear');
    const cart = Seq.getContext(seq, 'cartesian');

    const formatFormula = (f) => calculus.render(f, format);

    const linearPart = linear.map(formatFormula).join(', ');
    const cartPart = cart.length > 0 ? cart.map(formatFormula).join(', ') + ' ; ' : '';
    const succedentPart = formatFormula(seq.succedent);

    if (format === 'latex') {
      const turnstile = '\\vdash';
      if (cartPart) {
        return `${cartPart}${linearPart} ${turnstile} ${succedentPart}`;
      }
      return linearPart ? `${linearPart} ${turnstile} ${succedentPart}` : `${turnstile} ${succedentPart}`;
    }

    if (cartPart) {
      return `${cartPart}${linearPart} |- ${succedentPart}`;
    }
    return linearPart ? `${linearPart} |- ${succedentPart}` : `|- ${succedentPart}`;
  }

  return {
    parseSequent,
    parseHyp,
    formatSequent
  };
}

// ============================================================================
// High-Level API (same as lib/v2/index.js)
// ============================================================================

/**
 * Prove a sequent string
 */
async function proveString(sequentStr, opts = {}) {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');

  const sp = createSequentParser();
  const seq = sp.parseSequent(sequentStr);

  const p = prover.create(calculus);
  const result = p.prove(seq, opts);

  return {
    ...result,
    sequent: seq,
    formatted: sp.formatSequent(seq)
  };
}

/**
 * Parse a formula string
 */
function parseFormula(formulaStr) {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');
  return calculus.parse(formulaStr);
}

/**
 * Parse a sequent string
 */
function parseSequent(sequentStr) {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');
  const sp = createSequentParser();
  return sp.parseSequent(sequentStr);
}

/**
 * Render a formula or sequent
 */
function render(ast, format = 'ascii') {
  if (!calculus) throw new Error('Call init() or initFromBundle() first');

  if (ast?.succedent) {
    const sp = createSequentParser();
    return sp.formatSequent(ast, format);
  }

  return calculus.render(ast, format);
}

/**
 * Get the loaded calculus
 */
function getCalculus() {
  return calculus;
}

/**
 * Check if initialized
 */
function isInitialized() {
  return calculus !== null;
}

module.exports = {
  // Initialization
  initFromBundle,
  isInitialized,
  getCalculus,

  // High-level API
  proveString,
  parseFormula,
  parseSequent,
  render,
  createSequentParser,

  // Proof search
  prove: prover.prove,
  createProver: prover.create,

  // Sequent operations
  Seq,

  // AST utilities
  ast: {
    copy: AST.copy,
    isAtomic: AST.isAtomic,
    freeVars: AST.freeVars,
    occurs
  },

  // Substitution
  substitute: { copy, apply },

  // Unification
  unify: { unify, match }
};
