/**
 * v2 Calculus Module
 *
 * Loads calculus definition from .family/.calc/.rules files and generates:
 * - AST constructors (e.g., tensor(a, b), loli(a, b))
 * - Parser for object-language formulas
 * - Renderer with @ascii/@latex support
 * - Inference rules with metadata (invertibility, polarity)
 *
 * NOTHING is hardcoded - everything is generated from the spec files.
 */

const generator = require('../../celf/generator');
const tsParser = require('../../celf/ts-parser');
const path = require('path');

// Cache for loaded calculi
const cache = new Map();

/**
 * Load a calculus from spec files
 * @param {string} calcPath - Path to .calc file
 * @param {string} rulesPath - Path to .rules file (optional)
 * @returns {Promise<Calculus>} Loaded calculus with AST, parser, renderer, rules
 */
async function load(calcPath, rulesPath = null) {
  const cacheKey = `${calcPath}:${rulesPath || ''}`;
  if (cache.has(cacheKey)) return cache.get(cacheKey);

  // Use existing generator infrastructure to load with @extends chain
  const spec = await generator.loadWithExtends(calcPath);

  // Load rules if path provided
  let rules = {};
  if (rulesPath) {
    rules = await loadRules(rulesPath, spec.constructors);
  }

  // Build calculus object from spec
  const calculus = buildCalculus(spec, rules);

  cache.set(cacheKey, calculus);
  return calculus;
}

/**
 * Load the default ILL calculus with rules
 */
async function loadILL() {
  const baseDir = path.join(__dirname, '../../../calculus');
  return load(
    path.join(baseDir, 'ill.calc'),
    path.join(baseDir, 'ill.rules')
  );
}

/**
 * Load inference rules from .rules file
 */
async function loadRules(rulesPath, constructors) {
  await tsParser.init();
  const result = await tsParser.parseFile(rulesPath);
  if (!result.success) {
    throw new Error(`Failed to parse ${rulesPath}: ${result.error}`);
  }

  const rules = {};
  for (const decl of result.ast.declarations) {
    if (decl.type !== 'ClauseDecl') continue;
    if (decl.name.startsWith('@')) continue;  // Skip directives

    const annotations = {};
    for (const ann of decl.annotations || []) {
      if (ann.value?.type === 'BoolValue') {
        annotations[ann.key] = ann.value.value;
      } else if (ann.value?.type === 'StringValue') {
        annotations[ann.key] = ann.value.value;
      } else if (ann.value?.type === 'IdentValue') {
        annotations[ann.key] = ann.value.name;
      } else if (ann.value) {
        annotations[ann.key] = ann.value;
      } else {
        annotations[ann.key] = true;
      }
    }

    rules[decl.name] = {
      name: decl.name,
      head: decl.head,
      premises: decl.premises || [],
      invertible: annotations.invertible ?? null,
      pretty: annotations.pretty || decl.name,
      structural: annotations.structural ?? false,
      bridge: annotations.bridge || null,
      numPremises: (decl.premises || []).length
    };
  }

  return rules;
}

/**
 * Build calculus runtime from extracted spec
 */
function buildCalculus(spec, rules = {}) {
  const { baseTypes, constructors, directives } = spec;

  // Group constructors by return type
  const byType = {};
  for (const [name, constr] of Object.entries(constructors)) {
    const rt = constr.returnType;
    if (!byType[rt]) byType[rt] = [];
    byType[rt].push(constr);
  }

  // Build AST constructors
  const AST = buildAST(constructors);

  // Build parser
  const parser = buildParser(constructors);

  // Build renderer
  const render = buildRenderer(constructors);

  // Build polarity map - explicit @polarity OR inferred from rule structure
  const polarity = {};
  const { inferPolarityFromRules, inferInvertibilityFromRule } = require('../meta/focusing');
  const inferredPolarity = inferPolarityFromRules(rules);

  for (const [name, constr] of Object.entries(constructors)) {
    if (constr.annotations.polarity) {
      // Explicit annotation takes precedence
      polarity[name] = constr.annotations.polarity;
    } else if (inferredPolarity[name]) {
      // Fall back to inference
      polarity[name] = inferredPolarity[name];
    }
  }

  // Build invertibility map - explicit @invertible OR inferred from polarity
  const invertible = {};
  for (const [name, rule] of Object.entries(rules)) {
    if (rule.invertible !== null) {
      // Explicit annotation
      invertible[name] = rule.invertible;
    } else {
      // Infer from polarity and rule position (L/R)
      const inferred = inferInvertibilityFromRule(name, rule, polarity);
      if (inferred !== null) {
        invertible[name] = inferred;
      }
    }
  }

  return {
    name: directives.family || 'calculus',
    baseTypes,
    constructors,
    directives,
    rules,
    AST,
    parse: parser,
    render,

    // Focusing metadata
    polarity,      // connective -> 'positive' | 'negative'
    invertible,    // rule -> true | false

    // Utility: get all connectives for a type
    connectivesFor: (typeName) => byType[typeName] || [],

    // Utility: check if a connective is positive/negative
    isPositive: (tag) => polarity[tag] === 'positive',
    isNegative: (tag) => polarity[tag] === 'negative',

    // Utility: check if a rule is invertible
    isInvertible: (ruleName) => invertible[ruleName] === true
  };
}

/**
 * Build AST constructor functions from spec
 */
function buildAST(constructors) {
  const AST = {
    // Special: freevar for metavariables (always present)
    freevar: (name) => ({ tag: 'freevar', children: [name] })
  };

  for (const [name, constr] of Object.entries(constructors)) {
    const arity = constr.argTypes.length;

    if (arity === 0) {
      // Nullary constructor: constant
      AST[name] = () => ({ tag: name, children: [] });
    } else if (arity === 1) {
      // Unary constructor
      AST[name] = (a) => ({ tag: name, children: [a] });
    } else if (arity === 2) {
      // Binary constructor
      AST[name] = (a, b) => ({ tag: name, children: [a, b] });
    } else if (arity === 3) {
      // Ternary constructor
      AST[name] = (a, b, c) => ({ tag: name, children: [a, b, c] });
    } else {
      // General case
      AST[name] = (...args) => ({ tag: name, children: args });
    }
  }

  return AST;
}

/**
 * Build parser from spec
 * Uses precedence climbing with @prec/@ascii annotations
 */
function buildParser(constructors) {
  // Extract operators with precedence
  const operators = [];
  const nullary = {};
  const unaryPrefix = {};

  for (const [name, constr] of Object.entries(constructors)) {
    const ann = constr.annotations;
    if (!ann.ascii) continue;

    const ascii = ann.ascii;
    const prec = ann.prec;
    const precedence = typeof prec === 'object' ? prec.precedence : (prec || 100);
    const assoc = typeof prec === 'object' ? prec.associativity : 'left';

    if (constr.argTypes.length === 0) {
      // Nullary: e.g., "I" for one, "--" for any
      nullary[ascii] = name;
    } else if (constr.argTypes.length === 1 && ascii.startsWith('!') || ascii.match(/^[!@#$%^&*]+\s*_$/)) {
      // Unary prefix: "! _" for bang
      const op = ascii.replace(/\s*_\s*$/, '').trim();
      unaryPrefix[op] = { name, precedence };
    } else if (constr.argTypes.length === 2 && ascii.includes('_')) {
      // Binary infix: "_ * _" for tensor
      const op = ascii.replace(/_/g, '').trim();
      operators.push({ name, op, precedence, assoc, ascii });
    }
  }

  // Sort operators by precedence (lower = looser binding)
  operators.sort((a, b) => a.precedence - b.precedence);

  return function parse(input) {
    let pos = 0;
    const src = input.trim();

    const ws = () => { while (pos < src.length && /\s/.test(src[pos])) pos++; };

    const peek = (n = 1) => src.slice(pos, pos + n);
    const consume = (s) => { if (src.slice(pos, pos + s.length) === s) { pos += s.length; ws(); return true; } return false; };

    // Check for operator at current position
    const matchOp = () => {
      ws();
      for (const op of operators) {
        if (src.slice(pos, pos + op.op.length) === op.op) {
          return op;
        }
      }
      return null;
    };

    // Precedence climbing parser
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

      // Check nullary
      for (const [lit, name] of Object.entries(nullary)) {
        if (src.slice(pos, pos + lit.length) === lit &&
            (pos + lit.length >= src.length || !/\w/.test(src[pos + lit.length]))) {
          pos += lit.length;
          ws();
          return { tag: name, children: [] };
        }
      }

      // Check unary prefix
      for (const [op, info] of Object.entries(unaryPrefix)) {
        if (src.slice(pos, pos + op.length) === op) {
          pos += op.length;
          ws();
          const inner = parseAtom();
          return { tag: info.name, children: [inner] };
        }
      }

      // Parenthesized expression
      if (consume('(')) {
        const inner = parseExpr(0);
        consume(')');
        return inner;
      }

      // Identifier (atom or freevar)
      const idMatch = src.slice(pos).match(/^[A-Za-z_][A-Za-z0-9_]*/);
      if (idMatch) {
        const name = idMatch[0];
        pos += name.length;
        ws();

        // Uppercase single letter = freevar, otherwise atom
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
 * Build renderer from spec
 * Uses @ascii/@latex annotations
 */
function buildRenderer(constructors) {
  // Build format tables
  const formats = { ascii: {}, latex: {} };

  for (const [name, constr] of Object.entries(constructors)) {
    const ann = constr.annotations;

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

  // Add freevar handling
  formats.ascii.freevar = { template: '_', prec: 100 };
  formats.latex.freevar = { template: '#1', prec: 100 };

  return function render(ast, format = 'ascii', parentPrec = 0) {
    if (!ast?.tag) return String(ast ?? '');

    const fmt = formats[format]?.[ast.tag];
    if (!fmt) return `${ast.tag}(${ast.children.map(c => render(c, format, 0)).join(', ')})`;

    let result = fmt.template;

    // Replace placeholders with children
    if (result.includes('_')) {
      // ASCII format: _ placeholders
      for (const child of ast.children) {
        const childStr = render(child, format, fmt.prec);
        result = result.replace('_', childStr);
      }
    } else {
      // LaTeX format: #1, #2, ... placeholders
      ast.children.forEach((child, i) => {
        const childStr = render(child, format, fmt.prec);
        result = result.replace(new RegExp(`#${i + 1}`, 'g'), childStr);
      });
    }

    // Add parentheses if needed
    if (fmt.prec < parentPrec) {
      result = format === 'latex' ? `(${result})` : `(${result})`;
    }

    return result;
  };
}

/**
 * Clear the cache
 */
function clearCache() {
  cache.clear();
}

module.exports = {
  load,
  loadILL,
  clearCache
};
