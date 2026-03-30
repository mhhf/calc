/**
 * Shared builders for calculus runtime objects.
 *
 * Single source of truth for buildAST, buildParser, buildRenderer.
 * Used by both calculus/index.js (Node file loading) and browser.js (bundle hydration).
 *
 * Data computation (computeParserTables, computeRendererFormats) is separated
 * from function creation (buildParserFromTables, buildRendererFromFormats) so
 * that tables can be precomputed at build time into ill.json.
 */

const Store = require('../kernel/store');
const { computeEarleyGrammarFromTables, buildParserFromGrammar } = require('../parser/earley-grammar');

/**
 * Build AST constructor functions from spec.
 * Returns constructors that produce content-addressed hashes via Store.put.
 */
function buildAST(constructors) {
  const AST = {
    freevar: (name) => Store.put('freevar', [name]),
    metavar: (name) => Store.put('metavar', [name]),
    atom: (name) => Store.put('atom', [name]),

    // Store access utilities
    get: Store.get,
    tag: Store.tag,
    children: Store.children,
    child: Store.child,
    isTerm: Store.isTerm,
    isTermChild: Store.isTermChild,
    eq: Store.eq
  };

  for (const [name, constr] of Object.entries(constructors)) {
    const arity = constr.argTypes.length;

    if (arity === 0) {
      AST[name] = () => Store.put(name, []);
    } else if (arity === 1) {
      AST[name] = (a) => Store.put(name, [a]);
    } else if (arity === 2) {
      AST[name] = (a, b) => Store.put(name, [a, b]);
    } else if (arity === 3) {
      AST[name] = (a, b, c) => Store.put(name, [a, b, c]);
    } else {
      AST[name] = (...args) => Store.put(name, args);
    }
  }

  return AST;
}

// ─── Parser ─────────────────────────────────────────────────────────────────

/**
 * Compute parser tables from constructor annotations (pure data, serializable).
 * @param {Object} constructors - Constructor definitions with annotations
 * @returns {{ operators: Array, nullary: Object, unaryPrefix: Object }}
 */
function computeParserTables(constructors) {
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
    } else if (constr.argTypes.length === 1 && (ascii.startsWith('!') || ascii.match(/^[!@#$%^&*]+\s*_$/) || ascii.match(/^\w+\s+_$/))) {
      const op = ascii.replace(/\s*_\s*$/, '').trim();
      unaryPrefix[op] = { name, precedence, keyword: /^[a-z]/.test(op) };
    } else if (constr.argTypes.length === 2 && ascii.includes('_')) {
      const op = ascii.replace(/_/g, '').trim();
      operators.push({ name, op, precedence, assoc, ascii });
    }
  }

  operators.sort((a, b) => a.precedence - b.precedence);

  return { operators, nullary, unaryPrefix };
}

/**
 * Build parser from precomputed tables.
 *
 * Extended features (opt-in via tables fields):
 *   binders: { exists: 'exists', forall: 'forall' }
 *     — enables `exists X. body` / `forall X. body` with de Bruijn encoding
 *   multiCharFreevars: true
 *     — uppercase identifiers (any length) → freevar with '_' prefix
 *   numbers: true
 *     — decimal and 0x hex literals → Store.put('binlit', [BigInt(n)])
 *   application: true
 *     — juxtaposition: `f x y` → Store.put('f', [x, y]) (flat predicate form)
 *   arrows: true
 *     — `A -> B` → Store.put('arrow', [A, B])
 *   forwardRules: true
 *     — `A -o { B }` → loli(A, monad(B)), `A -o B` → loli(A, B)
 *   binaryNormalization: true
 *     — `e` → binlit(0n), `(i X)` where X is binlit → binlit(X*2+1)
 *
 * @param {{ operators, nullary, unaryPrefix, binders?, multiCharFreevars?, numbers?, application?, arrows?, forwardRules?, binaryNormalization? }} tables
 * @returns {Function} parse(input) → hash
 */
function buildParserFromTables(tables) {
  const spec = computeEarleyGrammarFromTables(tables);
  return buildParserFromGrammar(spec);
}

/**
 * Build parser from constructor annotations (convenience: compute tables + build).
 */
function buildParser(constructors) {
  return buildParserFromTables(computeParserTables(constructors));
}

// ─── Renderer ───────────────────────────────────────────────────────────────

/**
 * Compute renderer format tables from constructor annotations (pure data, serializable).
 * @param {Object} constructors - Constructor definitions with annotations
 * @returns {{ ascii: Object, latex: Object }}
 */
function computeRendererFormats(constructors) {
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
  formats.ascii.atom = { template: '_', prec: 100 };
  formats.latex.atom = { template: '#1', prec: 100 };

  return formats;
}

/**
 * Build renderer from precomputed format tables.
 * @param {{ ascii: Object, latex: Object }} formats
 * @returns {Function} render(h, format, parentPrec) → string
 */
function buildRendererFromFormats(formats) {
  return function render(h, format = 'ascii', parentPrec = 0) {
    // Handle hashes — look up in Store
    if (typeof h === 'number') {
      const node = Store.get(h);
      if (!node) return String(h);
      return render(node, format, parentPrec);
    }

    // Handle primitives
    if (typeof h === 'string') return h;
    if (h == null) return '';

    // Handle AST objects ({ tag, children })
    if (!h.tag) return String(h);

    const fmt = formats[format]?.[h.tag];
    if (!fmt) return `${h.tag}(${h.children.map(c => render(c, format, 0)).join(', ')})`;

    let result = fmt.template;

    if (result.includes('_')) {
      for (const child of h.children) {
        const childStr = render(child, format, fmt.prec);
        result = result.replace('_', childStr);
      }
    } else {
      h.children.forEach((child, i) => {
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
 * Build renderer from constructor annotations (convenience: compute formats + build).
 */
function buildRenderer(constructors) {
  return buildRendererFromFormats(computeRendererFormats(constructors));
}

// ─── Connectives by Type ────────────────────────────────────────────────────

/**
 * Group constructors by return type (pure data, serializable).
 * @param {Object} constructors
 * @returns {Object} { formula: [...names], term: [...names], ... }
 */
function computeConnectivesByType(constructors) {
  const byType = {};
  for (const [name, constr] of Object.entries(constructors)) {
    const rt = constr.returnType;
    if (!byType[rt]) byType[rt] = [];
    byType[rt].push(name);
  }
  return byType;
}

/**
 * Derive connective roles from constructor annotations and polarity.
 * Maps semantic roles (product, implication, etc.) to connective names
 * based on (category, arity, polarity) triples.
 */
function deriveRoles(constructors, polarity) {
  const roles = {};
  for (const [name, constr] of Object.entries(constructors)) {
    const cat = constr.annotations?.category;
    const arity = constr.argTypes?.length ?? 0;
    const pol = polarity[name];
    let role = null;
    if (cat === 'multiplicative') {
      if (arity === 2 && pol === 'positive') role = 'product';
      else if (arity === 2 && pol === 'negative') role = 'implication';
      else if (arity === 0) role = 'unit';
    } else if (cat === 'additive') {
      if (arity === 2 && pol === 'positive') role = 'internal-choice';
      else if (arity === 2 && pol === 'negative') role = 'external-choice';
      else if (arity === 0) role = 'additive-zero';
    } else if (cat === 'exponential' && arity === 1) {
      role = 'exponential';
    } else if (cat === 'monad' && arity === 1) {
      role = 'computation';
    } else if (cat === 'quantifier' && arity === 1 && pol === 'positive') {
      role = 'existential';
    }
    if (role) {
      if (roles[role]) {
        console.warn(`Role collision: '${role}' claimed by both '${roles[role]}' and '${name}'`);
      }
      roles[role] = name;
    }
  }
  return roles;
}

module.exports = {
  buildAST,
  computeParserTables,
  buildParserFromTables,
  buildParser,
  computeRendererFormats,
  buildRendererFromFormats,
  buildRenderer,
  computeConnectivesByType,
  deriveRoles
};
