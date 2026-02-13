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

/**
 * Build AST constructor functions from spec.
 * Returns constructors that produce content-addressed hashes via Store.put.
 */
function buildAST(constructors) {
  const AST = {
    freevar: (name) => Store.put('freevar', [name]),
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
    } else if (constr.argTypes.length === 1 && (ascii.startsWith('!') || ascii.match(/^[!@#$%^&*]+\s*_$/))) {
      const op = ascii.replace(/\s*_\s*$/, '').trim();
      unaryPrefix[op] = { name, precedence };
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
 * @param {{ operators, nullary, unaryPrefix }} tables
 * @returns {Function} parse(input) → hash
 */
function buildParserFromTables(tables) {
  const { operators, nullary, unaryPrefix } = tables;

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
        left = Store.put(op.name, [left, right]);
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
          return Store.put(name, []);
        }
      }

      for (const [op, info] of Object.entries(unaryPrefix)) {
        if (src.slice(pos, pos + op.length) === op) {
          pos += op.length;
          ws();
          const inner = parseAtom();
          return Store.put(info.name, [inner]);
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
          return Store.put('freevar', [name]);
        }
        return Store.put('atom', [name]);
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

module.exports = {
  buildAST,
  computeParserTables,
  buildParserFromTables,
  buildParser,
  computeRendererFormats,
  buildRendererFromFormats,
  buildRenderer,
  computeConnectivesByType
};
