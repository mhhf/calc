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
  const { nullary, unaryPrefix } = tables;
  const binderDefs = tables.binders || null;
  const multiCharFV = tables.multiCharFreevars || false;
  const parseNumbers = tables.numbers || false;
  const application = tables.application || false;
  const hasArrows = tables.arrows || false;
  const hasForwardRules = tables.forwardRules || false;
  const binaryNorm = tables.binaryNormalization || false;

  // Build operator list: start with calculus operators, add synthetic ones
  const operators = tables.operators.slice();
  if (hasArrows) {
    operators.push({ name: 'arrow', op: '->', precedence: 40, assoc: 'right' });
  }
  if (hasForwardRules) {
    operators.push({ name: 'loli', op: '-o', precedence: 50, assoc: 'right' });
  }
  operators.sort((a, b) => a.precedence - b.precedence);

  // Binder stack for de Bruijn encoding (shared across a single parse call)
  const binderStack = [];

  return function parse(input) {
    let pos = 0;
    const src = input.trim();
    binderStack.length = 0;

    const ws = () => { while (pos < src.length && /\s/.test(src[pos])) pos++; };
    const consume = (s) => { if (src.slice(pos, pos + s.length) === s) { pos += s.length; ws(); return true; } return false; };

    const matchOp = () => {
      ws();
      for (const op of operators) {
        if (src.slice(pos, pos + op.op.length) === op.op) {
          // Word-boundary check for alpha operators (avoid matching 'oplus' at start of 'oplus_l')
          const endPos = pos + op.op.length;
          if (/[a-zA-Z]/.test(op.op[op.op.length - 1]) && endPos < src.length && /\w/.test(src[endPos])) continue;
          return op;
        }
      }
      return null;
    };

    /** Check if current position can start a primary (atom/app argument). */
    const canStartPrimary = () => {
      if (pos >= src.length) return false;
      const c = src[pos];
      if (/[A-Za-z_'(]/.test(c)) return true;
      if (c === '!' && unaryPrefix['!']) return true;
      if (parseNumbers && /\d/.test(c)) return true;
      return false;
    };

    const parseExpr = (minPrec = 0) => {
      let left = application ? parseApp() : parseAtom();

      while (true) {
        ws();
        const op = matchOp();
        if (!op || op.precedence < minPrec) break;

        pos += op.op.length;
        ws();

        // Special: -o { body } → loli(left, monad(body))
        if (hasForwardRules && op.name === 'loli' && pos < src.length && src[pos] === '{') {
          pos++; ws();
          const body = parseExpr(0);
          ws(); consume('}');
          left = Store.put('loli', [left, Store.put('monad', [body])]);
          continue;
        }

        const nextMinPrec = op.assoc === 'right' ? op.precedence : op.precedence + 1;
        const right = parseExpr(nextMinPrec);
        left = Store.put(op.name, [left, right]);
      }

      return left;
    };

    /** Parse application: `f x y` → Store.put('f', [x, y]) (flat predicate form) */
    const parseApp = () => {
      let head = parseAtom();
      const args = [];

      while (canStartPrimary()) {
        args.push(parseAtom());
      }

      if (args.length === 0) return head;

      // Binary normalization: (i X) / (o X) where X is binlit → binlit
      if (binaryNorm) {
        const headNode = Store.get(head);
        if (headNode?.tag === 'atom' && args.length === 1 &&
            (headNode.children[0] === 'i' || headNode.children[0] === 'o')) {
          const argNode = Store.get(args[0]);
          if (argNode?.tag === 'binlit') {
            const val = argNode.children[0];
            return Store.put('binlit', [headNode.children[0] === 'i' ? val * 2n + 1n : val * 2n]);
          }
        }
      }

      // Flat predicate form: atom head → Store.put(name, args)
      const headNode = Store.get(head);
      if (headNode?.tag === 'atom') {
        return Store.put(headNode.children[0], args);
      }

      // Variable/unknown head: curried app form
      let result = head;
      for (const arg of args) {
        result = Store.put('app', [result, arg]);
      }
      return result;
    };

    const parseAtom = () => {
      ws();

      // Binder keywords: exists X. body / forall X. body (de Bruijn)
      if (binderDefs) {
        for (const [kw, tagName] of Object.entries(binderDefs)) {
          if (src.slice(pos, pos + kw.length) === kw &&
              (pos + kw.length >= src.length || !/\w/.test(src[pos + kw.length]))) {
            const savedPos = pos;
            pos += kw.length; ws();
            const varMatch = src.slice(pos).match(/^[A-Z][a-zA-Z0-9_']*/);
            if (varMatch) {
              const varName = varMatch[0];
              pos += varName.length; ws();
              if (pos < src.length && src[pos] === '.') {
                pos++; ws();
                binderStack.push(varName);
                const body = parseExpr(0);
                binderStack.pop();
                return Store.put(tagName, [body]);
              }
            }
            // Not binder syntax — fall through to unaryPrefix
            pos = savedPos;
          }
        }
      }

      // Number literals: 42, 0xFF
      if (parseNumbers) {
        const numMatch = src.slice(pos).match(/^(0x[0-9a-fA-F]+|\d+)/);
        if (numMatch && (pos === 0 || !/[a-zA-Z_]/.test(src[pos - 1]))) {
          pos += numMatch[0].length; ws();
          return Store.put('binlit', [BigInt(numMatch[0])]);
        }
      }

      for (const [lit, name] of Object.entries(nullary)) {
        if (src.slice(pos, pos + lit.length) === lit &&
            (pos + lit.length >= src.length || !/\w/.test(src[pos + lit.length]))) {
          pos += lit.length;
          ws();
          return Store.put(name, []);
        }
      }

      for (const [op, info] of Object.entries(unaryPrefix)) {
        // Skip binder keywords — already handled above
        if (binderDefs && binderDefs[op] !== undefined) continue;
        if (src.slice(pos, pos + op.length) === op) {
          // Keyword prefixes need word boundary check
          if (info.keyword && pos + op.length < src.length && /\w/.test(src[pos + op.length])) continue;
          pos += op.length;
          ws();
          // When application is enabled, prefix applies to full application expr
          const inner = application ? parseApp() : parseAtom();
          return Store.put(info.name, [inner]);
        }
      }

      if (consume('(')) {
        const inner = parseExpr(0);
        consume(')');
        return inner;
      }

      const idMatch = src.slice(pos).match(/^[A-Za-z_'][A-Za-z0-9_']*/);
      if (idMatch) {
        const name = idMatch[0];
        pos += name.length;
        ws();

        // Binary normalization: 'e' → binlit(0n)
        if (binaryNorm && name === 'e') {
          return Store.put('binlit', [0n]);
        }

        // Framework keyword: 'type' → Store.put('type', [])
        if (hasArrows && name === 'type') {
          return Store.put('type', []);
        }

        if (/[A-Z]/.test(name[0])) {
          // Check binder stack for bound variables (de Bruijn)
          for (let i = binderStack.length - 1; i >= 0; i--) {
            if (binderStack[i] === name) {
              return Store.put('bound', [BigInt(binderStack.length - 1 - i)]);
            }
          }
          // Free variable
          if (multiCharFV) {
            return Store.put('freevar', ['_' + name]);
          }
          if (name.length === 1) {
            return Store.put('freevar', [name]);
          }
          return Store.put('atom', [name]);
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
