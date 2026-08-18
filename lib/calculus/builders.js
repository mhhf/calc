/**
 * Shared builders for calculus runtime objects.
 *
 * Single source of truth for buildAST, buildParser, buildRenderer.
 * Used by both calculus/index.js (Node file loading) and browser.js (bundle hydration).
 *
 * Parser: parserFromTables delegates to the Earley parser engine
 * (lib/parser/earley-grammar.js). parserTables extracts operator
 * metadata from constructor annotations (serializable for ill.json bundle).
 *
 * Renderer: rendererFormats is separated from rendererFromFormats
 * so that formats can be precomputed at build time into ill.json.
 */

import Store from '../kernel/store.js';
import { earleyGrammarFromTables, parserFromGrammar, extractParserTables } from '../parser/earley-grammar.js';
import { computationRole } from '../engine/formula-utils.js';
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
 * Delegates to the parser layer's one extractor (TODO_0265 Phase 3 —
 * previously duplicated here and in earleyGrammar).
 * @param {Object} constructors - Constructor definitions with annotations
 * @returns {{ operators, nullary, unaryPrefix, circumfix, gradedPrefix }}
 */
function parserTables(constructors) {
  return extractParserTables(constructors);
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
 *     — adds the `-o` operator (if absent) and `$` preserved sugar; the
 *       `{ B }` bracket form itself comes from the circumfix tables
 *   binaryNormalization: true
 *     — `e` → binlit(0n), `(i X)` where X is binlit → binlit(X*2+1)
 *
 * @param {{ operators, nullary, unaryPrefix, binders?, multiCharFreevars?, numbers?, application?, arrows?, forwardRules?, binaryNormalization? }} tables
 * @returns {Function} parse(input) → hash
 */
function parserFromTables(tables) {
  const spec = earleyGrammarFromTables(tables);
  return parserFromGrammar(spec);
}

/**
 * Build parser from constructor annotations (convenience: compute tables + build).
 *
 * Bracket forms (`{ _ }`, `{ #2 }`) and graded prefixes (`! #2`) are
 * derived from @ascii declarations by extractParserTables — a calculus
 * parses exactly what it declares. A graded (arity-2) circumfix
 * additionally needs parserOpts.gradeUnit (an in-process () => hash hook
 * supplying the elided unit grade); without it `{ expr }` throws loudly
 * (audit round 11, F1).
 */
function buildParser(constructors, parserOpts = {}) {
  // parserOpts are the standard grammar table flags (gradeUnit,
  // timedAnnotations, application, multiCharFreevars, binders, ...) —
  // merged over the declaration-derived tables.
  return parserFromTables({ ...parserTables(constructors), ...parserOpts });
}

// ─── Renderer ───────────────────────────────────────────────────────────────

/**
 * Compute renderer format tables from constructor annotations (pure data, serializable).
 * @param {Object} constructors - Constructor definitions with annotations
 * @returns {{ ascii: Object, latex: Object }}
 */
function rendererFormats(constructors) {
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
  // Exact rational leaf (ratlit, TODO_0265) — children are BigInts.
  formats.ascii.ratlit = { template: '#1/#2', prec: 100 };
  formats.latex.ratlit = { template: '\\frac{#1}{#2}', prec: 100 };

  return formats;
}

/**
 * Build renderer from precomputed format tables.
 *
 * opts (TODO_0265 Phase 4c — graded-circumfix fidelity): a template that
 * elides the grade child (`{ #2 }` on an arity-2 node, mirroring the
 * parser's elided-grade convention) drops information — render(gmonad(d,b))
 * was "{ b }" for ANY d. With opts.gradeUnit the renderer appends `@g`
 * whenever the grade differs from the unit (parse ∘ render = id);
 * opts.renderGrade overrides how the grade itself prints. No opts ⇒
 * bit-identical to the historical behavior.
 *
 * @param {{ ascii: Object, latex: Object }} formats
 * @param {{ gradeUnit?: () => number, renderGrade?: (h) => string }} [opts]
 * @returns {Function} render(h, format, parentPrec) → string
 */
function rendererFromFormats(formats, opts = {}) {
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
      // Elided-grade circumfix (`{ #2 }`, arity 2): restore the grade as a
      // postfix `@g` when it is not the unit (Phase 4c fidelity).
      if (opts.gradeUnit && h.children.length === 2 &&
          fmt.template.includes('#2') && !fmt.template.includes('#1')) {
        const g = h.children[0];
        if (g !== opts.gradeUnit()) {
          // Integer grades are binlit leaves — print the value, not the
          // structural fallback `binlit(n)`; everything else renders
          // normally (ratlit has a default `#1/#2` template).
          const gNode = typeof g === 'number' ? Store.get(g) : null;
          const gStr = opts.renderGrade ? opts.renderGrade(g)
            : (gNode && gNode.tag === 'binlit' ? String(gNode.children[0])
              : render(g, format, 100));
          result += '@' + gStr;
        }
      }
    }

    if (fmt.prec < parentPrec) {
      result = `(${result})`;
    }

    return result;
  };
}

/**
 * Build renderer from constructor annotations (convenience: compute formats + build).
 * @param {Object} [rendererOpts] - see rendererFromFormats (gradeUnit/renderGrade)
 */
function buildRenderer(constructors, rendererOpts) {
  return rendererFromFormats(rendererFormats(constructors), rendererOpts);
}

// ─── Connectives by Type ────────────────────────────────────────────────────

/**
 * Group constructors by return type (pure data, serializable).
 * @param {Object} constructors
 * @returns {Object} { formula: [...names], term: [...names], ... }
 */
function connByType(constructors) {
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
 *
 * Emits THE one role shape (TODO_0265 Phase 3, B7 — unified with
 * engine/formula-utils.js resolveConn): camelCase keys, `computation` is
 * a record { tag, bodyIdx, gradeIdx } (see computationRole), all other
 * roles are bare connective names. resolveConn produces the same record
 * from a connective table; every consumer (bridge, kernel, check-term)
 * reads this shape regardless of which side built the calculus.
 */
function deriveRoles(constructors, polarity) {
  const roles = {};
  for (const [name, constr] of Object.entries(constructors)) {
    const cat = constr.annotations?.category;
    const arity = constr.argTypes?.length ?? 0;
    const pol = polarity[name];
    let role = null;
    let value = name;
    if (cat === 'multiplicative') {
      if (arity === 2 && pol === 'positive') role = 'product';
      else if (arity === 2 && pol === 'negative') role = 'implication';
      else if (arity === 0) role = 'unit';
    } else if (cat === 'additive') {
      if (arity === 2 && pol === 'positive') role = 'internalChoice';
      else if (arity === 2 && pol === 'negative') role = 'externalChoice';
      else if (arity === 0) role = 'additiveZero';
    } else if (cat === 'exponential' && arity === 2) {
      role = 'exponential';
    } else if (cat === 'monad') {
      const rec = computationRole(name, arity);
      if (rec) { role = 'computation'; value = rec; }
    } else if (cat === 'quantifier' && arity === 1 && pol === 'positive') {
      role = 'existential';
    }
    if (role) {
      if (roles[role]) {
        const prev = roles[role].tag ?? roles[role];
        console.warn(`Role collision: '${role}' claimed by both '${prev}' and '${name}'`);
      }
      roles[role] = value;
    }
  }
  return roles;
}

export { buildAST, parserTables, parserFromTables, buildParser, rendererFormats, rendererFromFormats, buildRenderer, connByType, deriveRoles };
export default { buildAST, parserTables, parserFromTables, buildParser, rendererFormats, rendererFromFormats, buildRenderer, connByType, deriveRoles };
