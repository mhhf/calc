/**
 * Earley grammar generation from calculus constructor annotations.
 *
 * Generates a stratified CFG (Danielsson-Norell style) from the operator
 * table extracted from .calc files. Each precedence level becomes a
 * distinct nonterminal; associativity is encoded via same/next references.
 *
 * Binder scoping uses the "open/closed" technique: each binary operator's
 * RHS is a BINDER_p nonterminal that allows binder-or-expression. This
 * ensures `forall X. A * B` = `forall(tensor(A, B))` (body extends to end)
 * while `A * forall X. B` = `tensor(A, forall(B))` (binder on RHS only).
 *
 * The grammar is auto-generated from .calc constructor annotations.
 */

'use strict';

const Store = require('../kernel/store');
const { T, NT, grammar, tokenize, earleyParse, extractLazy } = require('./earley');

// ─── Grammar Generation ─────────────────────────────────────────────────────

/**
 * Generate Earley grammar from constructor annotations.
 *
 * @param {Object} constructors - Constructor definitions with annotations
 * @param {Object} opts - Opt-in features (binders, application, arrows, etc.)
 * @returns {{ rules, start, lexerConfig, hasBinders, hasApp, hasBinNorm, multiCharFV }}
 */
function computeEarleyGrammar(constructors, opts = {}) {
  const binderDefs = opts.binders || null;
  const hasApp = opts.application || false;
  const hasArrows = opts.arrows || false;
  const hasForward = opts.forwardRules || false;
  const hasNumbers = opts.numbers || false;
  const hasBinNorm = opts.binaryNormalization || false;
  const multiCharFV = opts.multiCharFreevars || false;

  // ── Extract operators from constructor annotations ──
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
    } else if (constr.argTypes.length === 1 &&
               (ascii.startsWith('!') ||
                ascii.match(/^[!@#$%^&*]+\s*_$/) ||
                ascii.match(/^\w+\s+_$/))) {
      const op = ascii.replace(/\s*_\s*$/, '').trim();
      unaryPrefix[op] = { name, precedence, keyword: /^[a-z]/.test(op) };
    } else if (constr.argTypes.length === 2 && ascii.includes('_')) {
      const op = ascii.replace(/_/g, '').trim();
      operators.push({ name, op, precedence, assoc });
    }
  }

  if (hasArrows) operators.push({ name: 'arrow', op: '->', precedence: 40, assoc: 'right' });
  if (hasForward) operators.push({ name: 'loli', op: '-o', precedence: 50, assoc: 'right' });
  operators.sort((a, b) => a.precedence - b.precedence);

  // ── Nonterminal allocation ──
  const precLevels = [...new Set(operators.map(o => o.precedence))].sort((a, b) => a - b);
  let ntId = 0;

  // START = top-level entry (binder-or-expression)
  const START = ntId++;

  // One pair per precedence level: L_p (closed) + BINDER_p (open, if binders)
  const precToNT = new Map();    // prec → closed NT
  const precToBNT = new Map();   // prec → binder NT (open)
  for (const p of precLevels) {
    precToNT.set(p, ntId++);
    if (binderDefs) precToBNT.set(p, ntId++);
  }

  const UNARY = ntId++;
  const BINDER_UNARY = binderDefs ? ntId++ : -1;
  const APP = hasApp ? ntId++ : -1;
  const ATOM = ntId++;
  const BVARS = binderDefs ? ntId++ : -1;

  // Chain helpers
  const LOOSEST = precLevels.length > 0 ? precToNT.get(precLevels[0]) : UNARY;
  const unaryNext = hasApp ? APP : ATOM;

  function nextClosedAfterPrec(prec) {
    const idx = precLevels.indexOf(prec);
    return idx === precLevels.length - 1 ? UNARY : precToNT.get(precLevels[idx + 1]);
  }

  // ── Build rules ──
  const rules = [];

  /** Add binder rules for a given nonterminal (body = START). */
  function addBinderRules(lhs) {
    if (!binderDefs) return;
    for (const [kw, tagName] of Object.entries(binderDefs)) {
      rules.push({
        lhs, rhs: [T(kw), NT(BVARS), T('.'), NT(START)],
        action: null, tag: 'binder', binderTag: tagName,
      });
    }
  }

  // ── START = binder-or-expression top level ──
  addBinderRules(START);
  rules.push({ lhs: START, rhs: [NT(LOOSEST)], action: c => c[0], tag: 'pass' });

  // ── Binder var-list ──
  if (binderDefs) {
    rules.push({ lhs: BVARS, rhs: [NT(BVARS), T('IDENT')], action: null, tag: 'varlist' });
    rules.push({ lhs: BVARS, rhs: [T('IDENT')], action: null, tag: 'varlist' });
  }

  // ── Binary operator levels ──
  for (const prec of precLevels) {
    const nt = precToNT.get(prec);
    const next = nextClosedAfterPrec(prec);
    const opsAtPrec = operators.filter(o => o.precedence === prec);
    // Determine associativity (use first op's assoc for the binder fall-through)
    const assoc = opsAtPrec.length > 0 ? opsAtPrec[0].assoc : 'left';

    if (binderDefs) {
      // BINDER_p: binder-or-expression at this level
      const bnt = precToBNT.get(prec);
      addBinderRules(bnt);
      // Fall-through: right-assoc → same level L_p (for chaining), left-assoc → L_{p+1}
      const binderFallThrough = assoc === 'right' ? nt : next;
      rules.push({ lhs: bnt, rhs: [NT(binderFallThrough)], action: c => c[0], tag: 'pass' });

      // Binary rules: RHS is BINDER_p
      for (const op of opsAtPrec) {
        if (op.assoc === 'right') {
          if (hasForward && op.name === 'loli') {
            rules.push({
              lhs: nt, rhs: [NT(next), T(op.op), T('{'), NT(START), T('}')],
              action: c => Store.put('loli', [c[0], Store.put('monad', [c[3]])]),
              tag: 'loli_monad',
            });
          }
          rules.push({
            lhs: nt, rhs: [NT(next), T(op.op), NT(bnt)],
            action: c => Store.put(op.name, [c[0], c[2]]), tag: 'binary',
          });
        } else {
          rules.push({
            lhs: nt, rhs: [NT(nt), T(op.op), NT(bnt)],
            action: c => Store.put(op.name, [c[0], c[2]]), tag: 'binary',
          });
        }
      }
    } else {
      // No binders: standard stratified grammar
      for (const op of opsAtPrec) {
        if (op.assoc === 'right') {
          if (hasForward && op.name === 'loli') {
            rules.push({
              lhs: nt, rhs: [NT(next), T(op.op), T('{'), NT(START), T('}')],
              action: c => Store.put('loli', [c[0], Store.put('monad', [c[3]])]),
              tag: 'loli_monad',
            });
          }
          rules.push({
            lhs: nt, rhs: [NT(next), T(op.op), NT(nt)],
            action: c => Store.put(op.name, [c[0], c[2]]), tag: 'binary',
          });
        } else {
          rules.push({
            lhs: nt, rhs: [NT(nt), T(op.op), NT(next)],
            action: c => Store.put(op.name, [c[0], c[2]]), tag: 'binary',
          });
        }
      }
    }

    // Fall-through to next tighter closed level
    rules.push({ lhs: nt, rhs: [NT(next)], action: c => c[0], tag: 'pass' });
  }

  // ── Unary prefix ──
  if (binderDefs) {
    // '!' applies to BINDER_UNARY (allows binder after !)
    for (const [op, info] of Object.entries(unaryPrefix)) {
      if (binderDefs[op] !== undefined) continue;
      rules.push({
        lhs: UNARY, rhs: [T(op), NT(BINDER_UNARY)],
        action: c => Store.put(info.name, [c[1]]), tag: 'unary',
      });
    }
    rules.push({ lhs: UNARY, rhs: [NT(unaryNext)], action: c => c[0], tag: 'pass' });
    // BINDER_UNARY: binder-or-unary
    addBinderRules(BINDER_UNARY);
    rules.push({ lhs: BINDER_UNARY, rhs: [NT(UNARY)], action: c => c[0], tag: 'pass' });
  } else {
    for (const [op, info] of Object.entries(unaryPrefix)) {
      rules.push({
        lhs: UNARY, rhs: [T(op), NT(UNARY)],
        action: c => Store.put(info.name, [c[1]]), tag: 'unary',
      });
    }
    rules.push({ lhs: UNARY, rhs: [NT(unaryNext)], action: c => c[0], tag: 'pass' });
  }

  // ── Application (left-recursive) ──
  if (hasApp) {
    rules.push({ lhs: APP, rhs: [NT(APP), NT(ATOM)], action: null, tag: 'app' });
    rules.push({ lhs: APP, rhs: [NT(ATOM)], action: c => c[0], tag: 'pass' });
  }

  // ── Atom ──
  rules.push({ lhs: ATOM, rhs: [T('('), NT(START), T(')')], action: c => c[1], tag: 'parens' });
  rules.push({
    lhs: ATOM, rhs: [T('{'), NT(START), T('}')],
    action: c => Store.put('monad', [c[1]]), tag: 'monad',
  });

  // Arrays — comma is a binary operator (from LNL family), so [A, B] = [comma(A, B)]
  rules.push({ lhs: ATOM, rhs: [T('['), T(']')], action: () => Store.putArray([]), tag: 'arr_empty' });
  rules.push({
    lhs: ATOM, rhs: [T('['), NT(START), T(']')],
    action: c => Store.putArray([c[1]]), tag: 'arr',
  });
  rules.push({
    lhs: ATOM, rhs: [T('['), NT(START), T('|'), NT(START), T(']')],
    action: c => Store.put('acons', [c[1], c[3]]), tag: 'arr_cons',
  });

  // Nullary constants
  for (const [lit, name] of Object.entries(nullary)) {
    rules.push({ lhs: ATOM, rhs: [T(lit)], action: () => Store.put(name, []), tag: 'nullary' });
  }

  // Numbers
  if (hasNumbers) {
    rules.push({ lhs: ATOM, rhs: [T('NUMBER')], action: null, tag: 'number' });
  }

  // Identifiers
  rules.push({ lhs: ATOM, rhs: [T('IDENT')], action: null, tag: 'ident' });

  // 'type' keyword
  if (hasArrows) {
    rules.push({ lhs: ATOM, rhs: [T('type')], action: () => Store.put('type', []), tag: 'nullary' });
  }

  // ── Lexer config ──
  const allOps = operators.map(o => o.op);
  for (const op of Object.keys(unaryPrefix)) {
    if (!allOps.includes(op) && !/^[a-z]/.test(op)) allOps.push(op);
  }
  allOps.push('|');
  allOps.sort((a, b) => b.length - a.length);

  const keywords = [];
  for (const [op, info] of Object.entries(unaryPrefix)) {
    if (info.keyword && !(binderDefs && binderDefs[op] !== undefined)) keywords.push(op);
  }
  if (binderDefs) for (const kw of Object.keys(binderDefs)) keywords.push(kw);
  for (const lit of Object.keys(nullary)) if (/^[a-zA-Z]/.test(lit)) keywords.push(lit);
  if (hasArrows) keywords.push('type');

  return {
    rules, start: START,
    lexerConfig: { operators: allOps, keywords, numbers: hasNumbers },
    hasBinders: !!binderDefs, hasApp, hasBinNorm, multiCharFV,
  };
}

// ─── Parser Factory ──────────────────────────────────────────────────────────

/**
 * Build parser from Earley grammar spec.
 * Returns parse(string) → Store hash, same interface as Pratt parser.
 */
function buildParserFromGrammar(spec) {
  const g = grammar(spec.rules, spec.start);
  const { lexerConfig, hasApp, hasBinNorm, multiCharFV } = spec;

  return function parse(input) {
    const tokens = tokenize(input.trim(), lexerConfig);
    const lazy = earleyParse(g, tokens, extractLazy);
    return evaluate(lazy, [], hasApp, hasBinNorm, multiCharFV);
  };
}

// ─── Tree Evaluation (binder-aware, top-down) ────────────────────────────────

function evaluate(node, binderStack, hasApp, hasBinNorm, multiCharFV) {
  if (!node.rule) return node; // terminal token

  const { rule, children } = node;
  const ev = c => evaluate(c, binderStack, hasApp, hasBinNorm, multiCharFV);

  // Binder: kw Vars '.' Body — push vars BEFORE evaluating body
  if (rule.binderTag) {
    const varNames = collectVarNames(children[1]);
    for (const v of varNames) binderStack.push(v);
    const body = ev(children[3]);
    binderStack.length -= varNames.length;
    let result = body;
    for (let i = varNames.length - 1; i >= 0; i--) {
      result = Store.put(rule.binderTag, [result]);
    }
    return result;
  }

  // Application: flatten left-recursive spine
  if (rule.tag === 'app') {
    const spine = [];
    flattenApp(node, spine, ev);
    const head = spine[0], args = spine.slice(1);

    if (hasBinNorm && args.length === 1) {
      const hn = Store.get(head);
      if (hn?.tag === 'atom' && (hn.children[0] === 'i' || hn.children[0] === 'o')) {
        const an = Store.get(args[0]);
        if (an?.tag === 'binlit') {
          return Store.put('binlit', [hn.children[0] === 'i'
            ? an.children[0] * 2n + 1n : an.children[0] * 2n]);
        }
      }
    }

    const hn = Store.get(head);
    if (hn?.tag === 'atom') return Store.put(hn.children[0], args);

    let result = head;
    for (const arg of args) result = Store.put('app', [result, arg]);
    return result;
  }

  // Identifier
  if (rule.tag === 'ident') {
    const name = children[0].value;
    if (hasBinNorm && name === 'e') return Store.put('binlit', [0n]);
    if (/[A-Z]/.test(name[0])) {
      for (let i = binderStack.length - 1; i >= 0; i--) {
        if (binderStack[i] === name) {
          return Store.put('bound', [BigInt(binderStack.length - 1 - i)]);
        }
      }
      if (multiCharFV) return Store.put('metavar', [name]);
      if (name.length === 1) return Store.put('freevar', [name]);
      return Store.put('atom', [name]);
    }
    return Store.put('atom', [name]);
  }

  // Number
  if (rule.tag === 'number') {
    const raw = children[0].value;
    if (raw.startsWith('0x') && raw.length - 2 > 64) {
      const hex = raw.slice(2);
      if (hex.length % 2 !== 0) throw new Error(`Parse error: odd-length hex literal '${raw}'`);
      const elems = new Uint32Array(hex.length / 2);
      for (let i = 0; i < elems.length; i++) {
        elems[i] = Store.put('binlit', [BigInt(parseInt(hex.slice(i * 2, i * 2 + 2), 16))]);
      }
      return Store.put('arrlit', [elems]);
    }
    return Store.put('binlit', [BigInt(raw)]);
  }

  // Rules with direct actions
  if (rule.action) return rule.action(children.map(ev));

  // Single-child passthrough
  if (children.length === 1) return ev(children[0]);

  return children.map(ev);
}

function flattenApp(node, spine, ev) {
  if (node.rule?.tag === 'app') {
    flattenApp(node.children[0], spine, ev);
    spine.push(ev(node.children[1]));
  } else {
    spine.push(ev(node));
  }
}

function collectVarNames(node) {
  if (!node.rule) return [node.value];
  if (node.children.length === 1) return [node.children[0].value];
  return [...collectVarNames(node.children[0]), node.children[1].value];
}

module.exports = { computeEarleyGrammar, buildParserFromGrammar };
