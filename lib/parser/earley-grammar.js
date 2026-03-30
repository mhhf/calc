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
const { T, NT, grammar, tokenize, earleyParse } = require('./earley');

// ─── Grammar Generation ─────────────────────────────────────────────────────

/**
 * Generate Earley grammar from constructor annotations.
 *
 * @param {Object} constructors - Constructor definitions with annotations
 * @param {Object} opts - Opt-in features (binders, application, arrows, etc.)
 * @returns {{ rules, start, lexerConfig, hasBinders, hasApp, hasBinNorm, multiCharFV }}
 */
function computeEarleyGrammar(constructors, opts = {}) {
  // Extract operators from constructor annotations
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

  return _buildGrammar({ operators, nullary, unaryPrefix, ...opts });
}

/**
 * Generate Earley grammar from pre-extracted parser tables.
 * Same input shape as buildParserFromTables in builders.js.
 *
 * @param {Object} tables - { operators, nullary, unaryPrefix, binders?, arrows?, ... }
 * @returns {{ rules, start, lexerConfig, hasBinders, hasApp, hasBinNorm, multiCharFV }}
 */
function computeEarleyGrammarFromTables(tables) {
  return _buildGrammar(tables);
}

/**
 * Core grammar builder from operator tables + feature flags.
 */
function _buildGrammar(tables) {
  const binderDefs = tables.binders || null;
  const hasApp = tables.application || false;
  const hasArrows = tables.arrows || false;
  const hasForward = tables.forwardRules || false;
  const hasNumbers = tables.numbers || false;
  const hasBinNorm = tables.binaryNormalization || false;
  const multiCharFV = tables.multiCharFreevars || false;

  const operators = (tables.operators || []).slice();
  const nullary = { ...tables.nullary };
  const unaryPrefix = { ...tables.unaryPrefix };

  if (hasArrows && !operators.some(o => o.name === 'arrow')) {
    operators.push({ name: 'arrow', op: '->', precedence: 40, assoc: 'right' });
  }
  if (hasForward && !operators.some(o => o.name === 'loli')) {
    operators.push({ name: 'loli', op: '-o', precedence: 50, assoc: 'right' });
  }
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
  // Named argument: (name: expr) — produces named_arg sentinel
  rules.push({ lhs: ATOM, rhs: [T('('), T('IDENT'), T(':'), NT(START), T(')')], action: null, tag: 'named_arg' });
  rules.push({
    lhs: ATOM, rhs: [T('{'), NT(START), T('}')],
    action: c => Store.put('monad', [c[1]]), tag: 'monad',
  });

  // Arrays
  const hasCommaOp = operators.some(o => o.op === ',');
  rules.push({ lhs: ATOM, rhs: [T('['), T(']')], action: () => Store.putArray([]), tag: 'arr_empty' });
  if (hasCommaOp) {
    // Comma is a binary operator (from LNL family): [A, B] = [comma(A, B)]
    rules.push({
      lhs: ATOM, rhs: [T('['), NT(START), T(']')],
      action: c => Store.putArray([c[1]]), tag: 'arr',
    });
    rules.push({
      lhs: ATOM, rhs: [T('['), NT(START), T('|'), NT(START), T(']')],
      action: c => Store.put('acons', [c[1], c[3]]), tag: 'arr_cons',
    });
  } else {
    // Explicit comma-separated array syntax
    const ARR_ELEMS = ntId++;
    rules.push({
      lhs: ATOM, rhs: [T('['), NT(ARR_ELEMS), T(']')],
      action: null, tag: 'arr_list',
    });
    // [elems | tail] → acons chain
    rules.push({
      lhs: ATOM, rhs: [T('['), NT(ARR_ELEMS), T('|'), NT(START), T(']')],
      action: null, tag: 'arr_cons_list',
    });
    rules.push({
      lhs: ARR_ELEMS, rhs: [NT(ARR_ELEMS), T(','), NT(START)],
      action: null, tag: 'arr_elem_cons',
    });
    rules.push({
      lhs: ARR_ELEMS, rhs: [NT(START)],
      action: null, tag: 'arr_elem_single',
    });
  }

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
  allOps.push(':');
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
 * Returns parse(string) → Store hash.
 */
function buildParserFromGrammar(spec) {
  const g = grammar(spec.rules, spec.start);
  const { lexerConfig, hasApp, hasBinNorm, multiCharFV } = spec;
  const ctx = { binderStack: [], hasApp, hasBinNorm, multiCharFV };

  return function parse(input) {
    const tokens = tokenize(input.trim(), lexerConfig);
    ctx.binderStack.length = 0;
    return earleyParse(g, tokens, (item, rules) =>
      _extractEval(item, rules, ctx));
  };
}

// ─── Fused Extract + Evaluate ────────────────────────────────────────────────
//
// Single-pass: walks Earley back-pointers and produces Store hashes directly.
// No intermediate lazy tree allocation. Binder rules use deferred evaluation
// (extract Vars first for scope, then evaluate Body).
// App rules use a spine marker to accumulate arguments bottom-up.

const _APP_SPINE = Symbol('appSpine');

function _extractEval(item, rules, ctx) {
  const rule = rules[item.ruleIdx];

  if (rule.rhs.length === 0) {
    return rule.action ? rule.action([]) : null;
  }

  // ── Binder: kw Vars '.' Body ──
  // Must extract Vars BEFORE evaluating Body (de Bruijn scope).
  // Walk back-pointers right→left: Body(3), '.'(2), Vars(1), kw(0).
  if (rule.binderTag) {
    let cur = item;
    // child[3]: Body (complete nonterminal)
    const bodyBack = cur.back;
    const bodyItem = bodyBack.r;
    cur = bodyBack.l;
    // child[2]: '.' (scanned terminal)
    cur = cur.back.l;
    // child[1]: Vars (complete nonterminal)
    const varsBack = cur.back;
    const varNames = _extractVarNames(varsBack.r, rules);
    // Push vars, evaluate body, pop
    for (const v of varNames) ctx.binderStack.push(v);
    const body = _extractEval(bodyItem, rules, ctx);
    ctx.binderStack.length -= varNames.length;
    let result = body;
    for (let i = varNames.length - 1; i >= 0; i--) {
      result = Store.put(rule.binderTag, [result]);
    }
    return result;
  }

  // ── General: extract children and evaluate ──
  const n = rule.rhs.length;
  const children = new Array(n);
  let cur = item;

  for (let i = n - 1; i >= 0; i--) {
    const back = cur.back;
    if (back.t === 's') {
      children[i] = back.tok;
      cur = back.l;
    } else if (back.t === 'c') {
      children[i] = _extractEval(back.r, rules, ctx);
      cur = back.l;
    } else {
      // nullable
      children[i] = _extractNullableEval(back.nt, rules);
      cur = back.l;
    }
  }

  return _evalRule(rule, children, ctx);
}

function _evalRule(rule, children, ctx) {
  const tag = rule.tag;

  // App spine: accumulate arguments (left-recursive APP → APP ATOM)
  if (tag === 'app') {
    const left = children[0], right = children[1];
    if (left && left[_APP_SPINE]) {
      left.args.push(right);
      return left;
    }
    return { [_APP_SPINE]: true, head: left, args: [right] };
  }

  // Pass-through: finalize app spine if needed
  if (tag === 'pass') {
    return _finalizeApp(children[0], ctx);
  }

  // Binary operator: finalize any app spines in operands
  if (tag === 'binary' || tag === 'loli_monad') {
    for (let i = 0; i < children.length; i++) {
      children[i] = _finalizeApp(children[i], ctx);
    }
    return rule.action(children);
  }

  // Array element accumulation (returns array, not Store hash)
  if (tag === 'arr_elem_single') return [children[0]];
  if (tag === 'arr_elem_cons') {
    children[0].push(children[2]);
    return children[0];
  }

  // Array with explicit comma separators
  if (tag === 'arr_list') return Store.putArray(children[1]);
  if (tag === 'arr_cons_list') {
    const elems = children[1];
    let result = children[3];
    for (let i = elems.length - 1; i >= 0; i--) {
      result = Store.put('acons', [elems[i], result]);
    }
    return result;
  }

  // Identifier
  if (tag === 'ident') {
    const name = children[0].value;
    if (ctx.hasBinNorm && name === 'e') return Store.put('binlit', [0n]);
    if (/[A-Z]/.test(name[0])) {
      const bs = ctx.binderStack;
      for (let i = bs.length - 1; i >= 0; i--) {
        if (bs[i] === name) return Store.put('bound', [BigInt(bs.length - 1 - i)]);
      }
      if (ctx.multiCharFV) return Store.put('metavar', [name]);
      if (name.length === 1) return Store.put('freevar', [name]);
      return Store.put('atom', [name]);
    }
    return Store.put('atom', [name]);
  }

  // Number
  if (tag === 'number') {
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

  // Named argument: (IDENT ':' START) → named_arg(atom(name), exprHash)
  if (tag === 'named_arg') {
    const name = children[1].value;
    const expr = _finalizeApp(children[3], ctx);
    return Store.put('named_arg', [Store.put('atom', [name]), expr]);
  }

  // Rules with direct actions (monad, parens, arr, arr_cons, arr_empty, nullary, unary)
  if (rule.action) return rule.action(children);

  // Single-child passthrough (fallback)
  if (children.length === 1) return children[0];
  return children;
}

/** Finalize app spine into Store hash. */
function _finalizeApp(val, ctx) {
  if (!val || !val[_APP_SPINE]) return val;
  const { head, args } = val;

  if (ctx.hasBinNorm && args.length === 1) {
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

/** Extract variable names from BVARS nonterminal. */
function _extractVarNames(item, rules) {
  const rule = rules[item.ruleIdx];
  if (rule.rhs.length === 1) {
    // BVARS → IDENT
    return [item.back.tok.value];
  }
  // BVARS → BVARS IDENT
  const identTok = item.back.tok;
  const bvarsItem = item.back.l.back.r;
  return [..._extractVarNames(bvarsItem, rules), identTok.value];
}

function _extractNullableEval(ntId, rules) {
  for (const rule of rules) {
    if (rule.lhs === ntId && rule.rhs.length === 0) {
      return rule.action ? rule.action([]) : null;
    }
  }
  return null;
}

module.exports = { computeEarleyGrammar, computeEarleyGrammarFromTables, buildParserFromGrammar };
