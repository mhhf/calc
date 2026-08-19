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

import Store from '../kernel/store.js';
import { grade0, gradeW, monadUnit } from '../engine/grades.js';
import { putRat } from '../kernel/rat-term.js';
import { T, NT, grammar, tokenize, earleyParse, sortOperators } from './earley.js';
// ─── Table Extraction ───────────────────────────────────────────────────────

/**
 * Extract parser tables from constructor annotations (pure data, serializable).
 * THE one classifier — builders.parserTables delegates here (TODO_0265 Phase 3:
 * previously duplicated between builders.js and earleyGrammar).
 *
 * Classification, in order:
 *   circumfix    — "OPEN hole CLOSE" ascii (e.g. "{ _ }", "{ #2 }"); hole is
 *                  `_` or `#N`. Supported layouts: arity 1 with the hole as
 *                  the only child, or arity 2 with hole #2 and the grade
 *                  child (#1) elided — filled by tables.gradeUnit at parse.
 *   gradedPrefix — category 'exponential', arity 2, ascii "OP #2" (grade
 *                  elided): bang. Grammar emits OP / OP_0 / OP_ω rules.
 *   nullary / unaryPrefix / binary operator — as before.
 *   template     — any remaining #N-hole @ascii (TODO_0268 item A): a
 *                  sorted mixfix template, classified by _parseTemplate.
 *
 * @param {Object} constructors - Constructor definitions with annotations
 * @returns {{ operators, nullary, unaryPrefix, circumfix, gradedPrefix, templates }}
 */
function extractParserTables(constructors) {
  const operators = [];
  const nullary = {};
  const unaryPrefix = {};
  const circumfix = [];
  const templates = [];
  let gradedPrefix = null;

  for (const [name, constr] of Object.entries(constructors)) {
    const ann = constr.annotations;
    if (!ann || !ann.ascii) continue;
    const ascii = ann.ascii;
    const arity = constr.argTypes.length;
    const prec = ann.prec;
    const precedence = typeof prec === 'object' ? prec.precedence : (prec || 100);
    const assoc = typeof prec === 'object' ? prec.associativity : 'left';

    const cfx = ascii.match(/^([^\s_#]+)\s+(_|#(\d+))\s+([^\s_#]+)$/);
    if (cfx) {
      if ((arity === 1 && (cfx[2] === '_' || cfx[3] === '1')) ||
          (arity === 2 && cfx[3] === '2')) {
        const dup = circumfix.find(c => c.open === cfx[1] && c.close === cfx[4]);
        if (dup) {
          throw new Error(`Circumfix collision: '${cfx[1]} ... ${cfx[4]}' claimed by both '${dup.name}' and '${name}' — parse would be declaration-order-dependent`);
        }
        circumfix.push({ open: cfx[1], close: cfx[4], name, arity });
        continue;
      }
      // Looks circumfix but has an unsupported hole layout (e.g. arity-2
      // with body-first "{ #1 }") — warn instead of silently dropping.
      console.warn(`extractParserTables: '${name}' @ascii "${ascii}" looks circumfix but has an unsupported hole layout (supported: arity 1 hole _/#1, arity 2 hole #2 with elided grade) — no grammar rule emitted`);
      continue;
    }

    if (ann.category === 'exponential' && arity === 2) {
      const gp = ascii.match(/^(\S+)\s+#2$/);
      if (gp) {
        if (gradedPrefix) {
          throw new Error(`Graded-prefix collision: '${gradedPrefix.op}' (${gradedPrefix.name}) and '${gp[1]}' (${name}) — one graded prefix per calculus`);
        }
        gradedPrefix = { op: gp[1], name };
        continue;
      }
    }

    if (arity === 0) {
      nullary[ascii] = name;
    } else if (arity === 1 &&
               (ascii.startsWith('!') ||
                ascii.match(/^[!@#$%^&*]+\s*_$/) ||
                ascii.match(/^\w+\s+_$/))) {
      const op = ascii.replace(/\s*_\s*$/, '').trim();
      unaryPrefix[op] = { name, precedence, keyword: /^[a-z]/.test(op) };
    } else if (arity === 2 && ascii.includes('_')) {
      const op = ascii.replace(/_/g, '').trim();
      operators.push({ name, op, precedence, assoc });
    } else if (ascii.includes('#')) {
      templates.push(_parseTemplate(name, ascii, constr, precedence, assoc));
    }
  }

  operators.sort((a, b) => a.precedence - b.precedence);

  return { operators, nullary, unaryPrefix, circumfix, gradedPrefix, templates };
}

/**
 * Parse a sorted mixfix @ascii template (TODO_0268 item A) — the general
 * form behind the timed surface (at/after/before/read) and woplus.
 *
 * A template is a sequence of literal tokens and #N holes; hole #N is
 * sorted by the constructor's argTypes[N-1]. Classification follows the
 * mixfix discipline (Danielsson–Norell): only the positions of holes whose
 * sort equals the RETURN sort matter —
 *   none                    → 'closed'   (ATOM-level production)
 *   one, at the right edge  → 'prefix'   (UNARY level)
 *   one, at the left edge   → 'postfix'  (tight postfix level, e.g. `A@t`)
 *   two, at both edges      → 'infix'    (precedence-chain level)
 * Cross-sort holes (e.g. the grade in `#1@#2` / `#2 +[#1] #3`) target the
 * auxiliary sort's own nonterminal. Every argument must have a hole —
 * elision is only supported by the circumfix/gradedPrefix families.
 *
 * Output is pure data (bundle-serializable).
 */
function _parseTemplate(name, ascii, constr, precedence, assoc) {
  const argSorts = constr.argTypes;
  const returnSort = constr.returnType;
  const pieces = [];
  for (const chunk of ascii.trim().split(/\s+/)) {
    let rest = chunk;
    while (rest.length > 0) {
      const m = rest.match(/^#(\d+)/);
      if (m) {
        pieces.push({ hole: parseInt(m[1], 10) - 1 });
        rest = rest.slice(m[0].length);
      } else {
        const lit = rest.match(/^[^#]+/)[0];
        pieces.push({ lit });
        rest = rest.slice(lit.length);
      }
    }
  }
  const seen = new Set();
  for (const p of pieces) {
    if (p.hole === undefined) continue;
    if (p.hole < 0 || p.hole >= argSorts.length || seen.has(p.hole)) {
      throw new Error(`'${name}' @ascii "${ascii}": hole #${p.hole + 1} is out of range or duplicated`);
    }
    seen.add(p.hole);
    p.sort = argSorts[p.hole];
  }
  if (seen.size !== argSorts.length) {
    throw new Error(`'${name}' @ascii "${ascii}": every argument needs a hole (elision is only supported for circumfix/graded-prefix forms)`);
  }
  const first = pieces[0], last = pieces[pieces.length - 1];
  const sameCount = pieces.filter(p => p.hole !== undefined && p.sort === returnSort).length;
  const leftEdge = first.hole !== undefined && first.sort === returnSort;
  const rightEdge = last.hole !== undefined && last.sort === returnSort;
  let kind;
  if (sameCount === 0) kind = 'closed';
  else if (sameCount === 1 && rightEdge) kind = 'prefix';
  else if (sameCount === 1 && leftEdge) kind = 'postfix';
  else if (sameCount === 2 && leftEdge && rightEdge) kind = 'infix';
  else {
    throw new Error(`'${name}' @ascii "${ascii}": unsupported mixfix shape — same-sort holes must sit at the template edges`);
  }
  return { name, ascii, pieces, kind, precedence, assoc, returnSort, arity: argSorts.length };
}

// ─── Grammar Generation ─────────────────────────────────────────────────────

/**
 * Generate Earley grammar from constructor annotations.
 *
 * @param {Object} constructors - Constructor definitions with annotations
 * @param {Object} opts - Opt-in features (binders, application, arrows, etc.)
 * @returns {{ rules, start, lexerConfig, hasBinders, hasApp, hasBinNorm, multiCharFV }}
 */
function earleyGrammar(constructors, opts = {}) {
  return _buildGrammar({ ...extractParserTables(constructors), ...opts });
}

/**
 * Generate Earley grammar from pre-extracted parser tables.
 * Same input shape as parserFromTables in builders.js.
 *
 * @param {Object} tables - { operators, nullary, unaryPrefix, binders?, arrows?, ... }
 * @returns {{ rules, start, lexerConfig, hasBinders, hasApp, hasBinNorm, multiCharFV }}
 */
function earleyGrammarFromTables(tables) {
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

  // Sorted mixfix templates (TODO_0268 item A): the declaration-derived
  // successor of the former `timedAnnotations` flag. A calculus parses
  // `A@t` / `after E` / `A +[Q] B` because it DECLARES those templates —
  // same mechanism that killed the phantom-monad wart in Phase 3.
  const templates = tables.templates || [];
  // Auxiliary sort (v1 fence): template holes may reference AT MOST one
  // sort besides the template's return sort; it gets the literal/expression
  // chain historically called GRADE (numerals lex exactly — D3). A second
  // auxiliary sort needs per-sort chains (rides with TODO_0011 sorts).
  const auxSorts = new Set();
  for (const t of templates) {
    for (const p of t.pieces) {
      if (p.hole !== undefined && p.sort !== t.returnSort) auxSorts.add(p.sort);
    }
  }
  if (auxSorts.size > 1) {
    throw new Error(`sorted templates reference auxiliary sorts {${[...auxSorts].join(', ')}} — only one auxiliary (grade) sort is supported (TODO_0011)`);
  }
  const hasAux = auxSorts.size === 1;
  const postfixTs = templates.filter(t => t.kind === 'postfix');
  const infixTs = templates.filter(t => t.kind === 'infix');
  const prefixTs = templates.filter(t => t.kind === 'prefix');
  const closedTs = templates.filter(t => t.kind === 'closed');
  // `at` is a KERNEL wrapper (like $/preserved): declaring it opts into the
  // surface; its stamp/grade pun (`{B}@d` regrades the computation) stays
  // kernel-owned — see the postfix action below.
  const hasAt = templates.some(t => t.name === 'at');

  // Declaration-derived graded/bracket connectives (TODO_0265 Phase 3):
  // circumfix entries drive the `{ ... }` ATOM rules, gradedPrefix drives
  // the `!`/`!_0`/`!_ω` rules. Calculi that declare neither parse neither —
  // the pre-Phase-3 hardcodes gave every calculus phantom monad/bang nodes.
  // An arity-2 circumfix (graded computation, grade child elided) needs
  // tables.gradeUnit — an in-process () => hash hook supplying the unit
  // grade for bare `{B}`; without it, `{ ... }` throws loudly.
  const circumfixes = tables.circumfix || [];
  const gradedPrefix = tables.gradedPrefix || null;
  // Elided-grade default: binlit 0, the canonical Q-zero (D6 merge-back —
  // ILL's `{B}` and till's zero-delay `{B}` are the same hash). A calculus
  // with a different grade algebra overrides via tables.gradeUnit, the
  // same precedent as bang's g0/gw parser-level grade atoms.
  const compGradeUnit = tables.gradeUnit || monadUnit;
  // The graded circumfix connective, if any — `{B}@d` rebuilds its grade.
  const gradedCircumfix = circumfixes.find(c => c.arity === 2) || null;

  if (hasArrows && !operators.some(o => o.name === 'arrow')) {
    operators.push({ name: 'arrow', op: '->', precedence: 40, assoc: 'right' });
  }
  if (hasForward && !operators.some(o => o.name === 'loli')) {
    operators.push({ name: 'loli', op: '-o', precedence: 50, assoc: 'right' });
  }
  operators.sort((a, b) => a.precedence - b.precedence);

  // ── Nonterminal allocation ──
  const precLevels = [...new Set([
    ...operators.map(o => o.precedence),
    ...infixTs.map(t => t.precedence),
  ])].sort((a, b) => a - b);
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
  const POSTFIX = postfixTs.length > 0 ? ntId++ : -1;
  const APP = hasApp ? ntId++ : -1;
  const ATOM = ntId++;
  const BVARS = binderDefs ? ntId++ : -1;
  const GRADE = hasAux ? ntId++ : -1;
  const GEXPR = hasAux ? ntId++ : -1;
  const GTERM = hasAux ? ntId++ : -1;

  // Chain helpers. The POSTFIX level (e.g. `A@t`, TODO_0265 Phase 3 /
  // TODO_0268 item A) sits between UNARY and APP/ATOM — postfix templates
  // bind tighter than every operator, like all prefix ops share UNARY.
  const LOOSEST = precLevels.length > 0 ? precToNT.get(precLevels[0]) : UNARY;
  const appNext = hasApp ? APP : ATOM;
  const unaryNext = POSTFIX >= 0 ? POSTFIX : appNext;

  function nextClosedAfterPrec(prec) {
    const idx = precLevels.indexOf(prec);
    return idx === precLevels.length - 1 ? UNARY : precToNT.get(precLevels[idx + 1]);
  }

  // ── Build rules ──
  const rules = [];

  // ── Sorted-template emission (TODO_0268 item A) ──
  // Build RHS + argument-collecting action for a template. `edgeNTs` maps
  // an edge same-sort hole to its (stratified) nonterminal; cross-sort
  // holes always target the auxiliary GRADE nonterminal.
  function tmplRhs(t, leftNT, rightNT) {
    const rhs = [];
    const holeAt = [];              // parallel: rhs index → argIdx (or -1)
    t.pieces.forEach((p, i) => {
      if (p.lit !== undefined) {
        rhs.push(T(p.lit));
        holeAt.push(-1);
      } else if (p.sort !== t.returnSort) {
        rhs.push(NT(GRADE));
        holeAt.push(p.hole);
      } else {
        rhs.push(NT(i === 0 ? leftNT : rightNT));
        holeAt.push(p.hole);
      }
    });
    const mkArgs = (c) => {
      const args = new Array(t.arity);
      holeAt.forEach((argIdx, i) => { if (argIdx >= 0) args[argIdx] = c[i]; });
      return args;
    };
    return { rhs, mkArgs };
  }

  /** The `at` kernel pun (stamp on resources / grade on computations) plus
   *  its rejections — kernel-owned semantics for the declared surface. */
  function atAction(mkArgs) {
    return (c) => {
      const [h, g] = mkArgs(c);
      const tag = Store.tag(h);
      if (gradedCircumfix && tag === gradedCircumfix.name) {
        if (compGradeUnit && Store.child(h, 0) !== compGradeUnit()) {
          throw new Error("Parse error: double grade '{B}@d@e'");
        }
        return Store.put(tag, [g, Store.child(h, 1)]);
      }
      if (tag === 'at') throw new Error("Parse error: double stamp 'A@s@t'");
      if (circumfixes.some(cf => cf.name === tag)) {
        throw new Error(`Parse error: '@' on an ungraded computation '${tag}'`);
      }
      return Store.put('at', [h, g]);
    };
  }

  function tmplAction(t, mkArgs) {
    if (t.name === 'at') return atAction(mkArgs);
    return (c) => Store.put(t.name, mkArgs(c));
  }

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
    const tmplsAtPrec = infixTs.filter(t => t.precedence === prec);
    // Determine associativity (use first op's assoc for the binder fall-through)
    const assoc = opsAtPrec.length > 0 ? opsAtPrec[0].assoc
      : tmplsAtPrec.length > 0 ? tmplsAtPrec[0].assoc : 'left';

    // Binder NT setup (open nonterminal at this level)
    const bnt = binderDefs ? precToBNT.get(prec) : null;
    if (bnt) {
      addBinderRules(bnt);
      const binderFallThrough = assoc === 'right' ? nt : next;
      rules.push({ lhs: bnt, rhs: [NT(binderFallThrough)], action: c => c[0], tag: 'pass' });
    }

    for (const op of opsAtPrec) {
      // RHS target: binder NT if available, else closed level
      const rhsTarget = bnt || (op.assoc === 'right' ? nt : next);
      // (The former `A -o { B }` composite rule is gone: `{ B }` is a
      // first-class circumfix ATOM, so the ordinary binary rule covers it —
      // keeping both made the grammar ambiguous. TODO_0265 Phase 3.)
      const lhsFirst = op.assoc === 'right' ? next : nt;
      rules.push({
        lhs: nt, rhs: [NT(lhsFirst), T(op.op), NT(rhsTarget)],
        action: c => Store.put(op.name, [c[0], c[2]]), tag: 'binary',
      });
    }

    // Sorted infix templates at this level (e.g. woplus `#2 +[#1] #3`):
    // same stratification as binary ops, with the template's interior
    // literals/cross-sort holes between the two edge operands.
    for (const t of tmplsAtPrec) {
      const rhsTarget = bnt || (t.assoc === 'right' ? nt : next);
      const lhsFirst = t.assoc === 'right' ? next : nt;
      const { rhs, mkArgs } = tmplRhs(t, lhsFirst, rhsTarget);
      rules.push({ lhs: nt, rhs, action: tmplAction(t, mkArgs), tag: 'tmpl' });
    }

    // Fall-through to next tighter closed level
    rules.push({ lhs: nt, rhs: [NT(next)], action: c => c[0], tag: 'pass' });
  }

  // ── Unary prefix ──
  // Unary operand target: binder-open NT if available, else UNARY itself
  const unaryOperand = binderDefs ? BINDER_UNARY : UNARY;

  for (const [op, info] of Object.entries(unaryPrefix)) {
    if (binderDefs && binderDefs[op] !== undefined) continue;
    rules.push({
      lhs: UNARY, rhs: [T(op), NT(unaryOperand)],
      action: c => Store.put(info.name, [c[1]]), tag: 'unary',
    });
  }

  // Graded prefix modality (derived from @ascii "OP #2", category
  // 'exponential' — e.g. bang "! #2"): `OP A` = default grade ω,
  // `OP_0` / `OP_ω` explicit. The suffix set and the {0, ω} grade atoms
  // stay fixed here until .calc grows a grade annotation — Phase 4's
  // !_k / !_W count grades generalize this (TODO_0265 Phase 3 decision:
  // deriving suffixes/defaults from @ascii needs a .calc format extension,
  // not worth it for one connective family yet).
  // D15 (timed calculi): stamped persistents are rejected — `!A@t` parses
  // the `@` first, so the bang action sees an at() child and throws.
  if (gradedPrefix) {
    const { op, name } = gradedPrefix;
    const guard = hasAt
      ? (h) => {
          if (Store.tag(h) === 'at') {
            throw new Error(`Parse error: stamped persistents are not allowed — '${op}A@t' (D15)`);
          }
          return h;
        }
      : (h) => h;
    rules.push({
      lhs: UNARY, rhs: [T(op), NT(unaryOperand)],
      action: c => Store.put(name, [gradeW(), guard(c[1])]), tag: 'unary',
    });
    rules.push({
      lhs: UNARY, rhs: [T(op + '_0'), NT(unaryOperand)],
      action: c => Store.put(name, [grade0(), guard(c[1])]), tag: 'unary',
    });
    rules.push({
      lhs: UNARY, rhs: [T(op + '_ω'), NT(unaryOperand)],
      action: c => Store.put(name, [gradeW(), guard(c[1])]), tag: 'unary',
    });
    // Count grades `OP_k A` / `OP_W A` (D4, TODO_0265 Phase 4): a counted
    // LINEAR parcel — bang(binlit k, A) splits k off the matched cohort,
    // bang(metavar W, A) takes the whole cohort, binding W to its count at
    // firing time. Reuses GRADE for the count position (NUMBER → binlit,
    // IDENT → metavar/freevar). No D15 at-guard: counted parcels are linear,
    // so stamps are allowed (`!_2 wood@4`). `OP_0` / `OP_ω` stay reserved
    // literals (longest-match before `OP_`). ℚ parcels (fractional counts)
    // are post-v1 — a RATNUM count is a loud error, not a silent misparse.
    if (hasAux) {
      rules.push({
        lhs: UNARY, rhs: [T(op + '_'), NT(GRADE), NT(unaryOperand)],
        action: c => {
          const g = c[1];
          const gt = Store.tag(g);
          if (gt !== 'binlit' && gt !== 'metavar' && gt !== 'freevar') {
            throw new Error(gt === 'ratlit'
              ? `Parse error: fractional count grade '${op}_n/d' — ℚ parcels are post-v1 (D4)`
              : `Parse error: count grade must be a number or variable, got '${gt}'`);
          }
          return Store.put(name, [g, c[2]]);
        }, tag: 'unary',
      });
    }
  }

  // Preserved resource sugar ($prefix) for forward rules
  if (hasForward) {
    rules.push({
      lhs: UNARY, rhs: [T('$'), NT(unaryOperand)],
      action: c => Store.put('preserved', [c[1]]), tag: 'unary',
    });
  }

  // Sorted prefix templates (e.g. `read #1`, TODO_0268 item A): a keyword/
  // symbol head with the same-sort operand at the right edge — wrapper
  // nodes only; convert.js desugars/validates, compile.js strips into
  // rule metadata (same lifecycle as $-preserved).
  for (const t of prefixTs) {
    const { rhs, mkArgs } = tmplRhs(t, -1, unaryOperand);
    rules.push({ lhs: UNARY, rhs, action: tmplAction(t, mkArgs), tag: 'tmpl' });
  }

  rules.push({ lhs: UNARY, rhs: [NT(unaryNext)], action: c => c[0], tag: 'pass' });

  // BINDER_UNARY: binder-or-unary (only when binders exist)
  if (binderDefs) {
    addBinderRules(BINDER_UNARY);
    rules.push({ lhs: BINDER_UNARY, rhs: [NT(UNARY)], action: c => c[0], tag: 'pass' });
  }

  // ── Postfix level: sorted postfix templates (TODO_0265 Phase 3 / 0268 A) ──
  // e.g. `at` (@ascii "#1@#2"): `A@t` → at(A, t) availability stamp;
  // `{B}@d` (graded circumfix) → rebuild with grade d (replaces the elided
  // unit grade): duration effect — the at kernel pun (see atAction). All
  // postfix templates share one level between UNARY and APP, mirroring how
  // all prefix operators share UNARY. A left-assoc template is
  // left-recursive (so `A@s@t` reaches the action's loud double-stamp
  // error instead of a bare no-parse).
  if (POSTFIX >= 0) {
    for (const t of postfixTs) {
      const left = t.assoc === 'left' ? POSTFIX : appNext;
      const { rhs, mkArgs } = tmplRhs(t, left, -1);
      rules.push({ lhs: POSTFIX, rhs, action: tmplAction(t, mkArgs), tag: 'tmpl' });
    }
    rules.push({ lhs: POSTFIX, rhs: [NT(appNext)], action: c => c[0], tag: 'pass' });
  }

  if (hasAux) {
    // GRADE: exact rational literal, integer, variable, or parenthesized
    // grade expression. Literals go through putRat — canonical ℚ, never a
    // JS float (D3). Compound arithmetic only inside parens (GEXPR);
    // convert.js desugars it to !q-op goals (E7.1) — window args only.
    rules.push({ lhs: GRADE, rhs: [T('RATNUM')], action: c => _putRatToken(c[0].value), tag: 'grade_lit' });
    rules.push({ lhs: GRADE, rhs: [T('NUMBER')], action: c => putRat(BigInt(c[0].value), 1n), tag: 'grade_lit' });
    rules.push({ lhs: GRADE, rhs: [T('IDENT')], action: null, tag: 'ident' });
    rules.push({ lhs: GRADE, rhs: [T('('), NT(GEXPR), T(')')], action: c => c[1], tag: 'parens' });

    // GEXPR: left-associative rational arithmetic over grade terms.
    // Builds qexpr_* nodes — surface-only; convert.js desugars them to
    // persistent !qplus/!qsub/!qmul/!qdiv goals (windows) or rejects them
    // (any other grade position, v1).
    rules.push({
      lhs: GEXPR, rhs: [NT(GEXPR), T('+'), NT(GTERM)],
      action: c => Store.put('qexpr_add', [c[0], c[2]]), tag: 'gexpr',
    });
    rules.push({
      lhs: GEXPR, rhs: [NT(GEXPR), T('-'), NT(GTERM)],
      action: c => Store.put('qexpr_sub', [c[0], c[2]]), tag: 'gexpr',
    });
    rules.push({ lhs: GEXPR, rhs: [NT(GTERM)], action: c => c[0], tag: 'pass' });
    rules.push({
      lhs: GTERM, rhs: [NT(GTERM), T('*'), NT(GRADE)],
      action: c => Store.put('qexpr_mul', [c[0], c[2]]), tag: 'gexpr',
    });
    rules.push({
      lhs: GTERM, rhs: [NT(GTERM), T('/'), NT(GRADE)],
      action: c => Store.put('qexpr_div', [c[0], c[2]]), tag: 'gexpr',
    });
    rules.push({ lhs: GTERM, rhs: [NT(GRADE)], action: c => c[0], tag: 'pass' });
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
  // Circumfix forms, derived from @ascii declarations ("{ _ }", "{ #2 }").
  // Replaces the pre-multi-logic hardcoded `{ _ }` rule: only calculi that
  // DECLARE a bracket connective parse it (TODO_0265 Phase 3, root fix of
  // audit round 11's F1 phantom-monad wart).
  for (const cf of circumfixes) {
    const mk = cf.arity === 1
      ? (body) => Store.put(cf.name, [body])
      : (body) => {
          if (!compGradeUnit) {
            throw new Error(`graded computation '${cf.name}' requires tables.gradeUnit`);
          }
          return Store.put(cf.name, [compGradeUnit(), body]);
        };
    rules.push({
      lhs: ATOM, rhs: [T(cf.open), NT(START), T(cf.close)],
      action: c => mk(c[1]), tag: 'circumfix',
    });
  }

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

  // Sorted closed templates (e.g. `after #1` / `before #1`, TODO_0268 A):
  // no same-sort holes — an ATOM-level production (mixfix discipline:
  // closed operators live at the innermost level).
  for (const t of closedTs) {
    const { rhs, mkArgs } = tmplRhs(t, -1, -1);
    rules.push({ lhs: ATOM, rhs, action: tmplAction(t, mkArgs), tag: 'tmpl' });
  }

  // Nullary constants
  for (const [lit, name] of Object.entries(nullary)) {
    rules.push({ lhs: ATOM, rhs: [T(lit)], action: () => Store.put(name, []), tag: 'nullary' });
  }

  // Numbers
  if (hasNumbers) {
    rules.push({ lhs: ATOM, rhs: [T('NUMBER')], action: null, tag: 'number' });
  }
  // Rational literals as ordinary term arguments (graded calculi): a fact
  // `price 1/2` needs the exact literal outside grade positions too.
  if (hasAux) {
    rules.push({ lhs: ATOM, rhs: [T('RATNUM')], action: c => _putRatToken(c[0].value), tag: 'grade_lit' });
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
  // Graded-prefix tokens (derived: OP_ω, OP_0, OP_ — longest first).
  // OP_ drives the count-grade rules (`!_2 wood` / `!_W wood`, D4) under a
  // timed grammar; in an untimed graded grammar it stays RESERVED with no
  // rule — a LOUD parse error, not a silent bang(ω, _2(wood)) misparse.
  if (gradedPrefix) {
    for (const t of [gradedPrefix.op + '_ω', gradedPrefix.op + '_0', gradedPrefix.op + '_', gradedPrefix.op]) {
      if (!allOps.includes(t)) allOps.push(t);
    }
  }
  // Multi-char circumfix brackets need explicit operator tokens
  for (const cf of circumfixes) {
    if (cf.open.length > 1 && !allOps.includes(cf.open)) allOps.push(cf.open);
    if (cf.close.length > 1 && !allOps.includes(cf.close)) allOps.push(cf.close);
  }
  allOps.push('|');
  allOps.push(':');
  if (hasForward && !allOps.includes('$')) allOps.push('$');

  const keywords = [];
  for (const [op, info] of Object.entries(unaryPrefix)) {
    if (info.keyword && !(binderDefs && binderDefs[op] !== undefined)) keywords.push(op);
  }
  if (binderDefs) for (const kw of Object.keys(binderDefs)) keywords.push(kw);
  for (const lit of Object.keys(nullary)) if (/^[a-zA-Z]/.test(lit)) keywords.push(lit);
  if (hasArrows) keywords.push('type');

  // Template literals: word-like heads become keywords (`after`, `read`),
  // symbol pieces become operator tokens (`@`, `+[`) — all derived, no
  // per-feature keyword/operator lists.
  for (const t of templates) {
    for (const p of t.pieces) {
      if (p.lit === undefined) continue;
      if (/^[a-zA-Z]/.test(p.lit)) {
        if (!keywords.includes(p.lit)) keywords.push(p.lit);
      } else if (!allOps.includes(p.lit)) {
        allOps.push(p.lit);
      }
    }
  }
  allOps.sort((a, b) => b.length - a.length);

  return {
    rules, start: START,
    lexerConfig: { operators: allOps, keywords, numbers: hasNumbers || hasAux, rationals: hasAux },
    hasBinders: !!binderDefs, hasApp, hasBinNorm, multiCharFV,
  };
}

/** Parse a RATNUM token ("a/b" or "d.f") to a canonical rational hash.
 *  Digit-wise exact — a lexer that parseFloat'd would corrupt 0.1 (D3).
 *  Zero denominators are a parse error, not a leaked RangeError. */
function _putRatToken(raw) {
  const slash = raw.indexOf('/');
  if (slash >= 0) {
    const den = BigInt(raw.slice(slash + 1));
    if (den === 0n) {
      throw new Error(`Parse error: zero denominator in rational literal '${raw}'`);
    }
    return putRat(BigInt(raw.slice(0, slash)), den);
  }
  const dot = raw.indexOf('.');
  const frac = raw.slice(dot + 1);
  return putRat(BigInt(raw.slice(0, dot) + frac), 10n ** BigInt(frac.length));
}

// ─── Parser Factory ──────────────────────────────────────────────────────────

/**
 * Build parser from Earley grammar spec.
 * Returns parse(string) → Store hash.
 *
 * Three-tier fast path:
 *  1. Expression memo (text→hash cache, cleared on Store.clear())
 *  2. Single-token fast path (skip Earley for trivial expressions)
 *  3. Full Earley parse
 *
 * Memoization is safe because binderStack is always empty at parse() entry
 * (reset on each call) so identical text always produces identical hash.
 */
function parserFromGrammar(spec) {
  const g = grammar(spec.rules, spec.start);
  const { lexerConfig, hasApp, hasBinNorm, multiCharFV } = spec;
  const ctx = { binderStack: [], hasApp, hasBinNorm, multiCharFV };

  // Pre-sort operators and keywords once (avoid re-sorting per tokenize call)
  const fastConfig = {
    ...lexerConfig,
    _sortedOps: sortOperators(lexerConfig.operators || []),
    _kwSet: new Set(lexerConfig.keywords || []),
  };

  // Build nullary keyword → Store hash map for fast path
  const nullaryMap = new Map();
  for (const rule of spec.rules) {
    if (rule.tag === 'nullary' && rule.rhs.length === 1 && rule.rhs[0].sym === 0 && rule.action) {
      nullaryMap.set(rule.rhs[0].v, rule.action);
    }
  }

  // Expression memoization — cleared on Store.clear() AND Store.restore()
  // (text→hash mapping is invalid when Store content changes)
  const memo = new Map();
  Store.onReplace(() => memo.clear());

  return function parse(input) {
    const trimmed = input.trim();
    const cached = memo.get(trimmed);
    if (cached !== undefined) return cached;

    const tokens = tokenize(trimmed, fastConfig);

    // ── Fast path: single-token expressions (skip Earley) ──
    if (tokens.length === 1) {
      const tok = tokens[0];
      let result;
      if (tok.type === 'IDENT') {
        const name = tok.value;
        if (hasBinNorm && name === 'e') result = Store.put('binlit', [0n]);
        else if (name.charCodeAt(0) >= 65 && name.charCodeAt(0) <= 90) {
          // Uppercase
          if (multiCharFV) result = Store.put('metavar', [name]);
          else if (name.length === 1) result = Store.put('freevar', [name]);
          else result = Store.put('atom', [name]);
        } else {
          result = Store.put('atom', [name]);
        }
      } else if (tok.type === 'NUMBER') {
        result = _parseNumber(tok.value);
      } else {
        // Keyword — check nullary map
        const action = nullaryMap.get(tok.type);
        if (action) result = action([]);
      }
      if (result !== undefined) {
        memo.set(trimmed, result);
        return result;
      }
    }

    // ── Full Earley parse ──
    ctx.binderStack.length = 0;
    const result = earleyParse(g, tokens, (item, rules) =>
      _extract(item, rules, ctx));

    memo.set(trimmed, result);
    return result;
  };
}

// ─── Fused Extract + Evaluate ────────────────────────────────────────────────
//
// Single-pass: walks Earley back-pointers and produces Store hashes directly.
// No intermediate lazy tree allocation. Binder rules use deferred evaluation
// (extract Vars first for scope, then evaluate Body).
// App rules use a spine marker to accumulate arguments bottom-up.

/** Parse a number literal (decimal or hex >64 chars → arrlit of byte binlits). */
function _parseNumber(raw) {
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

const _APP_SPINE = Symbol('appSpine');

function _extract(item, rules, ctx) {
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
    const varNames = _varNames(varsBack.r, rules);
    // Push vars, evaluate body, pop
    for (const v of varNames) ctx.binderStack.push(v);
    const body = _extract(bodyItem, rules, ctx);
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
      children[i] = _extract(back.r, rules, ctx);
      cur = back.l;
    } else {
      // nullable
      children[i] = _extractNull(back.nt, rules);
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
    return _appFinalize(children[0], ctx);
  }

  // Binary operator: finalize any app spines in operands
  if (tag === 'binary') {
    for (let i = 0; i < children.length; i++) {
      children[i] = _appFinalize(children[i], ctx);
    }
    return rule.action(children);
  }

  // Sorted templates (`A@t`, `after E`, `A +[Q] B`, ...): finalize app
  // spines in every operand, then run the template's argument-collector.
  if (tag === 'tmpl') {
    for (let i = 0; i < children.length; i++) {
      children[i] = _appFinalize(children[i], ctx);
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
  if (tag === 'number') return _parseNumber(children[0].value);

  // Named argument: (IDENT ':' START) → named_arg(atom(name), exprHash)
  if (tag === 'named_arg') {
    const name = children[1].value;
    const expr = _appFinalize(children[3], ctx);
    return Store.put('named_arg', [Store.put('atom', [name]), expr]);
  }

  // Rules with direct actions (monad, parens, arr, arr_cons, arr_empty, nullary, unary)
  if (rule.action) return rule.action(children);

  // Single-child passthrough (fallback)
  if (children.length === 1) return children[0];
  return children;
}

/** Finalize app spine into Store hash. */
function _appFinalize(val, ctx) {
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
function _varNames(item, rules) {
  const rule = rules[item.ruleIdx];
  if (rule.rhs.length === 1) {
    // BVARS → IDENT
    return [item.back.tok.value];
  }
  // BVARS → BVARS IDENT
  const identTok = item.back.tok;
  const bvarsItem = item.back.l.back.r;
  return [..._varNames(bvarsItem, rules), identTok.value];
}

function _extractNull(ntId, rules) {
  for (const rule of rules) {
    if (rule.lhs === ntId && rule.rhs.length === 0) {
      return rule.action ? rule.action([]) : null;
    }
  }
  return null;
}

export { earleyGrammar, earleyGrammarFromTables, parserFromGrammar, extractParserTables };
export default { earleyGrammar, earleyGrammarFromTables, parserFromGrammar, extractParserTables };
