/**
 * .rules2 Parser
 *
 * Parses sequent-notation rule files directly into flat descriptors.
 *
 * Input:  sequent notation (e.g. "G ; D, A * B |- C")
 * Output: flat descriptor objects ({ connective, side, arity, contextSplit, ... })
 *
 * Two descriptor flavors (TODO_0265 Phase 6b Stage 1):
 *   index    — premises reference principal children by index (all of
 *              ill.rules; zero-allocation at apply time, Zig-portable)
 *   template — premises are formula PATTERNS instantiated by matching the
 *              principal (and, for left rules, the conclusion succedent)
 *              via one-way unification, with @grade side conditions
 *              evaluated through the calculus's grade-algebra record.
 *              Triggered by @grade / @template true / a compound premise
 *              formula — absent all three, descriptors are byte-identical
 *              to before (the D13 zero-delta gate).
 *
 * Template rules require a metavar-producing parser (multiCharFreevars):
 * pattern metavars bind against rigid sequent content; a freevar-mode
 * parser would make patterns rigid too, so it is rejected loudly.
 */

import Store from '../kernel/store.js';
import { balancedSplit as _rawSplit } from '../parser/balanced-split.js';
/** Split on separator, trim parts, drop empties (original local contract). */
function balancedSplit(str, sep) {
  return _rawSplit(str, sep).map(s => s.trim()).filter(Boolean);
}

/**
 * Parse a sequent string "cart ; linear |- succedent"
 * Returns { cartesian: string[], linear: string[], succedent: string }
 */
function parseSequent(line) {
  const [left, succedent] = _rawSplit(line, '|-').map(s => s.trim());
  const sides = left.split(';').map(s => s.trim());
  const cartStr = sides.length > 1 ? sides[0] : '';
  const linStr = sides.length > 1 ? sides[1] : sides[0];
  return {
    cartesian: cartStr ? balancedSplit(cartStr, ',') : [],
    linear: linStr ? balancedSplit(linStr, ',') : [],
    succedent: succedent.trim()
  };
}

/**
 * Check if a token is a context variable.
 * Primed vars (D', G) are always context vars.
 * Unprimed single uppercase: parse with formula parser — if freevar
 * and not in formulaVars, it's a context var.
 */
function _isCtxVar(token, formulaVars, parseFormula) {
  // Primed variables are always context vars
  if (/^[A-Z]'+$/.test(token)) return true;
  // Single uppercase: check via parser
  if (/^[A-Z]$/.test(token)) {
    if (formulaVars.has(token)) return false;
    const t = Store.tag(parseFormula(token));
    // freevar (default parser) or metavar (multiCharFreevars parser)
    return t === 'freevar' || t === 'metavar';
  }
  return false;
}

/** Rule variable: freevar (default parser) or metavar (multiCharFreevars). */
function _isRuleVar(tag) {
  return tag === 'freevar' || tag === 'metavar';
}

/** Collect rule-variable hashes occurring in a parsed formula. */
function _collectVars(h, out) {
  const tag = Store.tag(h);
  if (_isRuleVar(tag)) { out.add(h); return; }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) _collectVars(c, out);
  }
}

// @grade line forms — a definition (out := a op b) or a guard (a cmp b).
// Operands are rule variables or grade literals (parsed via grades.parseStamp).
const _GRADE_DEF_RE = /^([A-Za-z]\w*)\s*:=\s*(\w+(?:\/\d+)?)\s*([+\-])\s*(\w+(?:\/\d+)?)$/;
const _GRADE_GUARD_RE = /^(\w+(?:\/\d+)?)\s*(>=|<=|=|<|>)\s*(\w+(?:\/\d+)?)$/;

/**
 * Compile the template record for a template rule.
 * Patterns are Store hashes with metavars; steps evaluate in order through
 * the grade algebra at apply time (defs extend the binding, guards prune).
 * All variable-boundness checking happens HERE, at load time, loudly.
 */
function _compileTemplate({ name, principal, side, succHash, premiseSeqs,
                            gradeLines, parseFormula, formulaVars, grades }) {
  const bound = new Set();
  _collectVars(principal, bound);
  const succPattern = side === 'l' ? succHash : null;
  if (succPattern != null) _collectVars(succPattern, bound);
  for (const v of bound) {
    if (Store.tag(v) === 'freevar') {
      throw new Error(`rule '${name}': template rules require a metavar-producing parser (multiCharFreevars) — '${Store.child(v, 0)}' parsed as a freevar`);
    }
  }
  const byName = new Map([...bound].map(v => [Store.child(v, 0), v]));

  // Grade steps (defs bind new variables for later steps and premises)
  if (gradeLines.length && !grades) {
    throw new Error(`rule '${name}': @grade requires a grade algebra — pass opts.grades to the loader`);
  }
  const operand = (tok) => {
    if (/^[A-Za-z]/.test(tok)) {
      const v = byName.get(tok);
      if (!v) throw new Error(`rule '${name}': @grade references unbound variable '${tok}'`);
      return { v };
    }
    return { g: grades.parseStamp(tok) };
  };
  const steps = gradeLines.map(line => {
    let m;
    if ((m = line.match(_GRADE_DEF_RE))) {
      const step = { kind: 'def', a: operand(m[2]), op: m[3], b: operand(m[4]) };
      if (byName.has(m[1])) throw new Error(`rule '${name}': @grade '${m[1]}' is already bound`);
      const out = Store.put('metavar', [m[1]]);
      byName.set(m[1], out);
      bound.add(out);
      step.out = out;
      return step;
    }
    if ((m = line.match(_GRADE_GUARD_RE))) {
      return { kind: 'guard', a: operand(m[1]), op: m[2], b: operand(m[3]) };
    }
    throw new Error(`rule '${name}': malformed @grade line '${line}'`);
  });

  // Premise patterns — every variable must be bound by the conclusion or a def
  const pattern = (entry, zone) => {
    const h = parseFormula(entry);
    const vars = new Set();
    _collectVars(h, vars);
    for (const v of vars) {
      if (!bound.has(v)) {
        throw new Error(`rule '${name}': ${zone} premise variable '${Store.child(v, 0)}' is unbound (not in the conclusion or a @grade def)`);
      }
    }
    return h;
  };
  const premises = premiseSeqs.map(p => ({
    linear: p.linear.filter(e => !_isCtxVar(e, formulaVars, parseFormula))
      .map(e => pattern(e, 'linear')),
    cartesian: p.cartesian.filter(e => !_isCtxVar(e, formulaVars, parseFormula))
      .map(e => pattern(e, 'cartesian')),
    succedent: pattern(p.succedent, 'succedent'),
  }));

  return { principal, succedent: succPattern, steps, premises };
}

/**
 * Parse a rule block and extract descriptor + metadata.
 */
function _ruleBlock(block, parseFormula, formulaVars, opts = {}) {
  const lines = block.split('\n').map(l => l.trim()).filter(l => l && !l.startsWith('%'));

  // First line: "name: sequent" or just "name: annotations..."
  const firstLine = lines[0];
  const colonIdx = firstLine.indexOf(':');
  const name = firstLine.slice(0, colonIdx).trim();
  const rest = firstLine.slice(colonIdx + 1).trim();

  // Collect premise lines and annotation lines
  const premises = [];
  const annotations = {};
  let conclusionStr = rest;

  for (let i = 1; i < lines.length; i++) {
    const line = lines[i];
    if (line.startsWith('<-')) {
      premises.push(line.slice(2).trim());
    } else if (line.startsWith('@')) {
      const match = line.match(/^@(\w+)\s+(.*)/);
      if (match) {
        let val = match[2].replace(/\.$/, '').trim();
        if (val === 'true') val = true;
        else if (val === 'false') val = false;
        else if (val.startsWith('"') && val.endsWith('"')) val = val.slice(1, -1);
        // @grade lines accumulate (a rule may carry several side conditions)
        if (match[1] === 'grade') (annotations.grade ||= []).push(val);
        else annotations[match[1]] = val;
      }
    }
  }

  // Remove trailing period from conclusion
  conclusionStr = conclusionStr.replace(/\.$/, '').trim();

  // Parse sequents
  const conclusion = parseSequent(conclusionStr);
  const premiseSeqs = premises.map(parseSequent);

  // Identify formula entries vs context vars in conclusion
  const concLinFormulas = [];
  const concLinContextVars = [];
  for (const entry of conclusion.linear) {
    if (_isCtxVar(entry, formulaVars, parseFormula)) concLinContextVars.push(entry);
    else concLinFormulas.push(entry);
  }

  const concCartFormulas = [];
  const concCartContextVars = [];
  for (const entry of conclusion.cartesian) {
    if (_isCtxVar(entry, formulaVars, parseFormula)) concCartContextVars.push(entry);
    else concCartFormulas.push(entry);
  }

  // Find principal formula
  let principal = null;
  let side = null;

  // Check succedent: parse it, if compound (not a rule var/atom) → principal
  // on right. @side l overrides (a left rule whose succedent is ALSO
  // compound, e.g. monad_l's sticky monadic succedent pattern).
  const succHash = parseFormula(conclusion.succedent);
  const succTag = Store.tag(succHash);
  if (annotations.side !== 'l' && !_isRuleVar(succTag) && succTag !== 'atom') {
    principal = succHash;
    side = 'r';
  }

  // Check linear context for principal (compound formula)
  if (!principal) {
    for (const entry of concLinFormulas) {
      const h = parseFormula(entry);
      const t = Store.tag(h);
      if (!_isRuleVar(t) && t !== 'atom') {
        principal = h;
        side = 'l';
        break;
      }
    }
  }

  // Extract connective info
  let connective = null;
  let arity = 0;
  let childMap = {}; // freevar name → child index

  if (principal) {
    connective = Store.tag(principal);
    const children = Store.children(principal);
    arity = children.length;
    for (let i = 0; i < children.length; i++) {
      const c = children[i];
      if (Store.isTermChild(c) && _isRuleVar(Store.tag(c))) {
        childMap[Store.child(c, 0)] = i;
      }
    }
  }

  // Context flow
  const emptyLinear = conclusion.linear.length === 0;
  let contextFlow;
  if (emptyLinear) {
    contextFlow = 'empty';
  } else if (premiseSeqs.length === 0) {
    contextFlow = 'axiom';
  } else if (premiseSeqs.length === 1) {
    contextFlow = 'preserved';
  } else {
    // Check if all conclusion context vars appear in all premises
    const allCopied = concLinContextVars.every(v =>
      premiseSeqs.every(p => p.linear.includes(v) || p.cartesian.includes(v))
    );
    contextFlow = allCopied ? 'copy' : 'split';
  }

  const copyContext = contextFlow === 'copy';
  const contextSplit = contextFlow === 'split';
  const structural = annotations.structural === true;

  // Build premise descriptors (only when principal exists)
  if (!principal) {
    if (annotations.grade || annotations.template) {
      throw new Error(`rule '${name}': @grade/@template requires a principal formula`);
    }
    const descriptor = {
      connective, side, arity,
      copyContext, emptyLinear, contextSplit, contextFlow,
      premises: []
    };
    return {
      name, descriptor,
      invertible: annotations.invertible ?? null,
      pretty: annotations.pretty || name,
      structural,
      bridge: annotations.bridge || null,
      numPremises: premiseSeqs.length
    };
  }

  // Template detection (D1): @grade side conditions, an explicit
  // @template true (ω rules whose grade restriction lives in the pattern),
  // or a compound premise formula (inexpressible as a child index).
  const gradeLines = annotations.grade || [];
  const isTemplate = gradeLines.length > 0 || annotations.template === true ||
    premiseSeqs.some(p => [...p.linear, ...p.cartesian].some(e => {
      if (_isCtxVar(e, formulaVars, parseFormula)) return false;
      const t = Store.tag(parseFormula(e));
      return !_isRuleVar(t) && t !== 'atom';
    }));

  let descriptor;
  if (isTemplate) {
    if (side === 'l' && concLinFormulas.length !== 1) {
      throw new Error(`rule '${name}': a template rule needs exactly one principal formula in the conclusion (got ${concLinFormulas.length})`);
    }
    if (concCartFormulas.length > 0) {
      throw new Error(`rule '${name}': template rules do not support cartesian conclusion formulas`);
    }
    descriptor = {
      connective, side, arity,
      copyContext, emptyLinear, contextSplit, contextFlow,
      premises: [],
      template: _compileTemplate({
        name, principal, side, succHash, premiseSeqs,
        gradeLines, parseFormula, formulaVars, grades: opts.grades,
      }),
    };
  } else {
    const premiseDescs = premiseSeqs.map(p => {
      const desc = {};

      // Find new formula vars in linear (not in conclusion linear)
      const newLinFormulas = [];
      for (const entry of p.linear) {
        if (!_isCtxVar(entry, formulaVars, parseFormula) && !concLinFormulas.includes(entry)) {
          const h = parseFormula(entry);
          // Get the rule-var name(s) from this formula
          if (_isRuleVar(Store.tag(h))) {
            const varName = Store.child(h, 0);
            if (childMap[varName] != null) newLinFormulas.push(childMap[varName]);
          }
        }
      }
      if (newLinFormulas.length > 0) desc.linear = newLinFormulas;

      // Find new formula vars in cartesian
      const newCartFormulas = [];
      for (const entry of p.cartesian) {
        if (!_isCtxVar(entry, formulaVars, parseFormula) && !concCartFormulas.includes(entry)) {
          const h = parseFormula(entry);
          if (_isRuleVar(Store.tag(h))) {
            const varName = Store.child(h, 0);
            if (childMap[varName] != null) newCartFormulas.push(childMap[varName]);
          }
        }
      }
      if (newCartFormulas.length > 0) desc.cartesian = newCartFormulas;

      // Check succedent change
      const premSuccHash = parseFormula(p.succedent);
      if (premSuccHash !== succHash) {
        if (_isRuleVar(Store.tag(premSuccHash))) {
          const varName = Store.child(premSuccHash, 0);
          if (childMap[varName] != null) desc.succedent = childMap[varName];
        }
      }

      return desc;
    });

    descriptor = {
      connective,
      side,
      arity,
      copyContext,
      emptyLinear,
      contextSplit,
      contextFlow,
      premises: premiseDescs
    };
  }
  if (annotations.binding) descriptor.binding = annotations.binding;
  // @modeShift true — the rule is a bridge point (backward ↔ engine):
  // premise computation is bypassed, bridge.modeSwitch handles it.
  if (annotations.modeShift === true) descriptor.modeShift = true;

  return {
    name,
    descriptor,
    invertible: annotations.invertible ?? null,
    pretty: annotations.pretty || name,
    structural,
    bridge: annotations.bridge || null,
    numPremises: premiseSeqs.length
  };
}

/**
 * Parse a .rules2 file.
 * @param {string} text - File contents
 * @param {function} parseFormula - Formula parser (from buildParser)
 * @param {Object} [opts] - { grades } — grade-algebra record for @grade
 *   side conditions (template rules); ILL-style files never need it
 * @returns {Object} rules map { name → rule }
 */
function parseRules2(text, parseFormula, opts = {}) {
  // Extract @formulas directive
  const formulaMatch = text.match(/@formulas\s+([A-Z](?:\s*,\s*[A-Z])*)/);
  if (!formulaMatch) throw new Error('@formulas directive required');
  const formulaVars = new Set(formulaMatch[1].split(',').map(s => s.trim()));

  // Remove @formulas line and full-line comments, split into rule blocks
  // on '.' — comments are dropped BEFORE block splitting, so a section
  // header directly above a rule can never swallow the rule (a block whose
  // first line was a comment used to be skipped wholesale).
  const body = text.replace(/@formulas[^\n]*\n/, '')
    .split('\n').filter(l => !l.trim().startsWith('%')).join('\n');
  const blocks = body.split(/\.\s*\n/).filter(b => b.trim());

  const rules = {};
  for (const block of blocks) {
    const trimmed = block.trim();
    if (!trimmed) continue;
    const rule = _ruleBlock(trimmed, parseFormula, formulaVars, opts);
    rules[rule.name] = rule;
  }

  return rules;
}

export { parseRules2 };
export default { parseRules2 };
