/**
 * Earley parser — core recognizer + tree extraction.
 *
 * Generic, grammar-agnostic. Takes CFG rules with semantic actions,
 * produces values via bottom-up action evaluation.
 *
 * Complexity: O(n³) general, O(n²) unambiguous.
 * No Leo optimization — right-recursive grammars are O(n²), not O(n).
 * Item packing: key = (ruleIdx * 256 + dot) * (n+1) + origin.
 * Safe up to ~2^37 tokens (JS 53-bit safe integers / 65536 rules / 256 dot).
 *
 * References:
 *   Earley (1970) "An Efficient Context-Free Parsing Algorithm"
 *   Aycock & Horspool (2002) "Practical Earley Parsing" (nullable handling)
 */

'use strict';

// ─── Symbols ─────────────────────────────────────────────────────────────────

/** Terminal symbol — matches a token type string. */
function T(type) { return { sym: 0, v: type }; }

/** Nonterminal symbol — references a nonterminal by integer ID. */
function NT(id) { return { sym: 1, v: id }; }

// ─── Grammar ─────────────────────────────────────────────────────────────────

/**
 * Build optimized grammar from rule list.
 *
 * @param {{ lhs: number, rhs: Symbol[], action?: Function }[]} rules
 * @param {number} start - Start nonterminal ID
 * @returns {{ rules, start, nullable: Set<number>, byLhs: Map<number, number[]> }}
 */
function grammar(rules, start) {
  // Nullable nonterminals (fixed-point, Aycock-Horspool)
  const nullable = new Set();
  let changed = true;
  while (changed) {
    changed = false;
    for (const r of rules) {
      if (!nullable.has(r.lhs) &&
          r.rhs.every(s => s.sym === 1 && nullable.has(s.v))) {
        nullable.add(r.lhs);
        changed = true;
      }
    }
  }

  // Index: nonterminal → rule indices
  const byLhs = new Map();
  for (let i = 0; i < rules.length; i++) {
    const lhs = rules[i].lhs;
    if (!byLhs.has(lhs)) byLhs.set(lhs, []);
    byLhs.get(lhs).push(i);
  }

  return { rules, start, nullable, byLhs };
}

// ─── Lexer ───────────────────────────────────────────────────────────────────

// Character classification via charCode (faster than regex per char)
function _isWhitespace(c) {
  return c === 32 || c === 9 || c === 10 || c === 13; // space, tab, \n, \r
}
function _isDigit(c) {
  return c >= 48 && c <= 57; // 0-9
}
function _isHexDigit(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102);
}
function _isIdentStart(c) {
  return (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95 || c === 39; // A-Z a-z _ '
}
function _isIdentCont(c) {
  return _isIdentStart(c) || _isDigit(c);
}
function _isAlpha(c) {
  return (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}
function _isWordChar(c) {
  return _isAlpha(c) || _isDigit(c) || c === 95; // \w equiv
}

/**
 * Pre-sort operators for longest-match lexing.
 * Call once at grammar construction time, pass result as config._sortedOps.
 */
function sortOperators(operators) {
  return operators.slice().sort((a, b) => b.length - a.length);
}

/**
 * Tokenize input string.
 *
 * Token types:
 *   IDENT  — identifier ([A-Za-z_'][A-Za-z0-9_']*)
 *   NUMBER — numeric literal (decimal or 0xHex)
 *   <keyword> — keyword becomes its own token type
 *   <operator> — multi-char operator becomes its own token type
 *   single char — brackets, punctuation, single-char operators
 *
 * @param {string} input
 * @param {{ operators?: string[], keywords?: string[], numbers?: boolean, _sortedOps?: string[], _kwSet?: Set }} config
 * @returns {{ type: string, value: string, pos: number }[]}
 */
function tokenize(input, config = {}) {
  const ops = config._sortedOps || (config.operators || []).slice().sort((a, b) => b.length - a.length);
  const kws = config._kwSet || new Set(config.keywords || []);
  const nums = config.numbers !== false;
  const tokens = [];
  let pos = 0;
  const len = input.length;

  while (pos < len) {
    const cc = input.charCodeAt(pos);

    // Skip whitespace
    if (_isWhitespace(cc)) { pos++; continue; }
    // Skip line comments
    if (cc === 37) { // %
      while (pos < len && input.charCodeAt(pos) !== 10) pos++;
      continue;
    }

    const start = pos;

    // Numbers
    if (nums && _isDigit(cc)) {
      if (cc === 48 && pos + 1 < len && input.charCodeAt(pos + 1) === 120) { // 0x
        pos += 2;
        while (pos < len && _isHexDigit(input.charCodeAt(pos))) pos++;
      } else {
        while (pos < len && _isDigit(input.charCodeAt(pos))) pos++;
      }
      tokens.push({ type: 'NUMBER', value: input.slice(start, pos), pos: start });
      continue;
    }

    // Identifiers / keywords
    if (_isIdentStart(cc)) {
      while (pos < len && _isIdentCont(input.charCodeAt(pos))) pos++;
      const word = input.slice(start, pos);
      tokens.push({
        type: kws.has(word) ? word : 'IDENT',
        value: word,
        pos: start,
      });
      continue;
    }

    // Multi-char operators (longest match first)
    let matched = false;
    for (let oi = 0; oi < ops.length; oi++) {
      const op = ops[oi];
      if (input.startsWith(op, pos)) {
        const end = pos + op.length;
        if (_isAlpha(op.charCodeAt(op.length - 1)) && end < len && _isWordChar(input.charCodeAt(end))) continue;
        tokens.push({ type: op, value: op, pos: start });
        pos += op.length;
        matched = true;
        break;
      }
    }
    if (matched) continue;

    // Single character
    tokens.push({ type: input[pos], value: input[pos], pos: start });
    pos++;
  }

  return tokens;
}

// ─── Earley Recognizer ───────────────────────────────────────────────────────

/**
 * Parse token stream with Earley algorithm.
 *
 * Uses Set for item dedup (instead of Map) — items are stored in flat arrays.
 * The complete step iterates the origin set's item array directly.
 *
 * @param {{ rules, start, nullable, byLhs }} g - Grammar
 * @param {{ type: string, value: string, pos: number }[]} tokens
 * @returns {*} Semantic value from start rule's action
 * @throws {Error} Parse error with position and expected tokens
 */
// Pre-allocated chart pool: avoids creating new Sets/arrays per parse call.
// Grows to accommodate the largest input seen.
const _chartPool = [];
function _ensureChart(n) {
  while (_chartPool.length <= n) {
    _chartPool.push({ seen: new Set(), items: [] });
  }
}

function earleyParse(g, tokens, extractFn) {
  const { rules, start, nullable, byLhs } = g;
  const n = tokens.length;
  const stride = n + 1;

  // Reuse pre-allocated chart sets (clear instead of reallocate)
  _ensureChart(n);
  for (let i = 0; i <= n; i++) {
    _chartPool[i].seen.clear();
    _chartPool[i].items.length = 0;
  }
  const chart = _chartPool;

  function add(si, ruleIdx, dot, origin, back) {
    const key = (ruleIdx * 256 + dot) * stride + origin;
    const set = chart[si];
    if (set.seen.has(key)) return;
    set.seen.add(key);
    set.items.push({ ruleIdx, dot, origin, back });
  }

  // Seed: predict start symbol at position 0
  const startRules = byLhs.get(start);
  if (startRules) {
    for (let i = 0; i < startRules.length; i++) add(0, startRules[i], 0, 0, null);
  }

  for (let i = 0; i <= n; i++) {
    const setItems = chart[i].items;
    let qi = 0;
    while (qi < setItems.length) {
      const item = setItems[qi++];
      const rule = rules[item.ruleIdx];

      if (item.dot >= rule.rhs.length) {
        // ── Complete ──
        const originItems = chart[item.origin].items;
        const lhs = rule.lhs;
        for (let j = 0; j < originItems.length; j++) {
          const orig = originItems[j];
          const oRule = rules[orig.ruleIdx];
          if (orig.dot < oRule.rhs.length) {
            const sym = oRule.rhs[orig.dot];
            if (sym.sym === 1 && sym.v === lhs) {
              add(i, orig.ruleIdx, orig.dot + 1, orig.origin,
                { t: 'c', l: orig, r: item });
            }
          }
        }
      } else {
        const sym = rule.rhs[item.dot];
        if (sym.sym === 1) {
          // ── Predict ──
          const predicted = byLhs.get(sym.v);
          if (predicted) {
            for (let j = 0; j < predicted.length; j++) add(i, predicted[j], 0, i, null);
          }
          // Aycock-Horspool: nullable advance
          if (nullable.has(sym.v)) {
            add(i, item.ruleIdx, item.dot + 1, item.origin,
              { t: 'n', l: item, nt: sym.v });
          }
        } else if (i < n && tokens[i].type === sym.v) {
          // ── Scan ──
          add(i + 1, item.ruleIdx, item.dot + 1, item.origin,
            { t: 's', l: item, tok: tokens[i] });
        }
      }
    }
  }

  // Find accepting item: start symbol, complete, origin 0, at position n
  let accept = null;
  const finalItems = chart[n].items;
  for (let i = 0; i < finalItems.length; i++) {
    const item = finalItems[i];
    const rule = rules[item.ruleIdx];
    if (rule.lhs === start && item.dot === rule.rhs.length && item.origin === 0) {
      accept = item;
      break;
    }
  }

  if (!accept) throw parseError(chart, tokens, rules, n);

  return (extractFn || extract)(accept, rules);
}

// ─── Tree Extraction ─────────────────────────────────────────────────────────

/** Walk back-pointers to reconstruct parse tree and evaluate actions. */
function extract(item, rules) {
  const rule = rules[item.ruleIdx];
  if (rule.rhs.length === 0) return rule.action ? rule.action([]) : null;

  const children = new Array(rule.rhs.length);
  let cur = item;

  for (let i = rule.rhs.length - 1; i >= 0; i--) {
    const back = cur.back;
    if (back.t === 's') {
      children[i] = back.tok;
      cur = back.l;
    } else if (back.t === 'c') {
      children[i] = extract(back.r, rules);
      cur = back.l;
    } else if (back.t === 'n') {
      children[i] = extractNullable(back.nt, rules);
      cur = back.l;
    }
  }

  return rule.action ? rule.action(children) : children;
}

/** Evaluate semantic action for a nullable nonterminal (ε-derivation). */
function extractNullable(ntId, rules) {
  for (const rule of rules) {
    if (rule.lhs === ntId && rule.rhs.length === 0) {
      return rule.action ? rule.action([]) : null;
    }
  }
  for (const rule of rules) {
    if (rule.lhs === ntId && rule.rhs.every(s => s.sym === 1)) {
      const children = rule.rhs.map(s => extractNullable(s.v, rules));
      return rule.action ? rule.action(children) : null;
    }
  }
  return null;
}

// ─── Error Reporting ─────────────────────────────────────────────────────────

function parseError(chart, tokens, rules, n) {
  // Rightmost chart set with items = furthest the parser got
  let rightmost = 0;
  for (let i = n; i >= 0; i--) {
    if (chart[i].items.length > 0) { rightmost = i; break; }
  }

  // Expected: terminals after the dot in rightmost set
  const expected = new Set();
  const rItems = chart[rightmost].items;
  for (let j = 0; j < rItems.length; j++) {
    const item = rItems[j];
    const rule = rules[item.ruleIdx];
    if (item.dot < rule.rhs.length && rule.rhs[item.dot].sym === 0) {
      expected.add(rule.rhs[item.dot].v);
    }
  }

  const pos = rightmost < tokens.length
    ? tokens[rightmost].pos
    : (tokens.length > 0 ? tokens[n - 1].pos + tokens[n - 1].value.length : 0);
  const got = rightmost < tokens.length
    ? `'${tokens[rightmost].value}'`
    : 'end of input';
  const exp = expected.size > 0
    ? [...expected].map(e => `'${e}'`).join(', ')
    : '(nothing)';

  return new Error(`Parse error at position ${pos}: expected ${exp}, got ${got}`);
}

// ─── Convenience ─────────────────────────────────────────────────────────────

/**
 * Create a parser function from grammar spec and lexer config.
 *
 * @param {{ rules: Rule[], start: number }} spec
 * @param {Object} lexerConfig
 * @returns {Function} parse(input) → semantic value
 */
function createParser(spec, lexerConfig) {
  const g = grammar(spec.rules, spec.start);
  return function parse(input) {
    return earleyParse(g, tokenize(input, lexerConfig));
  };
}

module.exports = { T, NT, grammar, tokenize, earleyParse, createParser, sortOperators };
