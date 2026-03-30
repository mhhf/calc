/**
 * Earley parser — core recognizer + tree extraction.
 *
 * Generic, grammar-agnostic. Takes CFG rules with semantic actions,
 * produces values via bottom-up action evaluation.
 *
 * Complexity: O(n³) general, O(n²) unambiguous, O(n) LR-class.
 * Item packing: u32 = (ruleIdx:16 | dot:8 | origin:8) — max 255 tokens.
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
 * @param {{ operators?: string[], keywords?: string[], numbers?: boolean }} config
 * @returns {{ type: string, value: string, pos: number }[]}
 */
function tokenize(input, config = {}) {
  const ops = (config.operators || []).slice().sort((a, b) => b.length - a.length);
  const kws = new Set(config.keywords || []);
  const nums = config.numbers !== false;
  const tokens = [];
  let pos = 0;

  while (pos < input.length) {
    // Skip whitespace
    if (/\s/.test(input[pos])) { pos++; continue; }
    // Skip line comments
    if (input[pos] === '%') {
      while (pos < input.length && input[pos] !== '\n') pos++;
      continue;
    }

    const start = pos;

    // Numbers
    if (nums && /\d/.test(input[pos])) {
      if (input[pos] === '0' && pos + 1 < input.length && input[pos + 1] === 'x') {
        pos += 2;
        while (pos < input.length && /[0-9a-fA-F]/.test(input[pos])) pos++;
      } else {
        while (pos < input.length && /\d/.test(input[pos])) pos++;
      }
      tokens.push({ type: 'NUMBER', value: input.slice(start, pos), pos: start });
      continue;
    }

    // Identifiers / keywords
    if (/[A-Za-z_']/.test(input[pos])) {
      while (pos < input.length && /[A-Za-z0-9_']/.test(input[pos])) pos++;
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
    for (const op of ops) {
      if (input.startsWith(op, pos)) {
        const end = pos + op.length;
        if (/[a-zA-Z]$/.test(op) && end < input.length && /\w/.test(input[end])) continue;
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
 * @param {{ rules, start, nullable, byLhs }} g - Grammar
 * @param {{ type: string, value: string, pos: number }[]} tokens
 * @returns {*} Semantic value from start rule's action
 * @throws {Error} Parse error with position and expected tokens
 */
function earleyParse(g, tokens, extractFn) {
  const { rules, start, nullable, byLhs } = g;
  const n = tokens.length;

  // Chart: S[0..n], each set = { items: Map<u32key, item>, queue: item[] }
  const chart = new Array(n + 1);
  for (let i = 0; i <= n; i++) {
    chart[i] = { items: new Map(), queue: [] };
  }

  function add(si, ruleIdx, dot, origin, back) {
    const key = (ruleIdx << 16) | (dot << 8) | origin;
    if (chart[si].items.has(key)) return;
    const item = { ruleIdx, dot, origin, back };
    chart[si].items.set(key, item);
    chart[si].queue.push(item);
  }

  // Seed: predict start symbol at position 0
  for (const ri of (byLhs.get(start) || [])) add(0, ri, 0, 0, null);

  for (let i = 0; i <= n; i++) {
    const set = chart[i];
    let qi = 0;
    while (qi < set.queue.length) {
      const item = set.queue[qi++];
      const rule = rules[item.ruleIdx];

      if (item.dot >= rule.rhs.length) {
        // ── Complete ──
        for (const [, orig] of chart[item.origin].items) {
          const oRule = rules[orig.ruleIdx];
          if (orig.dot < oRule.rhs.length) {
            const sym = oRule.rhs[orig.dot];
            if (sym.sym === 1 && sym.v === rule.lhs) {
              add(i, orig.ruleIdx, orig.dot + 1, orig.origin,
                { t: 'c', l: orig, r: item });
            }
          }
        }
      } else {
        const sym = rule.rhs[item.dot];
        if (sym.sym === 1) {
          // ── Predict ──
          for (const ri of (byLhs.get(sym.v) || [])) add(i, ri, 0, i, null);
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
  for (const [, item] of chart[n].items) {
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

// ─── Lazy Extraction ─────────────────────────────────────────────────────────

/**
 * Extract parse tree without evaluating actions.
 * Returns { rule, children } where children are tokens or subtrees.
 * Used for context-dependent evaluation (e.g., de Bruijn binder encoding).
 */
function extractLazy(item, rules) {
  const rule = rules[item.ruleIdx];
  if (rule.rhs.length === 0) return { rule, children: [] };

  const children = new Array(rule.rhs.length);
  let cur = item;

  for (let i = rule.rhs.length - 1; i >= 0; i--) {
    const back = cur.back;
    if (back.t === 's') {
      children[i] = back.tok;
      cur = back.l;
    } else if (back.t === 'c') {
      children[i] = extractLazy(back.r, rules);
      cur = back.l;
    } else if (back.t === 'n') {
      children[i] = extractNullableLazy(back.nt, rules);
      cur = back.l;
    }
  }

  return { rule, children };
}

function extractNullableLazy(ntId, rules) {
  for (const rule of rules) {
    if (rule.lhs === ntId && rule.rhs.length === 0) {
      return { rule, children: [] };
    }
  }
  for (const rule of rules) {
    if (rule.lhs === ntId && rule.rhs.every(s => s.sym === 1)) {
      return { rule, children: rule.rhs.map(s => extractNullableLazy(s.v, rules)) };
    }
  }
  return { rule: { lhs: ntId, rhs: [], action: null }, children: [] };
}

// ─── Error Reporting ─────────────────────────────────────────────────────────

function parseError(chart, tokens, rules, n) {
  // Rightmost chart set with items = furthest the parser got
  let rightmost = 0;
  for (let i = n; i >= 0; i--) {
    if (chart[i].items.size > 0) { rightmost = i; break; }
  }

  // Expected: terminals after the dot in rightmost set
  const expected = new Set();
  for (const [, item] of chart[rightmost].items) {
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

module.exports = { T, NT, grammar, tokenize, earleyParse, extractLazy, createParser };
