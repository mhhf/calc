/**
 * Abbreviation macros (@def) — TODO_0150
 *
 * Extralogical parse-time expansion. Two pure functions:
 *   extractMacros(source)        — scan @def directives, return table + clean source
 *   expandMacros(text, table)    — expand macro references in formula text
 *
 * Analogous to Twelf %abbrev: transparent, always expanded, no logical status.
 * Produces identical content-addressed hashes to writing things out longhand.
 */

/**
 * Extract @def directives from source text.
 * Scans for `@def name(params) := body.` — paren/brace-aware terminator.
 * Blanks directives from source (preserves line structure for error positions).
 *
 * @param {string} source
 * @returns {{ macroTable: Map<string, {params: string[], body: string}>, cleanSource: string }}
 */
function extractMacros(source) {
  const macroTable = new Map();
  // Match @def at top-level: @def name(params) := body.
  // We scan manually for paren-aware `.` terminator.
  const defRe = /(?:^|(?<=\n))[ \t]*@def\s+/g;
  const ranges = []; // [{start, end}] — byte ranges to blank

  let m;
  while ((m = defRe.exec(source)) !== null) {
    const directiveStart = m.index;
    let pos = m.index + m[0].length;

    // Read macro name
    const nameMatch = source.slice(pos).match(/^([a-z_][a-zA-Z0-9_]*)/);
    if (!nameMatch) {
      throw new Error(`@def: expected macro name at position ${pos}`);
    }
    const name = nameMatch[1];
    pos += name.length;

    // Read parameter list: (param1, param2, ...)
    if (source[pos] !== '(') {
      throw new Error(`@def ${name}: expected '(' after macro name`);
    }
    pos++; // skip (
    const paramsStart = pos;
    let depth = 1;
    while (pos < source.length && depth > 0) {
      if (source[pos] === '(') depth++;
      else if (source[pos] === ')') depth--;
      pos++;
    }
    const paramsText = source.slice(paramsStart, pos - 1);
    const params = paramsText.split(',').map(p => p.trim()).filter(p => p.length > 0);
    if (params.length === 0) {
      throw new Error(`@def ${name}: macros require at least one parameter`);
    }
    // Validate param names (must be uppercase-start identifiers — metavar convention)
    for (const p of params) {
      if (!/^[A-Z][a-zA-Z0-9_']*$/.test(p)) {
        throw new Error(`@def ${name}: invalid parameter '${p}' (must start with uppercase)`);
      }
    }

    // Skip whitespace + :=
    while (pos < source.length && /\s/.test(source[pos])) pos++;
    if (source.slice(pos, pos + 2) !== ':=') {
      throw new Error(`@def ${name}: expected ':=' after parameter list`);
    }
    pos += 2;
    while (pos < source.length && /\s/.test(source[pos])) pos++;

    // Read body until paren/brace-balanced '.'
    const bodyStart = pos;
    let parenDepth = 0, braceDepth = 0;
    while (pos < source.length) {
      const c = source[pos];
      if (c === '(') parenDepth++;
      else if (c === ')') parenDepth--;
      else if (c === '{') braceDepth++;
      else if (c === '}') braceDepth--;
      else if (c === '%') {
        // Skip comment to end of line
        while (pos < source.length && source[pos] !== '\n') pos++;
        continue;
      }
      else if (c === '.' && parenDepth === 0 && braceDepth === 0) {
        break;
      }
      pos++;
    }
    if (pos >= source.length) {
      throw new Error(`@def ${name}: unterminated macro body (missing '.')`);
    }
    const body = source.slice(bodyStart, pos).trim();
    pos++; // skip .

    if (macroTable.has(name)) {
      throw new Error(`@def ${name}: duplicate macro definition`);
    }
    macroTable.set(name, { params, body });
    ranges.push({ start: directiveStart, end: pos });
  }

  // Blank directive ranges (replace with spaces, preserve newlines)
  let cleanSource = source;
  if (ranges.length > 0) {
    const chars = source.split('');
    for (const { start, end } of ranges) {
      for (let i = start; i < end; i++) {
        if (chars[i] !== '\n') chars[i] = ' ';
      }
    }
    cleanSource = chars.join('');
  }

  return { macroTable, cleanSource };
}

/**
 * Expand macro references in formula text.
 * Finds `name(args)` where name is in macroTable, preceded by word boundary.
 * Iterative expansion for nested macros with cycle detection.
 *
 * @param {string} text - formula text
 * @param {Map<string, {params: string[], body: string}>} macroTable
 * @returns {string} expanded text
 */
function expandMacros(text, macroTable) {
  // Build regex: match any macro name followed by (
  const names = [...macroTable.keys()];
  if (names.length === 0) return text;

  // Detect $macro( — hard error
  for (const name of names) {
    const dollarIdx = text.indexOf('$' + name + '(');
    if (dollarIdx !== -1) {
      // Verify it's a word boundary before $
      if (dollarIdx === 0 || !/[A-Za-z0-9_]/.test(text[dollarIdx - 1])) {
        throw new Error(
          `$ (preserved) cannot prefix macro '${name}' — ` +
          `use $ on individual atoms inside the macro body`
        );
      }
    }
  }

  const visited = new Set();
  let result = text;
  let changed = true;
  let iterations = 0;
  const MAX_ITERATIONS = 50;

  while (changed && iterations < MAX_ITERATIONS) {
    changed = false;
    iterations++;

    for (const name of names) {
      let i = 0;
      while (i < result.length) {
        const idx = result.indexOf(name + '(', i);
        if (idx === -1) break;

        // Word boundary check: char before must not be [A-Za-z0-9_]
        if (idx > 0 && /[A-Za-z0-9_]/.test(result[idx - 1])) {
          i = idx + 1;
          continue;
        }

        // Find matching close paren for args
        const argsStart = idx + name.length + 1;
        let depth = 1;
        let j = argsStart;
        while (j < result.length && depth > 0) {
          if (result[j] === '(') depth++;
          else if (result[j] === ')') depth--;
          j++;
        }
        if (depth !== 0) {
          throw new Error(`Unmatched parenthesis in macro call '${name}' at position ${idx}`);
        }
        const argsText = result.slice(argsStart, j - 1);
        const args = splitArgs(argsText);

        const macro = macroTable.get(name);
        if (args.length !== macro.params.length) {
          throw new Error(
            `Macro '${name}' expects ${macro.params.length} argument(s), got ${args.length}`
          );
        }

        // Cycle detection
        const key = `${name}(${args.join(',')})`;
        if (visited.has(key)) {
          throw new Error(`Macro expansion cycle detected: ${key}`);
        }
        visited.add(key);

        // Substitute params → args in body
        let expanded = macro.body;
        for (let k = 0; k < macro.params.length; k++) {
          expanded = substituteParam(expanded, macro.params[k], args[k].trim());
        }

        result = result.slice(0, idx) + expanded + result.slice(j);
        changed = true;
        // Don't advance i — re-scan from same position for nested expansions
        break;
      }
      if (changed) break; // restart outer loop after any substitution
    }
  }

  if (iterations >= MAX_ITERATIONS) {
    throw new Error(`Macro expansion exceeded ${MAX_ITERATIONS} iterations — possible infinite loop`);
  }

  return result;
}

/**
 * Split comma-separated args respecting nested parens.
 * @param {string} text
 * @returns {string[]}
 */
function splitArgs(text) {
  const args = [];
  let depth = 0, start = 0;
  for (let i = 0; i < text.length; i++) {
    if (text[i] === '(') depth++;
    else if (text[i] === ')') depth--;
    else if (text[i] === ',' && depth === 0) {
      args.push(text.slice(start, i));
      start = i + 1;
    }
  }
  args.push(text.slice(start));
  return args.filter(a => a.trim().length > 0);
}

/**
 * Substitute a parameter name with its argument value (whole-word replacement).
 * Word boundary: param must not be preceded/followed by [A-Za-z0-9_'].
 * @param {string} body
 * @param {string} param
 * @param {string} arg
 * @returns {string}
 */
function substituteParam(body, param, arg) {
  // Build regex for whole-word match (params start uppercase, may contain ' for primed vars)
  const escaped = param.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const re = new RegExp(`(?<![A-Za-z0-9_'])${escaped}(?![A-Za-z0-9_'])`, 'g');
  return body.replace(re, arg);
}

module.exports = { extractMacros, expandMacros };
