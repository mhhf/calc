/**
 * Split string on separator respecting balanced brackets.
 *
 * Shared by: declarations.js, sequent-parser.js, rules2-parser.js.
 * Tracks depth for (), {}, and [] to avoid splitting inside nested expressions.
 *
 * Returns raw (untrimmed) parts; callers trim/filter as needed.
 *
 * @param {string} str - input string
 * @param {string} sep - separator (single or multi-char)
 * @returns {string[]} parts split on top-level occurrences of sep
 */
function balancedSplit(str, sep) {
  const parts = [];
  let depth = 0, braceDepth = 0, bracketDepth = 0, start = 0;
  for (let i = 0; i < str.length; i++) {
    const c = str[i];
    if (c === '(') depth++;
    else if (c === ')') depth--;
    else if (c === '{') braceDepth++;
    else if (c === '}') braceDepth--;
    else if (c === '[') bracketDepth++;
    else if (c === ']') bracketDepth--;
    else if (depth === 0 && braceDepth === 0 && bracketDepth === 0 && str.slice(i, i + sep.length) === sep) {
      parts.push(str.slice(start, i));
      start = i + sep.length;
      i += sep.length - 1;
    }
  }
  parts.push(str.slice(start));
  return parts;
}

module.exports = { balancedSplit };
