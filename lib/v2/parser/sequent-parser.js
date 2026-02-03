/**
 * Sequent Parser for v2
 *
 * Parses sequent strings like:
 *   "-- : P, -- : P -o Q |- -- : Q"
 *   "A, B |- C"
 *   "|- A * B"
 *
 * Syntax:
 *   sequent ::= [antecedent] '|-' succedent
 *   antecedent ::= hyp (',' hyp)*
 *   hyp ::= [term ':'] formula
 *   term ::= '--' | identifier
 *   succedent ::= [term ':'] formula
 */

/**
 * Create a sequent parser for a calculus
 * @param {Object} calculus - Loaded calculus with parse() method
 */
function createSequentParser(calculus) {
  /**
   * Parse a sequent string
   * @param {string} input - Sequent string
   * @returns {Object} Sequent object for v2 prover
   */
  function parseSequent(input) {
    const src = input.trim();

    // Split on turnstile
    const parts = src.split('|-');
    if (parts.length !== 2) {
      throw new Error(`Invalid sequent: expected '|-' turnstile in "${src}"`);
    }

    const [antecedentStr, succedentStr] = parts.map(s => s.trim());

    // Parse succedent
    const succedent = parseHyp(succedentStr);

    // Parse antecedent (comma-separated hypotheses)
    const linearFormulas = [];
    if (antecedentStr) {
      const hyps = splitTopLevel(antecedentStr, ',');
      for (const hyp of hyps) {
        const formula = parseHyp(hyp.trim());
        if (formula) linearFormulas.push(formula);
      }
    }

    // Build v2 sequent
    const Seq = require('../kernel/sequent');
    return Seq.fromArrays(linearFormulas, [], succedent);
  }

  /**
   * Parse a hypothesis (optional term ':' formula)
   * @param {string} input - Hypothesis string
   * @returns {Object} Formula AST
   */
  function parseHyp(input) {
    const trimmed = input.trim();
    if (!trimmed) return null;

    // Check for term : formula pattern
    const colonIdx = trimmed.indexOf(':');
    if (colonIdx > 0) {
      const term = trimmed.slice(0, colonIdx).trim();
      const formulaStr = trimmed.slice(colonIdx + 1).trim();

      // Skip term (we don't track proof terms in v2 yet)
      // Just parse the formula
      return calculus.parse(formulaStr);
    }

    // No colon - treat entire string as formula
    return calculus.parse(trimmed);
  }

  /**
   * Split a string at top level (respecting parentheses)
   */
  function splitTopLevel(str, delim) {
    const parts = [];
    let depth = 0;
    let start = 0;

    for (let i = 0; i < str.length; i++) {
      const c = str[i];
      if (c === '(') depth++;
      else if (c === ')') depth--;
      else if (c === delim && depth === 0) {
        parts.push(str.slice(start, i));
        start = i + 1;
      }
    }

    parts.push(str.slice(start));
    return parts.filter(s => s.trim());
  }

  /**
   * Format a sequent for display
   */
  function formatSequent(seq, format = 'ascii') {
    const Seq = require('../kernel/sequent');
    const linear = Seq.getContext(seq, 'linear');

    const formatFormula = (f) => calculus.render(f, format);

    const antecedent = linear.map(f => `-- : ${formatFormula(f)}`).join(', ');
    const succedent = `-- : ${formatFormula(seq.succedent)}`;

    if (antecedent) {
      return `${antecedent} |- ${succedent}`;
    }
    return `|- ${succedent}`;
  }

  return {
    parseSequent,
    parseHyp,
    formatSequent
  };
}

module.exports = { createSequentParser };
