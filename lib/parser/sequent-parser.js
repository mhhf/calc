/**
 * Sequent Parser
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
 * @param {Object} calculus - Loaded calculus with parse() and render() methods
 */
function createSequentParser(calculus) {
  function parseSequent(input) {
    const src = input.trim();
    const parts = src.split('|-');
    if (parts.length !== 2) {
      throw new Error(`Invalid sequent: expected '|-' turnstile in "${src}"`);
    }

    const [antecedentStr, succedentStr] = parts.map(s => s.trim());
    const succedent = parseHyp(succedentStr);

    const linearFormulas = [];
    if (antecedentStr) {
      const hyps = splitTopLevel(antecedentStr, ',');
      for (const hyp of hyps) {
        const formula = parseHyp(hyp.trim());
        if (formula) linearFormulas.push(formula);
      }
    }

    const Seq = require('../kernel/sequent');
    return Seq.fromArrays(linearFormulas, [], succedent);
  }

  function parseHyp(input) {
    const trimmed = input.trim();
    if (!trimmed) return null;

    const colonIdx = trimmed.indexOf(':');
    if (colonIdx > 0) {
      const formulaStr = trimmed.slice(colonIdx + 1).trim();
      return calculus.parse(formulaStr);
    }

    return calculus.parse(trimmed);
  }

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

  function formatSequent(seq, format = 'ascii') {
    const Seq = require('../kernel/sequent');
    const linear = Seq.getContext(seq, 'linear');
    const cart = Seq.getContext(seq, 'cartesian');

    const formatFormula = (f) => calculus.render(f, format);

    const linearPart = linear.map(formatFormula).join(', ');
    const cartPart = cart.length > 0 ? cart.map(formatFormula).join(', ') + ' ; ' : '';
    const succedentPart = formatFormula(seq.succedent);

    if (format === 'latex') {
      const turnstile = '\\vdash';
      if (cartPart) {
        return `${cartPart}${linearPart} ${turnstile} ${succedentPart}`;
      }
      return linearPart ? `${linearPart} ${turnstile} ${succedentPart}` : `${turnstile} ${succedentPart}`;
    }

    if (cartPart) {
      return `${cartPart}${linearPart} |- ${succedentPart}`;
    }
    return linearPart ? `${linearPart} |- ${succedentPart}` : `|- ${succedentPart}`;
  }

  return {
    parseSequent,
    parseHyp,
    formatSequent
  };
}

module.exports = { createSequentParser };
