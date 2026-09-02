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

import { balancedSplit } from './balanced-split.js';
// Hoisted by tools/esm-hoist.js:
import Seq from '../kernel/sequent.js';

/**
 * Create a sequent parser for a calculus
 * @param {Object} calculus - Loaded calculus with parse() and render() methods
 */
function sequentParser(calculus) {
  // Zone names from the calculus's declared structure (TODO_0086).
  const ctxStruct = calculus.contextStructure || Seq.DEFAULT_CONTEXT_STRUCTURE;
  const CZ = ctxStruct.consumableZone;
  const SZ = ctxStruct.copySource;
  function parseSequent(input) {
    const src = input.trim();
    const parts = balancedSplit(src, '|-');
    if (parts.length !== 2) {
      throw new Error(`Invalid sequent: expected '|-' turnstile in "${src}"`);
    }

    const [antecedentStr, succedentStr] = parts.map(s => s.trim());
    const succedent = parseHyp(succedentStr);

    const linearFormulas = [];
    if (antecedentStr) {
      const hyps = balancedSplit(antecedentStr, ',').filter(s => s.trim());
      for (const hyp of hyps) {
        const formula = parseHyp(hyp.trim());
        if (formula) linearFormulas.push(formula);
      }
    }


    return Seq.seq({ [CZ]: linearFormulas, [SZ]: [] }, succedent);
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

  function formatSequent(seq, format = 'ascii') {

    const linear = Seq.getContext(seq, CZ);
    const cart = Seq.getContext(seq, SZ);

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

export { sequentParser };
export default { sequentParser };
