/**
 * Manual Proof Rendering — display formatting for interactive proofs.
 *
 * Separated from manual.js (state management) for clean separation of concerns.
 * These functions require a calculus with render() capability.
 */

const Seq = require('../../kernel/sequent');

/**
 * Create rendering helpers for a calculus
 * @param {Object} calculus - Loaded calculus with render()
 */
function createManualProofRenderer(calculus) {

  /**
   * Render sequent with optional focus highlighting
   * @param {Object} seq - Sequent to render
   * @param {string} format - 'ascii' or 'latex'
   * @param {Object} [focus] - Focus state for highlighting
   */
  function renderSequent(seq, format = 'ascii', focus = null) {
    const linear = Seq.getContext(seq, 'linear');
    const cart = Seq.getContext(seq, 'cartesian');
    const succedent = seq.succedent;

    const renderFormula = (h, highlight = false) => {
      const rendered = calculus.render(h, format);
      if (highlight) {
        if (format === 'latex') return `[${rendered}]`;
        return `[${rendered}]`;
      }
      return rendered;
    };

    // Render linear context with focus highlighting
    const linearParts = linear.map((h, i) => {
      const highlight = focus && focus.position === 'L' && focus.index === i;
      return renderFormula(h, highlight);
    });

    // Render succedent with focus highlighting
    const highlightSucc = focus && focus.position === 'R';
    const succPart = renderFormula(succedent, highlightSucc);

    const cartPart = cart.length > 0 ? cart.map(h => renderFormula(h)).join(', ') + ' ; ' : '';
    const linearPart = linearParts.join(', ');
    const turnstile = format === 'latex' ? '\\vdash' : '|-';

    if (cartPart) {
      return `${cartPart}${linearPart} ${turnstile} ${succPart}`;
    }
    return linearPart ? `${linearPart} ${turnstile} ${succPart}` : `${turnstile} ${succPart}`;
  }

  /**
   * Get abstract rule display (for inference rule visualization)
   */
  function getAbstractRule(ruleName) {
    const schemas = {
      'tensor_r': {
        conclusion: '\\Gamma \\vdash A \\otimes B',
        premises: ['\\Gamma_1 \\vdash A', '\\Gamma_2 \\vdash B'],
      },
      'tensor_l': {
        conclusion: '\\Gamma, A \\otimes B \\vdash C',
        premises: ['\\Gamma, A, B \\vdash C'],
      },
      'loli_r': {
        conclusion: '\\Gamma \\vdash A \\multimap B',
        premises: ['\\Gamma, A \\vdash B'],
      },
      'loli_l': {
        conclusion: '\\Gamma, A \\multimap B \\vdash C',
        premises: ['\\Gamma_1 \\vdash A', '\\Gamma_2, B \\vdash C'],
      },
      'with_r': {
        conclusion: '\\Gamma \\vdash A \\& B',
        premises: ['\\Gamma \\vdash A', '\\Gamma \\vdash B'],
      },
      'with_l1': {
        conclusion: '\\Gamma, A \\& B \\vdash C',
        premises: ['\\Gamma, A \\vdash C'],
      },
      'with_l2': {
        conclusion: '\\Gamma, A \\& B \\vdash C',
        premises: ['\\Gamma, B \\vdash C'],
      },
      'one_r': {
        conclusion: '\\vdash I',
        premises: [],
      },
      'one_l': {
        conclusion: '\\Gamma, I \\vdash C',
        premises: ['\\Gamma \\vdash C'],
      },
      'id': {
        conclusion: 'A \\vdash A',
        premises: [],
      },
      'Focus_L': {
        conclusion: '\\Gamma, A \\vdash C',
        premises: ['\\Gamma, [A] \\vdash C'],
      },
      'Focus_R': {
        conclusion: '\\Gamma \\vdash A',
        premises: ['\\Gamma \\vdash [A]'],
      },
    };

    return schemas[ruleName] || { conclusion: ruleName, premises: [] };
  }

  return { renderSequent, getAbstractRule };
}

module.exports = { createManualProofRenderer };
