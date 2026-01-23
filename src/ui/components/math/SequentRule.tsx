import { createMemo, Show, For } from 'solid-js';
import KaTeX from './KaTeX';

// @ts-ignore - CommonJS module
import * as CalcModule from '../../../../lib/calc.js';
// @ts-ignore - CommonJS module
import * as NodeModule from '../../../../lib/node.js';
// @ts-ignore - Generated parser
import * as parserMod from '../../../../out/parser.js';

const Calc = (CalcModule as any).default || CalcModule;
const Node = (NodeModule as any).default || NodeModule;
const parserModule = (parserMod as any).default || parserMod;

// Set up parser
parserModule.parser.yy.Node = Node;

interface SequentRuleProps {
  name: string;
  ruleStrings: string[]; // [conclusion, premise1, premise2, ...]
  simplified?: boolean;
  showAscii?: boolean;
}

/**
 * Convert metavariables to paper-style notation.
 * Preserves focus brackets [...] in the output.
 */
function simplifySequent(latex: string): string {
  return latex
    // Context metavariables
    .replace(/\?\s*X/g, '\\Gamma')
    .replace(/\?\s*Y/g, '\\Delta')
    .replace(/\?\s*Z/g, '\\Sigma')
    // Formula metavariables - remove F? prefix (but not inside brackets)
    .replace(/F\?\s*([A-Z])/g, '$1')
    // Structure metavariables
    .replace(/S\?\s*([A-Z])/g, '$1')
    // Term placeholder
    .replace(/\\cdot\s*:/g, '')
    .replace(/--\s*:/g, '')
    .replace(/--/g, '')
    // Clean up extra spaces (but preserve brackets)
    .replace(/\s+/g, ' ')
    .replace(/\(\s+/g, '(')
    .replace(/\s+\)/g, ')')
    // Clean up space before brackets
    .replace(/\[\s+/g, '[')
    .replace(/\s+\]/g, ']')
    .trim();
}

/**
 * Check if a string is already LaTeX formatted (contains \vdash)
 */
function isLatexFormatted(str: string): boolean {
  return str.includes('\\vdash') || str.includes('\\Gamma') || str.includes('\\multimap');
}

/**
 * Parse a sequent string and convert to LaTeX.
 * Handles focus brackets [formula] by extracting them, parsing the content,
 * and re-wrapping with brackets in the output.
 */
function sequentToLatex(sequentStr: string): string {
  // If already LaTeX formatted, return as-is
  if (isLatexFormatted(sequentStr)) {
    return sequentStr;
  }

  // Check for focus brackets and extract them
  // Pattern: [-- : formula] or [formula] in the sequent
  const bracketPattern = /\[([^\]]+)\]/g;
  const brackets: { placeholder: string; content: string; latex?: string }[] = [];
  let processedStr = sequentStr;

  // Replace brackets with placeholders before parsing
  let matchIndex = 0;
  processedStr = sequentStr.replace(bracketPattern, (match, content) => {
    const placeholder = `__FOCUS_${matchIndex}__`;
    brackets.push({ placeholder, content: content.trim() });
    matchIndex++;
    return placeholder;
  });

  try {
    // Parse the sequent without brackets
    const parsed = parserModule.parser.parse(processedStr);
    let latex = parsed.toString({ style: 'latex_se' });

    // Convert bracket contents to LaTeX and wrap with focus notation
    for (const b of brackets) {
      try {
        // Try to parse the bracket content as a formula/term
        const contentParsed = parserModule.parser.parse(`I |- ${b.content}`);
        // Extract just the succedent part
        const contentLatex = contentParsed.vals[1].toString({ style: 'latex' });
        b.latex = `[${contentLatex}]`;
      } catch {
        // Fallback: just wrap the content
        b.latex = `[${b.content}]`;
      }
      // Replace placeholder with bracketed LaTeX
      latex = latex.replace(b.placeholder, b.latex);
    }

    return latex;
  } catch {
    // Fallback: basic ASCII to LaTeX conversion
    let result = sequentStr
      .replace(/\|-/g, '\\vdash')
      .replace(/-o/g, '\\multimap')
      .replace(/\*/g, '\\otimes')
      .replace(/&/g, '\\&')
      .replace(/!/g, '!')
      .replace(/,/g, ', ');

    // Keep the brackets in fallback mode
    return result;
  }
}

/**
 * Renders an inference rule in standard fraction notation:
 *
 *     premise₁    premise₂
 *   ─────────────────────── (RuleName)
 *          conclusion
 */
export default function SequentRule(props: SequentRuleProps) {
  const ruleData = createMemo(() => {
    const [conclusion, ...premises] = props.ruleStrings;

    // Convert to LaTeX
    let conclusionLatex = sequentToLatex(conclusion);
    let premisesLatex = premises.map(p => sequentToLatex(p));

    // Simplify if requested
    if (props.simplified) {
      conclusionLatex = simplifySequent(conclusionLatex);
      premisesLatex = premisesLatex.map(simplifySequent);
    }

    return {
      conclusion: conclusionLatex,
      conclusionAscii: conclusion,
      premises: premisesLatex,
      premisesAscii: premises,
    };
  });

  // Build the inference rule LaTeX using \cfrac or custom layout
  const ruleLatex = createMemo(() => {
    const data = ruleData();
    const premiseStr = data.premises.length > 0
      ? data.premises.join(' \\quad ')
      : '';

    if (data.premises.length === 0) {
      // Axiom - no premises
      return `\\cfrac{}{${data.conclusion}}`;
    }

    return `\\cfrac{${premiseStr}}{${data.conclusion}}`;
  });

  return (
    <div class="rule-card bg-white dark:bg-gray-800 rounded-lg p-4 border border-gray-200 dark:border-gray-700">
      {/* Rule name */}
      <div class="flex items-center justify-between mb-3">
        <span class="font-mono text-sm font-semibold text-blue-600 dark:text-blue-400">
          {props.name}
        </span>
      </div>

      {/* Inference rule display */}
      <div class="text-center py-2 overflow-x-auto">
        <KaTeX latex={ruleLatex()} display={true} />
      </div>

      {/* ASCII fallback/reference */}
      <Show when={props.showAscii}>
        <div class="mt-3 pt-3 border-t border-gray-200 dark:border-gray-700">
          <div class="text-xs text-gray-500 dark:text-gray-400 font-mono space-y-1">
            <For each={ruleData().premisesAscii}>
              {(p) => <div>{p}</div>}
            </For>
            <div class="border-t border-gray-300 dark:border-gray-600 my-1"></div>
            <div>{ruleData().conclusionAscii}</div>
          </div>
        </div>
      </Show>
    </div>
  );
}
