import { createMemo, Show, For } from 'solid-js';
import KaTeX from './KaTeX';

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
 * Convert a sequent string to LaTeX notation.
 * Simple ASCII to LaTeX conversion without using the v1 parser.
 */
function sequentToLatex(sequentStr: string): string {
  // If already LaTeX formatted, return as-is
  if (isLatexFormatted(sequentStr)) {
    return sequentStr;
  }

  // Basic ASCII to LaTeX conversion
  return sequentStr
    .replace(/\|-/g, '\\vdash')
    .replace(/-o/g, '\\multimap')
    .replace(/\*/g, '\\otimes')
    .replace(/&/g, '\\&')
    .replace(/\+/g, '\\oplus')
    .replace(/!/g, '!')
    .replace(/;/g, ';')
    .replace(/,/g, ', ');
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
