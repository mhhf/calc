import { createSignal, createMemo, Show } from 'solid-js';
import KaTeX from '../components/math/KaTeX';
import FormulaInput from '../components/math/FormulaInput';
import ASTView from '../components/graph/ASTView';
import ErrorBoundary from '../components/common/ErrorBoundary';

// v2 API
import { parseFormula, renderFormula, buildASTTree, type Formula } from '../lib/calculus';

export default function Sandbox() {
  const [input, setInput] = createSignal('');
  const [error, setError] = createSignal<string | null>(null);

  const parsed = createMemo((): Formula | null => {
    const formula = input().trim();
    if (!formula) {
      setError(null);
      return null;
    }

    try {
      const node = parseFormula(formula);
      setError(null);
      return node;
    } catch (e: any) {
      setError(e.message || 'Parse error');
      return null;
    }
  });

  const latex = createMemo(() => {
    const node = parsed();
    if (!node) return '';
    try {
      return renderFormula(node, 'latex');
    } catch {
      return '';
    }
  });

  const asciiOutput = createMemo(() => {
    const node = parsed();
    if (!node) return '';
    try {
      return renderFormula(node, 'ascii');
    } catch {
      return '';
    }
  });

  const treeData = createMemo(() => {
    const node = parsed();
    if (!node) return null;
    try {
      return buildASTTree(node);
    } catch {
      return null;
    }
  });

  // Example formulas for quick testing
  const examples = [
    { label: 'Linear implication', formula: 'A -o B' },
    { label: 'Tensor product', formula: 'A * B' },
    { label: 'With (additive conjunction)', formula: 'A & B' },
    { label: 'Plus (additive disjunction)', formula: 'A + B' },
    { label: 'Bang (exponential)', formula: '!A' },
    { label: 'Complex', formula: '(A -o B) * (!C -o D)' },
  ];

  return (
    <ErrorBoundary>
      <div class="max-w-4xl mx-auto p-6 space-y-6 text-gray-900 dark:text-gray-100">
        <div>
          <h2 class="text-2xl font-bold text-gray-900 dark:text-white mb-2">
            Formula Sandbox
          </h2>
          <p class="text-gray-600 dark:text-gray-400">
            Enter a linear logic formula to parse and visualize it.
          </p>
        </div>

        {/* Formula input */}
        <FormulaInput
          value={input()}
          onInput={setInput}
          error={error()}
          placeholder="Enter a formula (e.g., A -o B, A * B, !A)"
        />

        {/* Example buttons */}
        <div class="flex flex-wrap gap-2">
          <span class="text-sm text-gray-500 dark:text-gray-400 mr-2">Examples:</span>
          {examples.map((ex) => (
            <button
              onClick={() => setInput(ex.formula)}
              class="px-3 py-1 text-sm bg-gray-100 dark:bg-gray-700 text-gray-700 dark:text-gray-300 rounded hover:bg-gray-200 dark:hover:bg-gray-600 transition-colors"
              title={ex.label}
            >
              {ex.formula}
            </button>
          ))}
        </div>

        {/* Output section */}
        <Show when={parsed()}>
          <div class="space-y-4">
            {/* LaTeX rendering */}
            <div class="bg-white dark:bg-gray-800 rounded-lg p-6 shadow-sm border border-gray-200 dark:border-gray-700 text-gray-900 dark:text-gray-100">
              <h3 class="text-sm font-medium text-gray-500 dark:text-gray-400 mb-3">
                Rendered Formula
              </h3>
              <div class="text-center text-2xl text-gray-900 dark:text-gray-100">
                <KaTeX latex={latex()} display />
              </div>
            </div>

            {/* ASCII output */}
            <div class="bg-white dark:bg-gray-800 rounded-lg p-4 shadow-sm border border-gray-200 dark:border-gray-700">
              <h3 class="text-sm font-medium text-gray-500 dark:text-gray-400 mb-2">
                ASCII Representation
              </h3>
              <code class="font-mono text-gray-900 dark:text-gray-100">
                {asciiOutput()}
              </code>
            </div>

            {/* LaTeX source */}
            <div class="bg-white dark:bg-gray-800 rounded-lg p-4 shadow-sm border border-gray-200 dark:border-gray-700">
              <h3 class="text-sm font-medium text-gray-500 dark:text-gray-400 mb-2">
                LaTeX Source
              </h3>
              <code class="font-mono text-sm text-gray-900 dark:text-gray-100 bg-gray-100 dark:bg-gray-900 px-2 py-1 rounded">
                {latex()}
              </code>
            </div>

            {/* AST Tree */}
            <div class="bg-white dark:bg-gray-800 rounded-lg p-4 shadow-sm border border-gray-200 dark:border-gray-700">
              <h3 class="text-sm font-medium text-gray-500 dark:text-gray-400 mb-3">
                Abstract Syntax Tree
              </h3>
              <ASTView tree={treeData()} />
            </div>
          </div>
        </Show>

        {/* Empty state */}
        <Show when={!parsed() && !error()}>
          <div class="text-center py-12 text-gray-500 dark:text-gray-400">
            <svg class="w-16 h-16 mx-auto mb-4 opacity-50" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="1.5" d="M9 12h6m-6 4h6m2 5H7a2 2 0 01-2-2V5a2 2 0 012-2h5.586a1 1 0 01.707.293l5.414 5.414a1 1 0 01.293.707V19a2 2 0 01-2 2z" />
            </svg>
            <p>Enter a formula above to see the parsed output</p>
          </div>
        </Show>
      </div>
    </ErrorBoundary>
  );
}
