/**
 * FormulaPlayground — inline formula parsing playground for book chapters.
 *
 * Markdown usage:
 *   ```{formula}
 *   A * (B -o C)
 *   ```
 * The body is the initial formula (optional). Renders the parsed formula
 * as KaTeX + ASCII + AST, editable in place.
 */
import { createSignal, createMemo, Show } from 'solid-js';
import ErrorBoundary from '../common/ErrorBoundary';
import KaTeX from '../math/KaTeX';
import ASTView from '../../components/graph/ASTView';
import { parseFormula, renderFormula, buildASTTree } from '../../lib/calculus';
import type { WidgetProps } from '../../lib/hydrateWidgets';

export default function FormulaPlayground(props: WidgetProps) {
  const [input, setInput] = createSignal(props.body.trim());
  const [showAst, setShowAst] = createSignal(props.options.ast === 'true');

  const parseResult = createMemo(() => {
    const text = input().trim();
    if (!text) return { formula: null as any, error: null as string | null };
    try {
      return { formula: parseFormula(text), error: null };
    } catch (e: any) {
      return { formula: null, error: e.message || 'Parse error' };
    }
  });

  const latex = createMemo(() => {
    const f = parseResult().formula;
    if (f == null) return '';
    try { return renderFormula(f, 'latex'); } catch { return ''; }
  });

  const ascii = createMemo(() => {
    const f = parseResult().formula;
    if (f == null) return '';
    try { return renderFormula(f, 'ascii'); } catch { return ''; }
  });

  const tree = createMemo(() => {
    const f = parseResult().formula;
    if (f == null || !showAst()) return null;
    try { return buildASTTree(f); } catch { return null; }
  });

  return (
    <ErrorBoundary>
      <div class="not-prose my-6 rounded-lg border border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800 overflow-hidden">
        <div class="flex items-center justify-between px-4 py-2 bg-gray-50 dark:bg-gray-900/40 border-b border-gray-200 dark:border-gray-700">
          <span class="text-xs font-semibold uppercase tracking-wide text-gray-500 dark:text-gray-400">
            Try it — formula playground
          </span>
          <button
            onClick={() => setShowAst(!showAst())}
            class="px-2 py-0.5 text-xs rounded border border-gray-200 dark:border-gray-700 text-gray-600 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700"
          >
            {showAst() ? 'Hide AST' : 'Show AST'}
          </button>
        </div>
        <div class="p-4 space-y-3">
          <input
            type="text"
            value={input()}
            onInput={(e) => setInput(e.currentTarget.value)}
            placeholder="Enter a formula, e.g. A -o (B * C)"
            class="w-full px-3 py-2 font-mono text-sm rounded border border-gray-300 dark:border-gray-600 bg-white dark:bg-gray-900 text-gray-900 dark:text-gray-100 focus:outline-none focus:ring-2 focus:ring-blue-500"
          />
          <Show when={parseResult().error}>
            <div class="text-sm text-red-600 dark:text-red-400">{parseResult().error}</div>
          </Show>
          <Show when={latex()}>
            <div class="text-center text-xl py-2">
              <KaTeX latex={latex()} display />
            </div>
            <div class="text-xs text-gray-500 dark:text-gray-400 font-mono text-center">{ascii()}</div>
          </Show>
          <Show when={tree()}>
            <div class="pt-2 border-t border-gray-100 dark:border-gray-700">
              <ASTView tree={tree()} />
            </div>
          </Show>
        </div>
      </div>
    </ErrorBoundary>
  );
}
