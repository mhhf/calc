/**
 * Quiz — multiple-choice check for book chapters.
 *
 * Markdown usage:
 *   ```{quiz, id=ch1-q1}
 *   Q: Which connective is *internal* choice?
 *   - [x] oplus (+)
 *   - [ ] with (&)
 *   - [ ] tensor (*)
 *   explanation: The prover picks the branch for ⊕; the environment picks for &.
 *   ```
 *
 * Multiple `Q:` sections in one block become a multi-question quiz.
 * Options with more than one [x] render as checkboxes (all must match).
 * Inline `$...$` math in questions/options renders via KaTeX.
 */
import { createSignal, For, Show } from 'solid-js';
import katex from 'katex';
import ErrorBoundary from '../common/ErrorBoundary';
import { markExercise, isExerciseDone } from '../../state/progress';
import type { WidgetProps } from '../../lib/hydrateWidgets';

interface QuizQuestion {
  question: string;
  options: { text: string; correct: boolean }[];
  explanation: string;
}

function parseQuiz(body: string): QuizQuestion[] {
  const questions: QuizQuestion[] = [];
  let current: QuizQuestion | null = null;
  for (const line of body.split('\n')) {
    const q = line.match(/^Q\s*:\s*(.*)$/);
    if (q) {
      current = { question: q[1], options: [], explanation: '' };
      questions.push(current);
      continue;
    }
    if (!current) continue;
    const opt = line.match(/^\s*-\s*\[([ xX])\]\s*(.*)$/);
    if (opt) {
      current.options.push({ text: opt[2], correct: opt[1].toLowerCase() === 'x' });
      continue;
    }
    const ex = line.match(/^explanation\s*:\s*(.*)$/);
    if (ex) {
      current.explanation = ex[1];
      continue;
    }
    if (line.trim() && current.options.length === 0) {
      current.question += ' ' + line.trim();
    } else if (line.trim() && current.explanation) {
      current.explanation += ' ' + line.trim();
    }
  }
  return questions.filter(q => q.options.length >= 2);
}

/** Render text with inline $...$ math and `code` spans. */
function richText(text: string): string {
  let html = text
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  html = html.replace(/\$([^$]+)\$/g, (_, m) => {
    try { return katex.renderToString(m, { displayMode: false, throwOnError: false }); }
    catch { return m; }
  });
  html = html.replace(/`([^`]+)`/g, '<code>$1</code>');
  html = html.replace(/\*([^*]+)\*/g, '<em>$1</em>');
  return html;
}

export default function Quiz(props: WidgetProps) {
  const questions = parseQuiz(props.body);
  const quizId = props.options.id;
  const [selections, setSelections] = createSignal<Record<number, Set<number>>>({});
  const [checked, setChecked] = createSignal(false);

  const isMulti = (q: QuizQuestion) => q.options.filter(o => o.correct).length > 1;

  function toggle(qi: number, oi: number, multi: boolean) {
    setChecked(false);
    setSelections((prev) => {
      const next = { ...prev };
      const cur = new Set(next[qi] || []);
      if (multi) {
        cur.has(oi) ? cur.delete(oi) : cur.add(oi);
      } else {
        cur.clear();
        cur.add(oi);
      }
      next[qi] = cur;
      return next;
    });
  }

  function questionCorrect(qi: number): boolean {
    const q = questions[qi];
    const sel = selections()[qi] || new Set<number>();
    return q.options.every((o, oi) => o.correct === sel.has(oi));
  }

  const allCorrect = () => questions.every((_, qi) => questionCorrect(qi));

  function check() {
    setChecked(true);
    if (allCorrect() && quizId) markExercise(props.slug, quizId);
  }

  return (
    <ErrorBoundary>
      <div class="not-prose my-6 rounded-lg border border-purple-200 dark:border-purple-900 bg-purple-50/40 dark:bg-purple-950/20 overflow-hidden">
        <div class="flex items-center justify-between px-4 py-2 bg-purple-100/60 dark:bg-purple-900/30 border-b border-purple-200 dark:border-purple-900">
          <span class="text-xs font-semibold uppercase tracking-wide text-purple-700 dark:text-purple-300">
            Quick check
          </span>
          <Show when={quizId && isExerciseDone(props.slug, quizId!)}>
            <span class="text-xs text-green-600 dark:text-green-400">✓ done</span>
          </Show>
        </div>
        <div class="p-4 space-y-5">
          <For each={questions}>
            {(q, qi) => (
              <div>
                <div class="text-sm font-medium text-gray-900 dark:text-gray-100 mb-2" innerHTML={richText(q.question)} />
                <div class="space-y-1.5">
                  <For each={q.options}>
                    {(opt, oi) => {
                      const selected = () => (selections()[qi()] || new Set()).has(oi());
                      const showState = () => checked() && selected();
                      return (
                        <label
                          class="flex items-start gap-2 px-3 py-1.5 rounded border cursor-pointer text-sm transition-colors"
                          classList={{
                            'border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800 hover:bg-gray-50 dark:hover:bg-gray-700': !showState(),
                            'border-green-400 bg-green-50 dark:bg-green-900/30': showState() && opt.correct,
                            'border-red-400 bg-red-50 dark:bg-red-900/30': showState() && !opt.correct,
                          }}
                        >
                          <input
                            type={isMulti(q) ? 'checkbox' : 'radio'}
                            name={`quiz-${props.slug}-${quizId || 'q'}-${qi()}`}
                            checked={selected()}
                            onChange={() => toggle(qi(), oi(), isMulti(q))}
                            class="mt-0.5"
                          />
                          <span class="text-gray-800 dark:text-gray-200" innerHTML={richText(opt.text)} />
                        </label>
                      );
                    }}
                  </For>
                </div>
                <Show when={checked() && q.explanation && questionCorrect(qi())}>
                  <div class="mt-2 text-xs text-gray-600 dark:text-gray-400 italic" innerHTML={richText(q.explanation)} />
                </Show>
              </div>
            )}
          </For>
          <div class="flex items-center gap-3">
            <button
              onClick={check}
              class="px-3 py-1.5 text-sm font-medium rounded bg-purple-600 text-white hover:bg-purple-700 transition-colors"
            >
              Check
            </button>
            <Show when={checked()}>
              <span
                class="text-sm font-medium"
                classList={{
                  'text-green-600 dark:text-green-400': allCorrect(),
                  'text-red-600 dark:text-red-400': !allCorrect(),
                }}
              >
                {allCorrect() ? '✓ Correct!' : 'Not quite — try again.'}
              </span>
            </Show>
          </div>
        </div>
      </div>
    </ErrorBoundary>
  );
}
