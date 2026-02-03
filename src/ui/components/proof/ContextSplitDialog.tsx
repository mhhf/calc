import { For, Show, createSignal, createMemo } from 'solid-js';
import KaTeX from '../math/KaTeX';
import { type ApplicableRule, sequentToLatex, previewSplitSubgoals } from '../../lib/proofLogicV2';

interface ContextEntry {
  id: string;
  formula: string;
  formulaLatex: string;
}

interface ContextSplitDialogProps {
  rule: ApplicableRule;
  contextEntries: ContextEntry[];
  currentSequent: any;  // The sequent being transformed
  position: string;     // Position for rule application
  onApply: (splits: { premise1: string[]; premise2: string[] }) => void;
  onCancel: () => void;
  onAutoSplit: () => void;
}

/**
 * Dialog for manually distributing context resources between premises
 * for rules like Tensor_R that split the context.
 *
 * In linear logic, all resources must be used exactly once (no weakening).
 * So all resources start assigned to premise 1, and user moves some to premise 2.
 */
export default function ContextSplitDialog(props: ContextSplitDialogProps) {
  // Track which premise each resource is assigned to (1 or 2)
  // Start with all resources assigned to premise 1 (no weakening = all must be used)
  const getInitialAssignments = (): Record<string, 1 | 2> => {
    const initial: Record<string, 1 | 2> = {};
    for (const entry of props.contextEntries) {
      initial[entry.id] = 1;  // Start all in premise 1
    }
    return initial;
  };
  const [assignments, setAssignments] = createSignal<Record<string, 1 | 2>>(getInitialAssignments());

  const premise1Resources = createMemo(() =>
    props.contextEntries.filter(e => assignments()[e.id] === 1)
  );

  const premise2Resources = createMemo(() =>
    props.contextEntries.filter(e => assignments()[e.id] === 2)
  );

  // Compute preview of subgoals based on current assignment
  // Always available since all resources are always assigned
  const previewSubgoals = createMemo(() => {
    const split = {
      premise1: props.contextEntries
        .filter(e => assignments()[e.id] === 1)
        .map(e => e.id),
      premise2: props.contextEntries
        .filter(e => assignments()[e.id] === 2)
        .map(e => e.id),
    };

    return previewSplitSubgoals(
      props.currentSequent,
      props.rule.name,
      props.position,
      split
    );
  });

  function toggleAssignment(id: string) {
    setAssignments(prev => {
      const current = prev[id];
      // Toggle between premise 1 and premise 2 (no unassigned state - linear logic!)
      const next = current === 1 ? 2 : 1;
      return { ...prev, [id]: next as 1 | 2 };
    });
  }

  function moveAllToPremise(premise: 1 | 2) {
    setAssignments(prev => {
      const next = { ...prev };
      for (const id of Object.keys(next)) {
        next[id] = premise;
      }
      return next as Record<string, 1 | 2>;
    });
  }

  function handleApply() {
    const splits = {
      premise1: props.contextEntries
        .filter(e => assignments()[e.id] === 1)
        .map(e => e.id),
      premise2: props.contextEntries
        .filter(e => assignments()[e.id] === 2)
        .map(e => e.id),
    };
    props.onApply(splits);
  }

  return (
    <div
      class="fixed inset-0 bg-black/50 flex items-center justify-center z-50"
      onClick={(e) => {
        if (e.target === e.currentTarget) props.onCancel();
      }}
    >
      <div class="bg-white dark:bg-gray-800 rounded-lg shadow-xl max-w-2xl w-full max-h-[90vh] overflow-hidden flex flex-col m-4">
        {/* Header */}
        <div class="px-4 py-3 border-b border-gray-200 dark:border-gray-700 flex-shrink-0">
          <h3 class="text-lg font-bold text-gray-900 dark:text-white">
            Distribute Context Resources
          </h3>
          <p class="text-sm text-gray-600 dark:text-gray-400 mt-1">
            Rule <span class="font-mono text-blue-600 dark:text-blue-400">{props.rule.name}</span> splits the context between two premises.
            Assign each resource to a premise.
          </p>
        </div>

        {/* Content */}
        <div class="flex-1 overflow-auto p-4">
          {/* Subgoal Preview - shown at top when all assigned */}
          <Show when={previewSubgoals()}>
            <div class="mb-6 bg-gradient-to-r from-emerald-50 to-violet-50 dark:from-emerald-900/20 dark:to-violet-900/20 rounded-lg p-4 border border-gray-200 dark:border-gray-700">
              <div class="text-sm font-semibold text-gray-700 dark:text-gray-300 mb-3 uppercase tracking-wide">
                New Subgoals Preview
              </div>
              <div class="space-y-3">
                <For each={previewSubgoals()}>
                  {(subgoal, index) => (
                    <div class="flex items-start gap-3">
                      <span
                        class="flex-shrink-0 w-6 h-6 rounded-full flex items-center justify-center text-xs font-bold text-white"
                        classList={{
                          'bg-emerald-500': index() === 0,
                          'bg-violet-500': index() === 1,
                        }}
                      >
                        {index() + 1}
                      </span>
                      <div class="flex-1 bg-white dark:bg-gray-800 rounded-lg px-3 py-2 border border-gray-100 dark:border-gray-700 overflow-x-auto">
                        <KaTeX latex={sequentToLatex(subgoal)} />
                      </div>
                    </div>
                  )}
                </For>
              </div>
            </div>
          </Show>

          {/* Resource list */}
          <div class="space-y-2 mb-6">
            <div class="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">
              Click resources to toggle assignment between
              <span class="text-emerald-600"> Premise 1</span> and
              <span class="text-violet-600"> Premise 2</span>
            </div>

            <Show when={props.contextEntries.length === 0}>
              <div class="text-sm text-gray-500 italic">
                No linear context resources to distribute.
              </div>
            </Show>

            <For each={props.contextEntries}>
              {(entry) => {
                const assignment = () => assignments()[entry.id];
                return (
                  <button
                    onClick={() => toggleAssignment(entry.id)}
                    class="w-full text-left px-3 py-2 rounded-lg border-2 transition-all"
                    classList={{
                      'border-emerald-400 bg-emerald-50 dark:bg-emerald-900/30': assignment() === 1,
                      'border-violet-400 bg-violet-50 dark:bg-violet-900/30': assignment() === 2,
                    }}
                  >
                    <div class="flex items-center justify-between">
                      <div class="flex items-center gap-2">
                        <span
                          class="w-6 h-6 rounded-full flex items-center justify-center text-xs font-bold text-white"
                          classList={{
                            'bg-emerald-500': assignment() === 1,
                            'bg-violet-500': assignment() === 2,
                          }}
                        >
                          {assignment()}
                        </span>
                        <KaTeX latex={entry.formulaLatex} />
                      </div>
                      <span
                        class="text-xs font-medium"
                        classList={{
                          'text-emerald-600 dark:text-emerald-400': assignment() === 1,
                          'text-violet-600 dark:text-violet-400': assignment() === 2,
                        }}
                      >
                        {assignment() === 1 && 'Premise 1'}
                        {assignment() === 2 && 'Premise 2'}
                      </span>
                    </div>
                  </button>
                );
              }}
            </For>
          </div>

          {/* Quick actions */}
          <div class="flex gap-2 mb-6">
            <button
              onClick={() => moveAllToPremise(1)}
              class="text-sm px-3 py-1 rounded bg-emerald-100 dark:bg-emerald-900/30 text-emerald-700 dark:text-emerald-300 hover:bg-emerald-200 dark:hover:bg-emerald-900/50"
            >
              All → Premise 1
            </button>
            <button
              onClick={() => moveAllToPremise(2)}
              class="text-sm px-3 py-1 rounded bg-violet-100 dark:bg-violet-900/30 text-violet-700 dark:text-violet-300 hover:bg-violet-200 dark:hover:bg-violet-900/50"
            >
              All → Premise 2
            </button>
          </div>

          {/* Preview */}
          <div class="grid grid-cols-2 gap-4">
            <div class="border border-emerald-200 dark:border-emerald-800 rounded-lg p-3">
              <div class="text-sm font-medium text-emerald-700 dark:text-emerald-300 mb-2 flex items-center gap-2">
                <span class="w-5 h-5 rounded-full bg-emerald-500 text-white flex items-center justify-center text-xs">1</span>
                Premise 1
              </div>
              <Show
                when={premise1Resources().length > 0}
                fallback={<span class="text-sm text-gray-400 italic">Empty context</span>}
              >
                <div class="space-y-1">
                  <For each={premise1Resources()}>
                    {(entry) => (
                      <div class="text-sm">
                        <KaTeX latex={entry.formulaLatex} />
                      </div>
                    )}
                  </For>
                </div>
              </Show>
            </div>

            <div class="border border-violet-200 dark:border-violet-800 rounded-lg p-3">
              <div class="text-sm font-medium text-violet-700 dark:text-violet-300 mb-2 flex items-center gap-2">
                <span class="w-5 h-5 rounded-full bg-violet-500 text-white flex items-center justify-center text-xs">2</span>
                Premise 2
              </div>
              <Show
                when={premise2Resources().length > 0}
                fallback={<span class="text-sm text-gray-400 italic">Empty context</span>}
              >
                <div class="space-y-1">
                  <For each={premise2Resources()}>
                    {(entry) => (
                      <div class="text-sm">
                        <KaTeX latex={entry.formulaLatex} />
                      </div>
                    )}
                  </For>
                </div>
              </Show>
            </div>
          </div>
        </div>

        {/* Footer */}
        <div class="px-4 py-3 border-t border-gray-200 dark:border-gray-700 flex-shrink-0 flex justify-between">
          <button
            onClick={props.onAutoSplit}
            class="px-4 py-2 bg-green-600 text-white rounded-lg hover:bg-green-700 transition-colors flex items-center gap-2"
          >
            <svg class="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M13 10V3L4 14h7v7l9-11h-7z" />
            </svg>
            Auto-split
          </button>
          <div class="flex gap-2">
            <button
              onClick={props.onCancel}
              class="px-4 py-2 text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-700 rounded-lg transition-colors"
            >
              Cancel
            </button>
            <button
              onClick={handleApply}
              class="px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
            >
              Apply with Split
            </button>
          </div>
        </div>
      </div>
    </div>
  );
}

export type { ContextEntry };
