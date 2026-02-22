import { Show, For } from 'solid-js';
import KaTeX from '../math/KaTeX';
import { type RuleApplicationDetails } from '../../lib/proofLogic';

interface RuleDetailDialogProps {
  details: RuleApplicationDetails | null;
  onClose: () => void;
}

/**
 * Dialog showing details of a rule application:
 * - The abstract rule
 * - The substitution (MGU)
 * - The instantiated premises
 */
export default function RuleDetailDialog(props: RuleDetailDialogProps) {
  // Close on backdrop click
  const handleBackdropClick = (e: MouseEvent) => {
    if (e.target === e.currentTarget) {
      props.onClose();
    }
  };

  // Close on Escape key
  const handleKeyDown = (e: KeyboardEvent) => {
    if (e.key === 'Escape') {
      props.onClose();
    }
  };

  return (
    <Show when={props.details}>
      <div
        class="fixed inset-0 bg-black/50 flex items-center justify-center z-50 p-4"
        onClick={handleBackdropClick}
        onKeyDown={handleKeyDown}
        tabIndex={0}
      >
        <div class="bg-white dark:bg-gray-800 rounded-lg shadow-lg max-w-2xl w-full max-h-[90vh] overflow-auto text-gray-900 dark:text-gray-100">
          {/* Header */}
          <div class="flex items-center justify-between p-4 border-b border-gray-200 dark:border-gray-700">
            <h2 class="text-lg font-semibold text-gray-900 dark:text-gray-100">
              Rule: <span class="font-mono text-blue-600 dark:text-blue-400">{props.details!.ruleName}</span>
            </h2>
            <button
              onClick={props.onClose}
              class="text-gray-500 hover:text-gray-700 dark:text-gray-400 dark:hover:text-gray-200"
            >
              <svg class="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>

          {/* Content */}
          <div class="p-4 space-y-6">
            {/* Abstract Rule */}
            <section>
              <h3 class="text-sm font-medium text-gray-500 dark:text-gray-400 mb-2">Abstract Rule</h3>
              <div class="bg-gray-50 dark:bg-gray-900 rounded-lg p-4 text-gray-900 dark:text-gray-100">
                {/* Premises */}
                <Show when={props.details!.abstractPremisesLatex.length > 0}>
                  <div class="flex flex-wrap gap-4 justify-center mb-2">
                    <For each={props.details!.abstractPremisesLatex}>
                      {(premise) => (
                        <div class="text-center">
                          <KaTeX latex={premise} />
                        </div>
                      )}
                    </For>
                  </div>
                  <div class="border-b border-gray-400 dark:border-gray-500 mb-2" />
                </Show>
                {/* Conclusion */}
                <div class="text-center">
                  <KaTeX latex={props.details!.abstractConclusionLatex} />
                </div>
              </div>
            </section>

            {/* Actual Conclusion */}
            <section>
              <h3 class="text-sm font-medium text-gray-500 dark:text-gray-400 mb-2">Applied to Sequent</h3>
              <div class="bg-blue-50 dark:bg-blue-900/20 rounded-lg p-4 text-center text-gray-900 dark:text-gray-100">
                <KaTeX latex={props.details!.actualConclusionLatex} />
              </div>
            </section>

            {/* Substitution */}
            <Show when={props.details!.substitution.length > 0}>
              <section>
                <h3 class="text-sm font-medium text-gray-500 dark:text-gray-400 mb-2">Substitution (MGU)</h3>
                <div class="bg-gray-50 dark:bg-gray-900 rounded-lg p-4 text-gray-900 dark:text-gray-100">
                  <div class="space-y-2">
                    <For each={props.details!.substitution}>
                      {(entry) => (
                        <div class="flex items-center gap-2 font-mono text-sm">
                          <span class="text-purple-600 dark:text-purple-400">
                            <KaTeX latex={entry.variableLatex} />
                          </span>
                          <span class="text-gray-500">↦</span>
                          <span class="text-green-600 dark:text-green-400">
                            <KaTeX latex={entry.valueLatex} />
                          </span>
                        </div>
                      )}
                    </For>
                  </div>
                </div>
              </section>
            </Show>

            {/* Instantiated Premises */}
            <Show when={props.details!.instantiatedPremisesLatex.length > 0}>
              <section>
                <h3 class="text-sm font-medium text-gray-500 dark:text-gray-400 mb-2">
                  Resulting Premises ({props.details!.instantiatedPremisesLatex.length})
                </h3>
                <div class="space-y-2">
                  <For each={props.details!.instantiatedPremisesLatex}>
                    {(premise, index) => (
                      <div class="bg-green-50 dark:bg-green-900/20 rounded-lg p-3 text-gray-900 dark:text-gray-100">
                        <span class="text-xs text-gray-500 dark:text-gray-400 mr-2">{index() + 1}.</span>
                        <KaTeX latex={premise} />
                      </div>
                    )}
                  </For>
                </div>
              </section>
            </Show>

            <Show when={props.details!.instantiatedPremisesLatex.length === 0}>
              <section>
                <div class="text-center text-gray-500 dark:text-gray-400 italic">
                  No premises (axiom/leaf rule)
                </div>
              </section>
            </Show>
          </div>

          {/* Footer */}
          <div class="p-4 border-t border-gray-200 dark:border-gray-700 flex justify-end">
            <button
              onClick={props.onClose}
              class="px-4 py-2 bg-gray-100 dark:bg-gray-700 text-gray-700 dark:text-gray-300 rounded hover:bg-gray-200 dark:hover:bg-gray-600 transition-colors"
            >
              Close
            </button>
          </div>
        </div>
      </div>
    </Show>
  );
}
