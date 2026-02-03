import { For, Show, createSignal } from 'solid-js';
import KaTeX from '../math/KaTeX';
import SequentRule from '../math/SequentRule';
import { type ApplicableRule, sequentToLatex } from '../../lib/proofLogicV2';

interface RuleSelectorProps {
  sequentLatex: string;
  applicableRules: ApplicableRule[];
  onApply: (ruleName: string, position: string) => void;
  onCancel: () => void;
  onAutoComplete: () => void;
}

/**
 * Modal panel for selecting which rule to apply.
 * Shows both the abstract rule and a preview of resulting premises.
 */
export default function RuleSelector(props: RuleSelectorProps) {
  // Auto-expand the first rule when there's only one, or leave first rule open
  const getInitialExpanded = () => {
    if (props.applicableRules.length === 1) {
      return props.applicableRules[0].name;
    }
    // If there are axioms (closes branch), expand the first one
    const axiom = props.applicableRules.find(r => r.premises.length === 0);
    if (axiom) return axiom.name;
    return props.applicableRules[0]?.name || null;
  };

  const [expandedRule, setExpandedRule] = createSignal<string | null>(getInitialExpanded());

  // Group rules by category
  const groupedRules = () => {
    const groups: Record<string, ApplicableRule[]> = {};
    for (const rule of props.applicableRules) {
      const cat = rule.category;
      if (!groups[cat]) groups[cat] = [];
      groups[cat].push(rule);
    }
    return groups;
  };

  const categoryLabels: Record<string, string> = {
    RuleZer: 'Axioms',
    RuleCut: 'Cut',
    RuleU: 'Unary Rules',
    RuleBin: 'Binary Rules',
    RuleStruct: 'Structural Rules',
  };

  return (
    <div
      class="fixed inset-0 bg-black/50 flex items-center justify-center z-50"
      onClick={(e) => {
        if (e.target === e.currentTarget) props.onCancel();
      }}
    >
      <div class="bg-white dark:bg-gray-800 rounded-lg shadow-xl max-w-3xl w-full max-h-[85vh] overflow-hidden flex flex-col m-4">
        {/* Header */}
        <div class="px-4 py-3 border-b border-gray-200 dark:border-gray-700 flex-shrink-0">
          <h3 class="text-lg font-bold text-gray-900 dark:text-white">
            Select Rule to Apply
          </h3>
          <div class="mt-2 text-sm text-gray-600 dark:text-gray-400">
            Current goal: <KaTeX latex={props.sequentLatex} />
          </div>
        </div>

        {/* Rules list */}
        <div class="flex-1 overflow-auto p-4">
          <Show
            when={props.applicableRules.length > 0}
            fallback={
              <div class="text-center py-8 text-gray-500 dark:text-gray-400">
                <p>No rules match this sequent.</p>
                <p class="text-sm mt-2">Try using Auto-complete or check the sequent structure.</p>
              </div>
            }
          >
            <For each={Object.entries(groupedRules())}>
              {([category, rules]) => (
                <div class="mb-6">
                  <h4 class="text-sm font-semibold text-gray-500 dark:text-gray-400 uppercase tracking-wide mb-3">
                    {categoryLabels[category] || category}
                  </h4>
                  <div class="space-y-3">
                    <For each={rules}>
                      {(rule) => (
                        <RuleCard
                          rule={rule}
                          isExpanded={expandedRule() === rule.name}
                          onToggle={() => setExpandedRule(
                            expandedRule() === rule.name ? null : rule.name
                          )}
                          onApply={() => props.onApply(rule.name, rule.position)}
                        />
                      )}
                    </For>
                  </div>
                </div>
              )}
            </For>
          </Show>
        </div>

        {/* Footer */}
        <div class="px-4 py-3 border-t border-gray-200 dark:border-gray-700 flex-shrink-0 flex justify-between">
          <button
            onClick={props.onAutoComplete}
            class="px-4 py-2 bg-green-600 text-white rounded-lg hover:bg-green-700 transition-colors flex items-center gap-2"
          >
            <svg class="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M13 10V3L4 14h7v7l9-11h-7z" />
            </svg>
            Auto-complete
          </button>
          <button
            onClick={props.onCancel}
            class="px-4 py-2 text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-700 rounded-lg transition-colors"
          >
            Cancel
          </button>
        </div>
      </div>
    </div>
  );
}

interface RuleCardProps {
  rule: ApplicableRule;
  isExpanded: boolean;
  onToggle: () => void;
  onApply: () => void;
}

function RuleCard(props: RuleCardProps) {
  // Get a short preview of premises for the header
  const premisePreview = () => {
    if (props.rule.premises.length === 0) {
      return { label: 'axiom', color: 'text-green-600 dark:text-green-400' };
    }
    if (props.rule.splitContext) {
      return { label: 'splits context', color: 'text-amber-600 dark:text-amber-400' };
    }
    return { label: `${props.rule.premises.length} premise${props.rule.premises.length > 1 ? 's' : ''}`, color: 'text-gray-500 dark:text-gray-400' };
  };

  return (
    <div
      class="border rounded-lg overflow-hidden transition-all"
      classList={{
        'border-gray-200 dark:border-gray-700': !props.isExpanded,
        'border-blue-400 dark:border-blue-600 ring-1 ring-blue-400 dark:ring-blue-600': props.isExpanded,
      }}
    >
      {/* Rule header - always visible */}
      <div
        class="px-4 py-3 flex items-center justify-between cursor-pointer transition-colors"
        classList={{
          'bg-gray-50 dark:bg-gray-700/50 hover:bg-gray-100 dark:hover:bg-gray-700': !props.isExpanded,
          'bg-blue-50 dark:bg-blue-900/30': props.isExpanded,
        }}
        onClick={props.onToggle}
      >
        {/* Left side: Rule name and badges */}
        <div class="flex items-center gap-2 flex-wrap">
          <span class="font-mono font-bold text-blue-600 dark:text-blue-400 text-lg">
            {props.rule.name}
          </span>
          <span class={`text-xs font-medium ${premisePreview().color}`}>
            {premisePreview().label}
          </span>
          <Show when={props.rule.splitContext}>
            <span class="inline-flex items-center gap-1 px-2 py-0.5 rounded-full bg-amber-100 dark:bg-amber-900/40 text-amber-700 dark:text-amber-300 text-xs">
              split
            </span>
          </Show>
        </div>

        {/* Right side: Actions */}
        <div class="flex items-center gap-2">
          <button
            onClick={(e) => {
              e.stopPropagation();
              props.onApply();
            }}
            class="px-4 py-1.5 bg-blue-600 text-white text-sm font-medium rounded-lg hover:bg-blue-700 transition-colors shadow-sm"
          >
            Apply
          </button>
          <svg
            class="w-5 h-5 text-gray-400 transition-transform"
            classList={{ 'rotate-180': props.isExpanded }}
            fill="none"
            viewBox="0 0 24 24"
            stroke="currentColor"
          >
            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M19 9l-7 7-7-7" />
          </svg>
        </div>
      </div>

      {/* Expanded details - TOP-DOWN LAYOUT: Abstract Rule → Principal Formula → New Subgoals */}
      <Show when={props.isExpanded}>
        <div class="p-4 space-y-4 border-t border-gray-100 dark:border-gray-700">
          {/* 1. Abstract rule */}
          <Show when={props.rule.ruleStrings.length > 0}>
            <div>
              <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2 uppercase tracking-wide">
                Abstract Rule
              </div>
              <div class="bg-white dark:bg-gray-800 rounded-lg p-3 border border-gray-100 dark:border-gray-700">
                <SequentRule
                  name=""
                  ruleStrings={props.rule.ruleStrings}
                  simplified={true}
                  showAscii={false}
                />
              </div>
            </div>
          </Show>

          {/* 2. Principal formula being decomposed */}
          <Show when={props.rule.principalFormulaLatex}>
            <div>
              <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2 uppercase tracking-wide">
                Decomposing
              </div>
              <div class="bg-blue-50 dark:bg-blue-900/20 rounded-lg px-3 py-2 border border-blue-100 dark:border-blue-800 inline-block">
                <KaTeX latex={props.rule.principalFormulaLatex!} />
              </div>
            </div>
          </Show>

          {/* 3. Context split warning */}
          <Show when={props.rule.splitContext}>
            <div class="bg-amber-50 dark:bg-amber-900/20 border border-amber-200 dark:border-amber-800 rounded-lg p-3">
              <div class="flex items-start gap-2">
                <svg class="w-5 h-5 text-amber-500 flex-shrink-0 mt-0.5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
                </svg>
                <div class="text-sm">
                  <div class="font-medium text-amber-800 dark:text-amber-200">Context Split</div>
                  <div class="text-amber-700 dark:text-amber-300 mt-1">
                    This rule splits the linear context between premises. You'll be able to choose how to distribute resources.
                  </div>
                </div>
              </div>
            </div>
          </Show>

          {/* 4. New subgoals / premises */}
          <div>
            <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2 uppercase tracking-wide">
              {props.rule.premises.length === 0
                ? 'Result'
                : 'New Subgoals'}
            </div>
            <Show
              when={props.rule.premises.length > 0}
              fallback={
                <div class="flex items-center gap-2 text-green-600 dark:text-green-400 text-sm bg-green-50 dark:bg-green-900/20 rounded-lg p-3">
                  <svg class="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                    <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
                  </svg>
                  Closes this branch (no new subgoals)
                </div>
              }
            >
              <div class="space-y-2">
                <For each={props.rule.premises}>
                  {(premise, index) => (
                    <div class="flex items-start gap-3 text-sm">
                      <span
                        class="flex-shrink-0 w-6 h-6 rounded-full bg-gray-200 dark:bg-gray-700 flex items-center justify-center text-xs font-medium text-gray-600 dark:text-gray-300"
                      >
                        {index() + 1}
                      </span>
                      <div class="flex-1 bg-gray-50 dark:bg-gray-900 rounded-lg px-3 py-2 border border-gray-100 dark:border-gray-700">
                        <KaTeX latex={sequentToLatex(premise)} />
                      </div>
                    </div>
                  )}
                </For>
              </div>
            </Show>
          </div>
        </div>
      </Show>
    </div>
  );
}
