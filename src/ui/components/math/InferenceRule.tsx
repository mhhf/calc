import { createMemo, Show } from 'solid-js';
import KaTeX from './KaTeX';
import type { Rule } from '../../../../lib/types';

interface InferenceRuleProps {
  rule: Rule;
  parser?: { parse: (s: string) => unknown };
}

/**
 * Prettify metavariables in LaTeX output
 * Converts: ?X -> \Gamma, F?A -> A, -- -> \cdot
 */
function prettifyMetavars(latex: string): string {
  return latex
    .replace(/\?X/g, '\\Gamma')
    .replace(/\?Y/g, '\\Delta')
    .replace(/\?Z/g, '\\Sigma')
    .replace(/F\?([A-Z])/g, '$1')
    .replace(/S\?([A-Z])/g, '$1')
    .replace(/--/g, '\\cdot');
}

/**
 * Parse rule string and extract premisses and conclusion
 */
function parseRuleString(ruleStr: string): { premisses: string[]; conclusion: string } | null {
  // Rules are formatted like: "premise1, premise2 |- conclusion"
  // or multiple rules separated by ;
  const parts = ruleStr.split(/\s*;\s*/);
  if (parts.length === 0) return null;

  // First part is usually the conclusion pattern
  const conclusion = parts[0];
  const premisses = parts.slice(1);

  return { premisses, conclusion };
}

export default function InferenceRule(props: InferenceRuleProps) {
  const ruleData = createMemo(() => {
    const rule = props.rule;
    if (!rule) return null;

    // Get LaTeX representation if available
    let latex = rule.latex || rule.ascii || '';

    // For display, we show the rule name and its ASCII/LaTeX
    return {
      name: rule.ruleName,
      ctx: rule.ctxName,
      latex: prettifyMetavars(latex),
      ascii: rule.ascii || '',
      polarity: rule.polarity,
      invertable: rule.invertable,
      unused: rule._unused_by_proofstate,
    };
  });

  return (
    <Show when={ruleData()}>
      {(data) => (
        <div
          class="rule-card"
          classList={{
            'opacity-60': data().unused,
          }}
        >
          <div class="flex items-start justify-between mb-2">
            <div>
              <span class="text-xs font-medium text-gray-500 dark:text-gray-400">
                {data().ctx}
              </span>
              <h3 class="font-mono text-sm font-semibold text-gray-900 dark:text-white">
                {data().name}
              </h3>
            </div>
            <div class="flex gap-1">
              <Show when={data().polarity}>
                <span
                  class="px-2 py-0.5 text-xs rounded"
                  classList={{
                    'bg-green-100 text-green-800 dark:bg-green-900/30 dark:text-green-400':
                      data().polarity === 'positive',
                    'bg-red-100 text-red-800 dark:bg-red-900/30 dark:text-red-400':
                      data().polarity === 'negative',
                  }}
                >
                  {data().polarity}
                </span>
              </Show>
              <Show when={data().invertable}>
                <span class="px-2 py-0.5 text-xs bg-blue-100 text-blue-800 dark:bg-blue-900/30 dark:text-blue-400 rounded">
                  inv
                </span>
              </Show>
            </div>
          </div>

          <Show
            when={data().latex}
            fallback={
              <div class="font-mono text-sm text-gray-700 dark:text-gray-300">
                {data().ascii || '(no syntax)'}
              </div>
            }
          >
            <div class="text-center py-2">
              <KaTeX latex={data().latex} />
            </div>
          </Show>
        </div>
      )}
    </Show>
  );
}
