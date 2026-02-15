import { For, Show, createMemo } from 'solid-js';
import InferenceRule from './InferenceRule';
import type { Rule } from '../../../../lib/types';

interface RuleGridProps {
  rules: Rule[];
  groupBy?: 'ctx' | 'none';
}

export default function RuleGrid(props: RuleGridProps) {
  const groupedRules = createMemo(() => {
    if (props.groupBy === 'none') {
      return { 'All Rules': props.rules };
    }

    // Group by context name
    const groups: Record<string, Rule[]> = {};
    for (const rule of props.rules) {
      const key = rule.ctxName || 'Other';
      if (!groups[key]) groups[key] = [];
      groups[key].push(rule);
    }
    return groups;
  });

  return (
    <div class="space-y-8">
      <For each={Object.entries(groupedRules())}>
        {([groupName, rules]) => (
          <section>
            <Show when={props.groupBy !== 'none'}>
              <h2 class="text-lg font-bold text-gray-900 dark:text-white mb-4 pb-2 border-b border-gray-200 dark:border-gray-700">
                {groupName}
                <span class="ml-2 text-sm font-normal text-gray-500 dark:text-gray-400">
                  ({rules.length} rules)
                </span>
              </h2>
            </Show>
            <div class="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 xl:grid-cols-4 gap-4">
              <For each={rules}>
                {(rule) => <InferenceRule rule={rule} />}
              </For>
            </div>
          </section>
        )}
      </For>
    </div>
  );
}
