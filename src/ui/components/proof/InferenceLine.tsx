import { Show } from 'solid-js';

interface InferenceLineProps {
  ruleName: string;
  width?: string;
}

/**
 * Horizontal inference line between premises and conclusion.
 * Shows the rule name on the right.
 */
export default function InferenceLine(props: InferenceLineProps) {
  return (
    <div class="flex items-center gap-2 my-2">
      <div
        class="flex-1 border-t-2 border-gray-400 dark:border-gray-500"
        style={{ "min-width": props.width || '100px' }}
      />
      <Show when={props.ruleName && props.ruleName !== '???'}>
        <span class="text-xs font-mono text-gray-600 dark:text-gray-400 whitespace-nowrap">
          {props.ruleName}
        </span>
      </Show>
    </div>
  );
}
