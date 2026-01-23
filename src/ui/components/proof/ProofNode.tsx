import { Show } from 'solid-js';
import KaTeX from '../math/KaTeX';

interface ProofNodeProps {
  sequentLatex: string;
  sequentAscii: string;
  ruleName: string;
  isLeaf: boolean;
  isProven: boolean;
  isSelected: boolean;
  isClickable: boolean;
  onClick: () => void;
}

/**
 * A single node in the proof tree, displaying a sequent.
 * Clickable when unproven to select for rule application.
 */
export default function ProofNode(props: ProofNodeProps) {
  const statusIcon = () => {
    if (props.ruleName === '???') return '?';
    if (props.isProven) return '✓';
    return '○';
  };

  const statusColor = () => {
    if (props.ruleName === '???') return 'text-blue-500';
    if (props.isProven) return 'text-green-500';
    return 'text-gray-400';
  };

  return (
    <div
      class="proof-node relative inline-block"
      classList={{
        'cursor-pointer': props.isClickable,
        'hover:bg-blue-50 dark:hover:bg-blue-900/20': props.isClickable,
      }}
      onClick={() => props.isClickable && props.onClick()}
    >
      <div
        class="px-3 py-2 rounded-lg border-2 transition-all"
        classList={{
          'border-blue-500 bg-blue-50 dark:bg-blue-900/30': props.isSelected,
          'border-blue-300 dark:border-blue-600': props.ruleName === '???' && !props.isSelected,
          'border-green-300 dark:border-green-600 bg-green-50/50 dark:bg-green-900/20': props.isProven && !props.isSelected,
          'border-gray-200 dark:border-gray-700': props.ruleName !== '???' && !props.isProven && !props.isSelected,
        }}
      >
        {/* Status indicator */}
        <span
          class={`absolute -top-2 -right-2 w-5 h-5 rounded-full flex items-center justify-center text-xs font-bold ${statusColor()}`}
          classList={{
            'bg-blue-100 dark:bg-blue-800': props.ruleName === '???',
            'bg-green-100 dark:bg-green-800': props.isProven,
            'bg-gray-100 dark:bg-gray-700': props.ruleName !== '???' && !props.isProven,
          }}
        >
          {statusIcon()}
        </span>

        {/* Sequent */}
        <div class="text-center">
          <KaTeX latex={props.sequentLatex} />
        </div>
      </div>

      {/* Rule name (shown below for proven nodes) */}
      <Show when={props.ruleName !== '???'}>
        <div class="text-center mt-1">
          <span class="text-xs font-mono text-gray-500 dark:text-gray-400">
            ({props.ruleName})
          </span>
        </div>
      </Show>
    </div>
  );
}
