import { Show, createMemo } from 'solid-js';
import KaTeX from '../math/KaTeX';
import type { PTTree } from '../../../../lib/types';

interface ProofTreeProps {
  tree: PTTree | null;
}

/**
 * Renders a proof tree node recursively
 */
function ProofTreeNode(props: { node: PTTree }) {
  const hasChildren = () => props.node.children && props.node.children.length > 0;

  return (
    <div class="flex flex-col items-center">
      {/* Children (premisses) */}
      <Show when={hasChildren()}>
        <div class="flex gap-4 mb-2">
          {props.node.children.map((child) => (
            <ProofTreeNode node={child} />
          ))}
        </div>
      </Show>

      {/* Inference line and rule name */}
      <div class="relative">
        <Show when={hasChildren()}>
          <div class="border-t-2 border-gray-800 dark:border-gray-200 mb-1" />
        </Show>

        {/* Conclusion */}
        <div class="text-center px-4 py-1">
          <span class="font-mono text-sm">
            {props.node.head.conclusion}
          </span>
        </div>

        {/* Rule name */}
        <span class="absolute -right-2 top-0 transform translate-x-full text-xs text-gray-500 dark:text-gray-400 font-mono">
          {props.node.head.type !== '???' ? props.node.head.type : ''}
        </span>

        {/* Proven indicator */}
        <Show when={props.node.head.proven === 'x'}>
          <span class="absolute -left-2 top-0 transform -translate-x-full text-green-500">
            ✓
          </span>
        </Show>
      </div>
    </div>
  );
}

export default function ProofTree(props: ProofTreeProps) {
  return (
    <Show
      when={props.tree}
      fallback={
        <div class="text-gray-500 dark:text-gray-400 text-sm">
          No proof tree to display
        </div>
      }
    >
      {(tree) => (
        <div class="bg-white dark:bg-gray-800 rounded-lg p-6 overflow-auto">
          <div class="flex justify-center">
            <ProofTreeNode node={tree()} />
          </div>
        </div>
      )}
    </Show>
  );
}
