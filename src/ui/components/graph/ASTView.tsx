import { createMemo, Show } from 'solid-js';
import type { TreeNode } from '../../../../lib/types/node';

interface ASTViewProps {
  tree: TreeNode | null;
}

/**
 * Renders a simple tree view of the AST
 * This is a fallback for when solid-g6 is not needed
 */
function TreeNodeView(props: { node: TreeNode; depth?: number }) {
  const depth = props.depth ?? 0;
  const indent = depth * 20;
  // Handle leaf nodes where children may be undefined
  const children = () => props.node.children || [];

  return (
    <div style={{ "margin-left": `${indent}px` }}>
      <div class="flex items-center gap-2 py-1">
        <span class="text-gray-400 dark:text-gray-500">
          {children().length > 0 ? '├─' : '└─'}
        </span>
        <span class="font-mono text-sm">
          <span class="text-blue-600 dark:text-blue-400">
            {props.node.head.constr || props.node.head.name || '?'}
          </span>
          <Show when={props.node.head.ascii}>
            <span class="text-gray-500 dark:text-gray-400 ml-2">
              {props.node.head.ascii}
            </span>
          </Show>
        </span>
      </div>
      <Show when={children().length > 0}>
        <div>
          {children().map((child) => (
            <TreeNodeView node={child} depth={depth + 1} />
          ))}
        </div>
      </Show>
    </div>
  );
}

export default function ASTView(props: ASTViewProps) {
  return (
    <Show
      when={props.tree}
      fallback={
        <div class="text-gray-500 dark:text-gray-400 text-sm">
          No AST to display
        </div>
      }
    >
      {(tree) => (
        <div class="bg-white dark:bg-gray-800 rounded-lg p-4 font-mono text-sm overflow-auto max-h-96">
          <TreeNodeView node={tree()} />
        </div>
      )}
    </Show>
  );
}
