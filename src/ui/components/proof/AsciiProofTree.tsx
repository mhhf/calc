import { createMemo, Show } from 'solid-js';
import { type SerializedProof, type SerializedProofNode } from '../../lib/proofLogic';

interface AsciiProofTreeProps {
  proof: SerializedProof;
}

/**
 * Renders a proof tree in tree-style ASCII format (like the `tree` command).
 *
 * Example output:
 * ```
 * P * Q |- P * Q  (Tensor_L)
 * └── P, Q |- P * Q  (Tensor_R)
 *     ├── P |- P  (Id) ✓
 *     └── Q |- Q  (Id) ✓
 * ```
 *
 * - Goal at root, premises as children (subgoals)
 * - Focus shown with [brackets] around focused formula
 * - ✓ = proven leaf, ? = open goal
 */
export default function AsciiProofTree(props: AsciiProofTreeProps) {
  const asciiTree = createMemo(() => {
    return renderTree(props.proof.tree);
  });

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(asciiTree());
    } catch (err) {
      const textarea = document.createElement('textarea');
      textarea.value = asciiTree();
      document.body.appendChild(textarea);
      textarea.select();
      document.execCommand('copy');
      document.body.removeChild(textarea);
    }
  };

  return (
    <div class="space-y-4">
      {/* Header */}
      <div class="flex items-center justify-between">
        <div class="text-sm text-gray-600 dark:text-gray-400">
          <Show when={props.proof.complete}>
            <span class="text-green-600 dark:text-green-400 font-medium">✓ Complete</span>
          </Show>
          <Show when={!props.proof.complete}>
            <span class="text-yellow-600 dark:text-yellow-400 font-medium">○ Incomplete</span>
          </Show>
          <span class="ml-3">
            {props.proof.stats.provenNodes} proven, {props.proof.stats.unprovenNodes} open
          </span>
        </div>
        <button
          onClick={handleCopy}
          class="px-3 py-1.5 text-sm bg-gray-100 dark:bg-gray-700 text-gray-700 dark:text-gray-300 rounded hover:bg-gray-200 dark:hover:bg-gray-600 transition-colors"
        >
          Copy
        </button>
      </div>

      {/* ASCII tree */}
      <pre class="bg-gray-50 dark:bg-gray-900 border border-gray-200 dark:border-gray-700 rounded-lg p-4 overflow-auto font-mono text-sm whitespace-pre text-gray-900 dark:text-gray-100">
        {asciiTree()}
      </pre>
    </div>
  );
}

/**
 * Format a single node as a string: "sequent  (rule) status"
 */
function formatNode(node: SerializedProofNode): string {
  const sequent = node.conclusion.ascii;

  // Status marker
  let status = '';
  if (node.rule === '???') {
    status = ' ?';
  } else if (node.premises.length === 0) {
    status = ' ✓';
  }

  // Rule name (skip for unproven nodes)
  const rule = node.rule === '???' ? '' : `  (${node.rule})`;

  return `${sequent}${rule}${status}`;
}

/**
 * Render the entire tree as a string.
 */
function renderTree(root: SerializedProofNode): string {
  const lines: string[] = [];

  // Recursive helper
  function render(node: SerializedProofNode, prefix: string, childPrefix: string): void {
    lines.push(prefix + formatNode(node));

    const children = node.premises;
    for (let i = 0; i < children.length; i++) {
      const isLast = i === children.length - 1;
      const connector = isLast ? '└── ' : '├── ';
      const nextChildPrefix = isLast ? '    ' : '│   ';

      render(children[i], childPrefix + connector, childPrefix + nextChildPrefix);
    }
  }

  // Start with root (no prefix)
  render(root, '', '');

  return lines.join('\n');
}
