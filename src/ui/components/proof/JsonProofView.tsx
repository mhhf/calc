import { createMemo, Show } from 'solid-js';
import { SerializedProof } from '../../lib/proofLogic';

interface JsonProofViewProps {
  proof: SerializedProof;
}

/**
 * Displays a serialized proof as formatted JSON.
 * Includes syntax highlighting and copy-to-clipboard functionality.
 */
export default function JsonProofView(props: JsonProofViewProps) {
  const jsonString = createMemo(() => {
    return JSON.stringify(props.proof, null, 2);
  });

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(jsonString());
    } catch (err) {
      // Fallback for older browsers
      const textarea = document.createElement('textarea');
      textarea.value = jsonString();
      document.body.appendChild(textarea);
      textarea.select();
      document.execCommand('copy');
      document.body.removeChild(textarea);
    }
  };

  const handleDownload = () => {
    const blob = new Blob([jsonString()], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `proof-${new Date().toISOString().slice(0, 10)}.json`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  };

  return (
    <div class="space-y-4">
      {/* Header with stats and actions */}
      <div class="flex items-center justify-between flex-wrap gap-4">
        <div class="flex items-center gap-4 text-sm">
          <span class="text-gray-600 dark:text-gray-400">
            <span class="font-medium">{props.proof.stats.totalNodes}</span> nodes
          </span>
          <span class="text-gray-600 dark:text-gray-400">
            <span class="font-medium">{props.proof.stats.maxDepth}</span> depth
          </span>
          <Show when={props.proof.complete}>
            <span class="px-2 py-0.5 bg-green-100 dark:bg-green-900/30 text-green-700 dark:text-green-400 rounded text-xs font-medium">
              Complete
            </span>
          </Show>
          <Show when={!props.proof.complete}>
            <span class="px-2 py-0.5 bg-yellow-100 dark:bg-yellow-900/30 text-yellow-700 dark:text-yellow-400 rounded text-xs font-medium">
              Incomplete
            </span>
          </Show>
          <span class="px-2 py-0.5 bg-purple-100 dark:bg-purple-900/30 text-purple-700 dark:text-purple-400 rounded text-xs font-medium">
            {props.proof.mode}
          </span>
        </div>

        <div class="flex gap-2">
          <button
            onClick={handleCopy}
            class="px-3 py-1.5 text-sm bg-gray-100 dark:bg-gray-700 text-gray-700 dark:text-gray-300 rounded hover:bg-gray-200 dark:hover:bg-gray-600 transition-colors flex items-center gap-1.5"
            title="Copy JSON to clipboard"
          >
            <svg class="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 012 2v2m-6 12h8a2 2 0 002-2v-8a2 2 0 00-2-2h-8a2 2 0 00-2 2v8a2 2 0 002 2z" />
            </svg>
            Copy
          </button>
          <button
            onClick={handleDownload}
            class="px-3 py-1.5 text-sm bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-400 rounded hover:bg-blue-200 dark:hover:bg-blue-800/30 transition-colors flex items-center gap-1.5"
            title="Download as JSON file"
          >
            <svg class="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M4 16v1a3 3 0 003 3h10a3 3 0 003-3v-1m-4-4l-4 4m0 0l-4-4m4 4V4" />
            </svg>
            Download
          </button>
        </div>
      </div>

      {/* JSON content */}
      <div class="relative">
        <pre class="bg-gray-50 dark:bg-gray-900 border border-gray-200 dark:border-gray-700 rounded-lg p-4 overflow-auto max-h-[600px] text-sm font-mono">
          <code class="text-gray-800 dark:text-gray-200 whitespace-pre">
            {jsonString()}
          </code>
        </pre>
      </div>

      {/* Schema info */}
      <details class="text-sm text-gray-600 dark:text-gray-400">
        <summary class="cursor-pointer hover:text-gray-800 dark:hover:text-gray-200">
          JSON Schema Info
        </summary>
        <div class="mt-2 p-3 bg-gray-50 dark:bg-gray-900 rounded border border-gray-200 dark:border-gray-700 space-y-2">
          <p><strong>version:</strong> Schema version (currently "1.0")</p>
          <p><strong>goal:</strong> The sequent being proved</p>
          <p><strong>complete:</strong> Whether all branches are closed</p>
          <p><strong>mode:</strong> "unfocused" or "focused" proof mode</p>
          <p><strong>tree:</strong> Recursive proof tree structure</p>
          <p class="mt-2 text-xs">Each node contains: rule, position, conclusion (sequent), focus state, resources, and premises.</p>
        </div>
      </details>
    </div>
  );
}
