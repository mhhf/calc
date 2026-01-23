interface ProofControlsProps {
  onUndo: () => void;
  onRedo: () => void;
  onReset: () => void;
  canUndo: boolean;
  canRedo: boolean;
  provenCount: number;
  unprovenCount: number;
  isComplete: boolean;
}

/**
 * Control buttons for the proof: undo, redo, reset, and status display.
 */
export default function ProofControls(props: ProofControlsProps) {
  return (
    <div class="flex items-center justify-between gap-4 p-3 bg-gray-50 dark:bg-gray-800/50 rounded-lg border border-gray-200 dark:border-gray-700">
      {/* Left: Action buttons */}
      <div class="flex items-center gap-2">
        {/* Undo */}
        <button
          onClick={props.onUndo}
          disabled={!props.canUndo}
          class="flex items-center gap-1 px-3 py-1.5 rounded text-sm font-medium transition-colors"
          classList={{
            'bg-gray-200 dark:bg-gray-700 text-gray-700 dark:text-gray-300 hover:bg-gray-300 dark:hover:bg-gray-600': props.canUndo,
            'bg-gray-100 dark:bg-gray-800 text-gray-400 dark:text-gray-600 cursor-not-allowed': !props.canUndo,
          }}
          title="Undo (Ctrl+Z)"
        >
          <svg class="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M3 10h10a8 8 0 018 8v2M3 10l6 6m-6-6l6-6" />
          </svg>
          Undo
        </button>

        {/* Redo */}
        <button
          onClick={props.onRedo}
          disabled={!props.canRedo}
          class="flex items-center gap-1 px-3 py-1.5 rounded text-sm font-medium transition-colors"
          classList={{
            'bg-gray-200 dark:bg-gray-700 text-gray-700 dark:text-gray-300 hover:bg-gray-300 dark:hover:bg-gray-600': props.canRedo,
            'bg-gray-100 dark:bg-gray-800 text-gray-400 dark:text-gray-600 cursor-not-allowed': !props.canRedo,
          }}
          title="Redo (Ctrl+Y)"
        >
          <svg class="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M21 10h-10a8 8 0 00-8 8v2M21 10l-6 6m6-6l-6-6" />
          </svg>
          Redo
        </button>

        {/* Divider */}
        <div class="w-px h-6 bg-gray-300 dark:bg-gray-600 mx-1" />

        {/* Reset */}
        <button
          onClick={props.onReset}
          class="flex items-center gap-1 px-3 py-1.5 rounded text-sm font-medium bg-red-100 dark:bg-red-900/30 text-red-700 dark:text-red-400 hover:bg-red-200 dark:hover:bg-red-900/50 transition-colors"
          title="Reset proof"
        >
          <svg class="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
          </svg>
          Reset
        </button>
      </div>

      {/* Right: Status */}
      <div class="flex items-center gap-4">
        {/* Progress indicator */}
        <div class="flex items-center gap-2 text-sm">
          <span class="text-green-600 dark:text-green-400">
            {props.provenCount} proven
          </span>
          <span class="text-gray-400">/</span>
          <span class="text-blue-600 dark:text-blue-400">
            {props.unprovenCount} remaining
          </span>
        </div>

        {/* Completion badge */}
        {props.isComplete && (
          <span class="flex items-center gap-1 px-3 py-1 bg-green-100 dark:bg-green-900/30 text-green-700 dark:text-green-400 rounded-full text-sm font-medium">
            <svg class="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M5 13l4 4L19 7" />
            </svg>
            Complete!
          </span>
        )}
      </div>
    </div>
  );
}
