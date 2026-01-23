import { Show } from 'solid-js';

interface FormulaInputProps {
  value: string;
  onInput: (value: string) => void;
  error?: string | null;
  placeholder?: string;
}

export default function FormulaInput(props: FormulaInputProps) {
  return (
    <div class="space-y-2">
      <div class="relative">
        <input
          type="text"
          value={props.value}
          onInput={(e) => props.onInput(e.currentTarget.value)}
          placeholder={props.placeholder ?? 'Enter a formula (e.g., A -o B, A * B, !A)'}
          class="formula-input"
          classList={{ error: !!props.error }}
          spellcheck={false}
          autocomplete="off"
        />
        <Show when={props.value}>
          <button
            onClick={() => props.onInput('')}
            class="absolute right-3 top-1/2 -translate-y-1/2 text-gray-400 hover:text-gray-600 dark:hover:text-gray-300"
            title="Clear"
          >
            <svg class="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        </Show>
      </div>
      <Show when={props.error}>
        <div class="text-sm text-red-600 dark:text-red-400 font-mono bg-red-50 dark:bg-red-900/20 px-3 py-2 rounded">
          {props.error}
        </div>
      </Show>
    </div>
  );
}
