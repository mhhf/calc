import { ParentComponent } from 'solid-js';
import { darkMode, toggleDarkMode } from '../../state/ui';

const Shell: ParentComponent = (props) => {
  return (
    <div class={`min-h-screen flex flex-col ${darkMode() ? 'dark' : ''}`}>
      <header class="bg-white dark:bg-gray-800 border-b border-gray-200 dark:border-gray-700 px-4 py-3">
        <div class="max-w-7xl mx-auto flex items-center justify-between">
          <div class="flex items-center gap-3">
            <h1 class="text-xl font-bold text-gray-900 dark:text-white">
              CALC
            </h1>
            <span class="text-sm text-gray-500 dark:text-gray-400">
              Linear Logic Proof Assistant
            </span>
          </div>
          <button
            onClick={toggleDarkMode}
            class="p-2 rounded-lg text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-700 transition-colors"
            title="Toggle dark mode"
          >
            {darkMode() ? (
              <svg class="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 3v1m0 16v1m9-9h-1M4 12H3m15.364 6.364l-.707-.707M6.343 6.343l-.707-.707m12.728 0l-.707.707M6.343 17.657l-.707.707M16 12a4 4 0 11-8 0 4 4 0 018 0z" />
              </svg>
            ) : (
              <svg class="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M20.354 15.354A9 9 0 018.646 3.646 9.003 9.003 0 0012 21a9.003 9.003 0 008.354-5.646z" />
              </svg>
            )}
          </button>
        </div>
      </header>
      <div class="flex-1 flex flex-col bg-gray-50 dark:bg-gray-900">
        {props.children}
      </div>
    </div>
  );
};

export default Shell;
