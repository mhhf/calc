import { ErrorBoundary as SolidErrorBoundary, ParentComponent } from 'solid-js';

interface ErrorFallbackProps {
  error: Error;
  reset: () => void;
}

function ErrorFallback(props: ErrorFallbackProps) {
  return (
    <div class="p-6 bg-red-50 dark:bg-red-900/20 border border-red-200 dark:border-red-800 rounded-lg">
      <h3 class="text-lg font-semibold text-red-800 dark:text-red-200 mb-2">
        Something went wrong
      </h3>
      <pre class="text-sm text-red-700 dark:text-red-300 bg-red-100 dark:bg-red-900/40 p-3 rounded overflow-auto mb-4">
        {props.error.message}
      </pre>
      <button
        onClick={props.reset}
        class="px-4 py-2 bg-red-600 hover:bg-red-700 text-white rounded-lg transition-colors"
      >
        Try again
      </button>
    </div>
  );
}

const ErrorBoundary: ParentComponent = (props) => {
  return (
    <SolidErrorBoundary
      fallback={(err, reset) => <ErrorFallback error={err} reset={reset} />}
    >
      {props.children}
    </SolidErrorBoundary>
  );
};

export default ErrorBoundary;
