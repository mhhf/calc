export default function Loading() {
  return (
    <div class="flex items-center justify-center p-8">
      <div class="flex flex-col items-center gap-3">
        <div class="w-8 h-8 border-4 border-blue-500 border-t-transparent rounded-full animate-spin" />
        <span class="text-sm text-gray-500 dark:text-gray-400">Loading...</span>
      </div>
    </div>
  );
}
