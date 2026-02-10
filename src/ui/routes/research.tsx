import { ParentProps } from "solid-js";
import { A } from "@solidjs/router";

// Layout for research pages - GitHub README style (light theme)
export default function ResearchLayout(props: ParentProps) {
  return (
    <div class="min-h-screen bg-white">
      {/* Navigation bar */}
      <nav class="bg-gray-50 border-b border-gray-200 px-6 py-3">
        <div class="max-w-4xl mx-auto flex items-center justify-between">
          <div class="flex items-center space-x-4">
            <A href="/" class="text-blue-600 hover:text-blue-800 font-medium">
              ← CALC App
            </A>
            <span class="text-gray-400">|</span>
            <A href="/research" class="text-gray-900 font-semibold">
              Research Docs
            </A>
          </div>
        </div>
      </nav>

      {/* Content */}
      <main class="max-w-4xl mx-auto px-6 py-8">
        {props.children}
      </main>
    </div>
  );
}
