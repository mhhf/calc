import { ParentProps } from "solid-js";
import { A } from "@solidjs/router";

// Layout for research pages
export default function ResearchLayout(props: ParentProps) {
  return (
    <div class="min-h-screen bg-gray-950">
      {/* Navigation bar */}
      <nav class="bg-gray-900 border-b border-gray-800 px-6 py-4">
        <div class="max-w-4xl mx-auto flex items-center justify-between">
          <div class="flex items-center space-x-4">
            <A href="/" class="text-blue-400 hover:text-blue-300">
              ← CALC App
            </A>
            <span class="text-gray-600">|</span>
            <A href="/research" class="text-gray-200 font-medium">
              Research Index
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
