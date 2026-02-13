import { ParentProps } from "solid-js";
import { A } from "@solidjs/router";

export default function DevLayout(props: ParentProps) {
  return (
    <div class="min-h-screen bg-white">
      <nav class="bg-gray-50 border-b border-gray-200 px-6 py-3">
        <div class="max-w-4xl mx-auto flex items-center justify-between">
          <div class="flex items-center space-x-4">
            <A href="/" class="text-blue-600 hover:text-blue-800 font-medium">
              ← CALC App
            </A>
            <span class="text-gray-400">|</span>
            <A href="/dev" class="text-gray-900 font-semibold">
              Dev Docs
            </A>
          </div>
        </div>
      </nav>

      <main class="max-w-4xl mx-auto px-6 py-8">
        {props.children}
      </main>
    </div>
  );
}
