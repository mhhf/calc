/**
 * Page header shell used by every overview page.
 */

import { ParentComponent, Show, JSX } from 'solid-js';

interface Props {
  glyph?: string;
  title: string;
  question?: string;
  subtitle?: string;
  accentClass?: string;
  rightSlot?: JSX.Element;
}

const Page: ParentComponent<Props> = (props) => {
  return (
    <div class="max-w-7xl mx-auto p-6 space-y-6 text-gray-900 dark:text-gray-100">
      <header class="flex items-start justify-between gap-6 flex-wrap">
        <div class="flex items-start gap-4">
          <Show when={props.glyph}>
            <div class={`shrink-0 h-10 w-10 rounded-lg grid place-items-center font-bold text-2xl ${props.accentClass ?? 'text-blue-600 dark:text-blue-400'} bg-gray-100 dark:bg-gray-800`}>
              {props.glyph}
            </div>
          </Show>
          <div>
            <h2 class="text-2xl font-bold text-gray-900 dark:text-white">{props.title}</h2>
            <Show when={props.question}>
              <p class="text-sm font-medium text-gray-500 dark:text-gray-400 mt-1 italic">{props.question}</p>
            </Show>
            <Show when={props.subtitle}>
              <p class="text-gray-600 dark:text-gray-300 mt-2 max-w-3xl">{props.subtitle}</p>
            </Show>
          </div>
        </div>
        <Show when={props.rightSlot}>{props.rightSlot}</Show>
      </header>
      {props.children}
    </div>
  );
};

export default Page;
