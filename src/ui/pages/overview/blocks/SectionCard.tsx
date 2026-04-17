/**
 * Storybook-style section card — a titled framed region containing a canvas.
 *
 * Consistent shell used by every overview page for major sections.
 */

import { ParentComponent, Show, JSX } from 'solid-js';

interface Props {
  title: string;
  subtitle?: string;
  rightSlot?: JSX.Element;
}

const SectionCard: ParentComponent<Props> = (props) => {
  return (
    <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
      <div class="px-6 py-4 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700 flex items-start justify-between gap-4">
        <div>
          <h3 class="font-semibold text-gray-900 dark:text-white text-base">{props.title}</h3>
          <Show when={props.subtitle}>
            <p class="text-sm text-gray-500 dark:text-gray-400 mt-1.5 leading-relaxed max-w-3xl">{props.subtitle}</p>
          </Show>
        </div>
        <Show when={props.rightSlot}>{props.rightSlot}</Show>
      </div>
      <div class="p-6">{props.children}</div>
    </section>
  );
};

export default SectionCard;
