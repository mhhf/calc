/**
 * Consistent component visualization used across all views.
 *
 * Same component → same colored box, same name, same click-target. This is
 * the operational meaning of "cross-view component identity" — a ComponentBox
 * with id 'engine.match' looks identical on Trust, Specificity, Atlas, and
 * the Forward Engine deep dive, and clicking it routes the same way.
 */

import { Show, splitProps } from 'solid-js';
import type { Component } from '../data/types';
import { TRUST_COLORS } from '../data/palette';

interface Props {
  component: Component;
  /** Optional click handler — typically opens DetailPanel. */
  onSelect?: (c: Component) => void;
  /** Render only id + trust dot (for tight layouts like specificity tree). */
  compact?: boolean;
  /** Flag the component as currently selected (highlighted ring). */
  selected?: boolean;
  /** Extra classes for the wrapper — for grid/flex sizing. */
  extraClass?: string;
}

export default function ComponentBox(allProps: Props) {
  const [props] = splitProps(allProps, ['component', 'onSelect', 'compact', 'selected', 'extraClass']);
  const trust = () => TRUST_COLORS[props.component.trust];

  const handleClick = () => {
    if (props.onSelect) props.onSelect(props.component);
  };
  const handleKey = (e: KeyboardEvent) => {
    if (props.onSelect && (e.key === 'Enter' || e.key === ' ')) {
      e.preventDefault();
      props.onSelect(props.component);
    }
  };

  return (
    <button
      type="button"
      onClick={handleClick}
      onKeyDown={handleKey}
      tabIndex={props.onSelect ? 0 : -1}
      aria-label={`${props.component.name} — ${props.component.summary}`}
      class={`group relative block w-full text-left rounded-md border ${trust().border} ${trust().bg} transition-shadow hover:shadow-md focus:outline-none focus-visible:ring-2 focus-visible:ring-blue-500 ${props.selected ? 'ring-2 ring-blue-500 shadow-md' : ''} ${props.extraClass ?? ''}`}
    >
      <div class={`absolute left-0 top-0 bottom-0 w-1 rounded-l-md ${trust().dot}`} aria-hidden="true" />
      <Show when={props.compact} fallback={
        <div class={`px-3 py-2 ${trust().text}`}>
          <div class="flex items-center gap-2">
            <span class="font-mono text-[13px] font-semibold truncate">{props.component.name}</span>
          </div>
          <div class="mt-0.5 text-[11px] text-gray-700 dark:text-gray-300 opacity-90 line-clamp-2">
            {props.component.summary}
          </div>
        </div>
      }>
        <div class={`px-2 py-1 ${trust().text}`}>
          <span class="font-mono text-xs font-semibold truncate">{props.component.name}</span>
        </div>
      </Show>
    </button>
  );
}
