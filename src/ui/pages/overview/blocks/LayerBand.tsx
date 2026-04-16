/**
 * Horizontal band representing one layer within a stack.
 *
 * Used by the Trust Stack columns and by deep-dive layer diagrams
 * (Prover, Forward Engine). Trust color comes from the layer; components
 * inside follow their own trust (which usually matches but can differ
 * where a layer contains kernel-trust items at the bottom).
 */

import { For } from 'solid-js';
import type { Layer, Component } from '../data/types';
import { TRUST_COLORS } from '../data/palette';
import ComponentBox from './ComponentBox';
import { getComponent } from '../data/components';

interface Props {
  layer: Layer;
  onSelect?: (c: Component) => void;
  selectedId?: string;
  /** Show layer name label on the left rather than top. */
  horizontal?: boolean;
  /** Compact mode — smaller component boxes for tight stacks. */
  compact?: boolean;
}

export default function LayerBand(props: Props) {
  const trust = () => TRUST_COLORS[props.layer.trust];
  const components = () =>
    props.layer.componentIds.map(id => getComponent(id)).filter(Boolean) as Component[];

  return (
    <div class={`rounded-lg border ${trust().border} ${trust().bg} p-3`}>
      <div class="flex items-baseline justify-between mb-2">
        <div>
          <h4 class={`font-bold text-sm ${trust().text}`}>{props.layer.name}</h4>
          <p class="text-[11px] text-gray-600 dark:text-gray-400 mt-0.5">{props.layer.role}</p>
        </div>
        <span class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-500">
          {components().length} {components().length === 1 ? 'module' : 'modules'}
        </span>
      </div>
      <div class={`grid gap-2 ${props.compact ? 'grid-cols-2 sm:grid-cols-3' : 'grid-cols-1 sm:grid-cols-2'}`}>
        <For each={components()}>
          {(c) => (
            <ComponentBox
              component={c}
              onSelect={props.onSelect}
              selected={props.selectedId === c.id}
              compact={props.compact}
            />
          )}
        </For>
      </div>
    </div>
  );
}
