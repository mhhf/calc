/**
 * Colored axis badge (Trust / Specificity / Stage / Mode).
 *
 * Uses the shared palette so that the same axis-value wears the same color
 * in every view — the central cross-view identity signal.
 */

import { Show } from 'solid-js';
import type { Trust, Specificity, Stage } from '../data/types';
import { TRUST_COLORS, SPECIFICITY_COLORS, STAGE_COLORS } from '../data/palette';

export function TrustBadge(props: { trust: Trust; compact?: boolean }) {
  const p = () => TRUST_COLORS[props.trust];
  return (
    <span
      class={`inline-flex items-center gap-1.5 rounded px-2 py-0.5 text-xs font-medium ${p().bg} ${p().text} ${p().border} border`}
      title={`Trust level: ${p().label}`}
    >
      <span class={`h-1.5 w-1.5 rounded-full ${p().dot}`} aria-hidden="true" />
      <Show when={!props.compact}>{p().label}</Show>
    </span>
  );
}

export function SpecificityBadge(props: { specificity: Specificity; compact?: boolean }) {
  const p = () => SPECIFICITY_COLORS[props.specificity];
  return (
    <span
      class={`inline-flex items-center rounded px-2 py-0.5 text-xs font-medium ${p().bg} ${p().text} ${p().border} border`}
      title={`Specificity: ${p().label}`}
    >
      <Show when={!props.compact} fallback={p().label.slice(0, 1)}>{p().label}</Show>
    </span>
  );
}

export function StageBadge(props: { stage: Stage }) {
  const p = () => STAGE_COLORS[props.stage];
  return (
    <span
      class={`inline-flex items-center rounded px-1.5 py-0.5 text-[11px] font-medium uppercase tracking-wide ${p().bg} ${p().text} ${p().border} border`}
    >
      {p().label}
    </span>
  );
}

export function ModeBadge(props: { mode: string }) {
  const palette: Record<string, string> = {
    backward: 'bg-emerald-100 text-emerald-800 dark:bg-emerald-900/30 dark:text-emerald-300',
    forward: 'bg-blue-100 text-blue-800 dark:bg-blue-900/30 dark:text-blue-300',
    symbolic: 'bg-purple-100 text-purple-800 dark:bg-purple-900/30 dark:text-purple-300',
    certification: 'bg-orange-100 text-orange-800 dark:bg-orange-900/30 dark:text-orange-300',
  };
  return (
    <span class={`inline-flex items-center rounded px-1.5 py-0.5 text-[11px] font-medium ${palette[props.mode] ?? 'bg-gray-100 text-gray-600'}`}>
      {props.mode}
    </span>
  );
}
