/**
 * Specificity Tree view — horizontal tree of CALC's domain layering.
 *
 * Each node shows:
 *   - specificity badge
 *   - summary
 *   - components at this level (click → DetailPanel)
 *   - strategies / optimizations / chips specific to this level
 *
 * Collapse/expand children per node. Planned nodes render dim.
 */

import { createSignal, For, Show } from 'solid-js';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import DetailPanel from './blocks/DetailPanel';
import ComponentBox from './blocks/ComponentBox';
import { SpecificityBadge } from './blocks/Badge';
import { useHashComponent } from './blocks/useHashComponent';
import { VIEWS } from './data/meta';
import { SPECIFICITY_COLORS } from './data/palette';
import type { Component, Specificity } from './data/types';
import { getComponent } from './data/components';
import { SPEC_TREE, type SpecNode } from './data/specTree';

function AxisLegend() {
  const order: Specificity[] = ['framework', 'logic', 'theory', 'program', 'instance'];
  return (
    <div class="flex items-center gap-1 text-xs overflow-x-auto">
      <span class="uppercase tracking-wider font-semibold text-gray-500 dark:text-gray-400 text-[10px] whitespace-nowrap">Specificity →</span>
      <For each={order}>{(s) => <SpecificityBadge specificity={s} />}</For>
    </div>
  );
}

/** Pill of strategy / opt / chip bullets, coded to context. */
function FactRow(props: { label: string; facts?: string[]; tone: 'strategy' | 'optimization' | 'chip' }) {
  const palette = {
    strategy:     'bg-blue-50 dark:bg-blue-900/20 text-blue-800 dark:text-blue-200 border-blue-200 dark:border-blue-700',
    optimization: 'bg-orange-50 dark:bg-orange-900/20 text-orange-800 dark:text-orange-200 border-orange-200 dark:border-orange-700',
    chip:         'bg-purple-50 dark:bg-purple-900/20 text-purple-800 dark:text-purple-200 border-purple-200 dark:border-purple-700',
  }[props.tone];
  return (
    <Show when={props.facts && props.facts.length > 0}>
      <div class="flex flex-wrap items-baseline gap-1.5">
        <span class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 w-20 shrink-0">{props.label}</span>
        <For each={props.facts}>
          {(f) => <span class={`text-[11px] px-1.5 py-0.5 rounded border ${palette}`}>{f}</span>}
        </For>
      </div>
    </Show>
  );
}

interface TreeRowProps {
  node: SpecNode;
  depth: number;
  onSelect: (c: Component) => void;
  selectedId?: string;
  isLastInSiblings: boolean;
  prefix: boolean[]; // true = parent had more siblings below ⇒ draw vertical at this depth
}

function TreeRow(props: TreeRowProps) {
  const [expanded, setExpanded] = createSignal(true);
  const p = () => SPECIFICITY_COLORS[props.node.specificity];
  const hasChildren = () => (props.node.children?.length ?? 0) > 0;

  const components = () =>
    props.node.componentIds.map(id => getComponent(id)).filter(Boolean) as Component[];

  return (
    <div>
      <div class="flex items-start gap-0">
        {/* Prefix lines for ancestor siblings */}
        <For each={props.prefix}>
          {(draw) => (
            <div class="w-6 shrink-0 self-stretch relative">
              <Show when={draw}>
                <div class="absolute left-3 top-0 bottom-0 border-l border-gray-300 dark:border-gray-600" />
              </Show>
            </div>
          )}
        </For>
        {/* Connector at this depth (skip for root) */}
        <Show when={props.depth > 0}>
          <div class="w-6 shrink-0 self-stretch relative">
            <div
              class={`absolute left-3 top-0 border-l border-gray-300 dark:border-gray-600 ${props.isLastInSiblings ? 'h-5' : 'bottom-0'}`}
            />
            <div class="absolute left-3 top-5 w-3 border-t border-gray-300 dark:border-gray-600" />
          </div>
        </Show>

        {/* Node card */}
        <div
          class={`flex-1 rounded-lg border ${p().border} ${p().bg} p-3 mb-2 ${props.node.planned ? 'opacity-60' : ''}`}
        >
          <div class="flex items-baseline justify-between gap-2 flex-wrap">
            <div class="flex items-baseline gap-2 flex-wrap">
              <Show when={hasChildren()}>
                <button
                  type="button"
                  onClick={() => setExpanded(!expanded())}
                  aria-label={expanded() ? 'Collapse' : 'Expand'}
                  class="text-gray-500 dark:text-gray-400 hover:text-gray-800 dark:hover:text-gray-200 font-mono text-sm w-4"
                >
                  {expanded() ? '▾' : '▸'}
                </button>
              </Show>
              <h4 class={`font-bold ${p().text}`}>{props.node.name}</h4>
              <SpecificityBadge specificity={props.node.specificity} />
              <Show when={props.node.planned}>
                <span class="text-[10px] uppercase tracking-wider px-1.5 py-0.5 rounded bg-gray-200 dark:bg-gray-700 text-gray-600 dark:text-gray-300">
                  Planned
                </span>
              </Show>
            </div>
          </div>
          <p class="text-sm text-gray-700 dark:text-gray-300 mt-1">{props.node.summary}</p>

          <div class="mt-3 space-y-1.5">
            <FactRow label="Strategies"    facts={props.node.strategies}    tone="strategy" />
            <FactRow label="Optimizations" facts={props.node.optimizations} tone="optimization" />
            <FactRow label="ZK chips"      facts={props.node.chips}         tone="chip" />
          </div>

          <Show when={components().length > 0}>
            <div class="mt-3">
              <div class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-1.5">
                Components ({components().length})
              </div>
              <div class="grid grid-cols-1 sm:grid-cols-2 md:grid-cols-3 gap-2">
                <For each={components()}>
                  {(c) => (
                    <ComponentBox
                      component={c}
                      onSelect={props.onSelect}
                      selected={props.selectedId === c.id}
                      compact
                    />
                  )}
                </For>
              </div>
            </div>
          </Show>
        </div>
      </div>

      {/* Children */}
      <Show when={expanded() && hasChildren()}>
        <For each={props.node.children}>
          {(child, i) => (
            <TreeRow
              node={child}
              depth={props.depth + 1}
              onSelect={props.onSelect}
              selectedId={props.selectedId}
              isLastInSiblings={i() === (props.node.children!.length - 1)}
              prefix={[...props.prefix, props.depth === 0 ? false : !props.isLastInSiblings]}
            />
          )}
        </For>
      </Show>
    </div>
  );
}

export default function Specificity() {
  const meta = VIEWS.find(v => v.id === 'specificity')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      question={meta.question}
      subtitle={meta.blurb}
      rightSlot={<AxisLegend />}
    >
      <SectionCard
        title="CALC's specificity lattice"
        subtitle="Each level down the tree adds a commitment. Framework code runs for every calculus; logic code runs for every ILL program; theory code runs whenever the corresponding equational theory is active; program/instance code is scoped to one domain."
      >
        <TreeRow
          node={SPEC_TREE}
          depth={0}
          onSelect={setSelected}
          selectedId={selected()?.id}
          isLastInSiblings={true}
          prefix={[]}
        />
      </SectionCard>

      <SectionCard
        title="Key insight"
        subtitle="Strategies, optimizations, and ZK chips exist at EVERY specificity level — they are not separate layers above the logic."
      >
        <div class="grid grid-cols-1 md:grid-cols-3 gap-3 text-sm">
          <div class="rounded border border-blue-200 dark:border-blue-700 bg-blue-50 dark:bg-blue-900/20 p-3">
            <div class="font-semibold text-blue-800 dark:text-blue-200">Strategies</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              The strategy stack has framework-level layers (fingerprint, disc-tree) plus logic-level
              (Andreoli focusing), plus theory-level (binlit ↔ i/o/e normalization), plus program-level
              (EVM opcode dispatch). Each specificity adds a more informative selector.
            </p>
          </div>
          <div class="rounded border border-orange-200 dark:border-orange-700 bg-orange-50 dark:bg-orange-900/20 p-3">
            <div class="font-semibold text-orange-800 dark:text-orange-200">Optimizations</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Same pattern — framework-level (structural memo), logic-level (compiled clauses),
              theory-level (FFI opt), program-level (per-opcode fast paths). Each level's optimization
              is parametric in the level above.
            </p>
          </div>
          <div class="rounded border border-purple-200 dark:border-purple-700 bg-purple-50 dark:bg-purple-900/20 p-3">
            <div class="font-semibold text-purple-800 dark:text-purple-200">ZK chips</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Chip design mirrors specificity — framework chips verify rule application, logic chips
              verify connective decomposition, theory chips handle arithmetic/hashing, custom chips
              encode program-specific semantics.
            </p>
          </div>
        </div>
      </SectionCard>

      <DetailPanel component={selected()} onClose={() => setSelected(null)} />
    </Page>
  );
}
