/**
 * Component Atlas — searchable / filterable / sortable index of every
 * architecturally-significant module in CALC.
 *
 * One row per component, enriched with its four-axis tags. The user can:
 *   - free-text search (matches id + name + summary + files)
 *   - filter by Trust, Specificity, Stage, Mode, DeepDive, Cluster
 *   - sort by any column (ascending / descending toggle)
 *   - click a row to open the shared DetailPanel (same UX as every other view)
 *
 * Data source is the single COMPONENTS registry — adding an entry there
 * makes it appear here automatically with correct coloring.
 */

import { createSignal, createMemo, For, Show } from 'solid-js';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import DetailPanel from './blocks/DetailPanel';
import { useHashComponent } from './blocks/useHashComponent';
import { TrustBadge, SpecificityBadge, StageBadge, ModeBadge } from './blocks/Badge';
import { COMPONENTS } from './data/components';
import { VIEWS, DEEP_DIVES } from './data/meta';
import { TRUST_COLORS, SPECIFICITY_COLORS } from './data/palette';
import type { Component, Trust, Specificity, Stage, Mode, DeepDive } from './data/types';

type SortKey = 'name' | 'trust' | 'specificity' | 'deepDive' | 'cluster' | 'stages' | 'modes';
type SortDir = 'asc' | 'desc';

const TRUSTS: Trust[] = ['kernel', 'infrastructure', 'optimization', 'ui'];
const SPECS: Specificity[]  = ['framework', 'logic', 'theory', 'program', 'instance'];
const STAGES: Stage[] = ['define', 'parse', 'compile', 'execute', 'certify', 'present'];
const MODES: Mode[] = ['backward', 'forward', 'symbolic', 'certification'];

/** Utility: compare by component field given a sort key. */
function compareBy(a: Component, b: Component, key: SortKey): number {
  switch (key) {
    case 'name':       return a.name.localeCompare(b.name);
    case 'trust':      return TRUST_COLORS[a.trust].rank - TRUST_COLORS[b.trust].rank;
    case 'specificity':return SPECIFICITY_COLORS[a.specificity].rank - SPECIFICITY_COLORS[b.specificity].rank;
    case 'deepDive':   return a.deepDive.localeCompare(b.deepDive);
    case 'cluster':    return (a.cluster ?? '').localeCompare(b.cluster ?? '');
    case 'stages':     return a.stages.length - b.stages.length;
    case 'modes':      return a.modes.length - b.modes.length;
    default:           return 0;
  }
}

interface FacetChipProps<T extends string> {
  label: string;
  value: T;
  active: boolean;
  onToggle: (v: T) => void;
  /** Optional colored dot to echo the palette. */
  dotClass?: string;
}
function FacetChip<T extends string>(props: FacetChipProps<T>) {
  return (
    <button
      type="button"
      onClick={() => props.onToggle(props.value)}
      class={`inline-flex items-center gap-1 rounded-full px-2.5 py-0.5 text-xs border transition
        ${props.active
          ? 'bg-blue-600 text-white border-blue-600 shadow-sm'
          : 'bg-white dark:bg-gray-800 text-gray-700 dark:text-gray-300 border-gray-300 dark:border-gray-600 hover:bg-gray-100 dark:hover:bg-gray-700'}
      `}
    >
      <Show when={props.dotClass}>
        <span class={`h-1.5 w-1.5 rounded-full ${props.dotClass}`} aria-hidden="true" />
      </Show>
      <span>{props.label}</span>
    </button>
  );
}

function SortHeader(props: {
  label: string; k: SortKey;
  sortKey: SortKey; sortDir: SortDir;
  onClick: (k: SortKey) => void;
  align?: 'left' | 'center';
}) {
  const active = () => props.sortKey === props.k;
  return (
    <th class={`py-2 px-2 font-semibold text-gray-700 dark:text-gray-300 select-none ${props.align === 'center' ? 'text-center' : 'text-left'}`}>
      <button
        type="button"
        onClick={() => props.onClick(props.k)}
        class={`inline-flex items-center gap-1 hover:text-blue-600 dark:hover:text-blue-400 ${active() ? 'text-blue-700 dark:text-blue-300' : ''}`}
      >
        <span>{props.label}</span>
        <Show when={active()}>
          <span class="text-[10px]">{props.sortDir === 'asc' ? '▲' : '▼'}</span>
        </Show>
      </button>
    </th>
  );
}

export default function Atlas() {
  const meta = VIEWS.find(v => v.id === 'atlas')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);

  const [query, setQuery] = createSignal('');
  const [trustFilter, setTrustFilter]   = createSignal<Set<Trust>>(new Set());
  const [specFilter,  setSpecFilter]    = createSignal<Set<Specificity>>(new Set());
  const [stageFilter, setStageFilter]   = createSignal<Set<Stage>>(new Set());
  const [modeFilter,  setModeFilter]    = createSignal<Set<Mode>>(new Set());
  const [diveFilter,  setDiveFilter]    = createSignal<Set<DeepDive>>(new Set());
  const [sortKey, setSortKey] = createSignal<SortKey>('name');
  const [sortDir, setSortDir] = createSignal<SortDir>('asc');

  /** Toggle helpers — return new set to guarantee signal fires. */
  const toggle = <T,>(setter: (u: (prev: Set<T>) => Set<T>) => void) => (v: T) =>
    setter(prev => {
      const next = new Set(prev);
      if (next.has(v)) next.delete(v); else next.add(v);
      return next;
    });

  const toggleTrust = toggle<Trust>(setTrustFilter);
  const toggleSpec  = toggle<Specificity>(setSpecFilter);
  const toggleStage = toggle<Stage>(setStageFilter);
  const toggleMode  = toggle<Mode>(setModeFilter);
  const toggleDive  = toggle<DeepDive>(setDiveFilter);

  const onSortClick = (k: SortKey) => {
    if (sortKey() === k) setSortDir(d => (d === 'asc' ? 'desc' : 'asc'));
    else { setSortKey(k); setSortDir('asc'); }
  };

  const filtered = createMemo(() => {
    const q = query().trim().toLowerCase();
    const tf = trustFilter(), sf = specFilter(), stf = stageFilter(), mf = modeFilter(), df = diveFilter();
    return COMPONENTS.filter(c => {
      if (q) {
        const hay = `${c.id} ${c.name} ${c.summary} ${c.files.join(' ')}`.toLowerCase();
        if (!hay.includes(q)) return false;
      }
      if (tf.size > 0 && !tf.has(c.trust)) return false;
      if (sf.size > 0 && !sf.has(c.specificity)) return false;
      if (stf.size > 0 && !c.stages.some(s => stf.has(s))) return false;
      if (mf.size > 0 && !c.modes.some(m => mf.has(m))) return false;
      if (df.size > 0 && !df.has(c.deepDive)) return false;
      return true;
    });
  });

  const sorted = createMemo(() => {
    const copy = filtered().slice();
    copy.sort((a, b) => compareBy(a, b, sortKey()));
    if (sortDir() === 'desc') copy.reverse();
    return copy;
  });

  const clearAll = () => {
    setQuery('');
    setTrustFilter(new Set<Trust>());
    setSpecFilter(new Set<Specificity>());
    setStageFilter(new Set<Stage>());
    setModeFilter(new Set<Mode>());
    setDiveFilter(new Set<DeepDive>());
  };

  const anyFilter = () =>
    query().length > 0 ||
    trustFilter().size + specFilter().size + stageFilter().size + modeFilter().size + diveFilter().size > 0;

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      question={meta.question}
      subtitle={meta.blurb}
    >
      <SectionCard
        title="Search + filter"
        subtitle="Combine facets freely — they AND together. Clicking twice deselects a facet."
      >
        <div class="flex flex-col gap-3">
          {/* Search */}
          <div class="flex flex-wrap items-center gap-2">
            <div class="flex-1 min-w-[16rem]">
              <input
                type="search"
                placeholder="Search id, name, summary, or file path…"
                value={query()}
                onInput={(e) => setQuery(e.currentTarget.value)}
                class="w-full rounded border border-gray-300 dark:border-gray-600 bg-white dark:bg-gray-900 px-3 py-1.5 text-sm text-gray-900 dark:text-gray-100 focus:outline-none focus:ring-2 focus:ring-blue-500"
              />
            </div>
            <div class="text-xs text-gray-600 dark:text-gray-400 whitespace-nowrap">
              {sorted().length} / {COMPONENTS.length} components
            </div>
            <Show when={anyFilter()}>
              <button
                type="button"
                onClick={clearAll}
                class="text-xs px-2 py-1 rounded border border-gray-300 dark:border-gray-600 text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700"
              >
                Clear all
              </button>
            </Show>
          </div>

          {/* Facets */}
          <div class="space-y-2">
            <div class="flex items-center gap-2 flex-wrap">
              <span class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 w-24 shrink-0">Trust</span>
              <For each={TRUSTS}>
                {(t) => <FacetChip label={TRUST_COLORS[t].label} value={t} active={trustFilter().has(t)} onToggle={toggleTrust} dotClass={TRUST_COLORS[t].dot} />}
              </For>
            </div>
            <div class="flex items-center gap-2 flex-wrap">
              <span class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 w-24 shrink-0">Specificity</span>
              <For each={SPECS}>
                {(s) => <FacetChip label={SPECIFICITY_COLORS[s].label} value={s} active={specFilter().has(s)} onToggle={toggleSpec} />}
              </For>
            </div>
            <div class="flex items-center gap-2 flex-wrap">
              <span class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 w-24 shrink-0">Stage</span>
              <For each={STAGES}>
                {(s) => <FacetChip label={s} value={s} active={stageFilter().has(s)} onToggle={toggleStage} />}
              </For>
            </div>
            <div class="flex items-center gap-2 flex-wrap">
              <span class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 w-24 shrink-0">Mode</span>
              <For each={MODES}>
                {(m) => <FacetChip label={m} value={m} active={modeFilter().has(m)} onToggle={toggleMode} />}
              </For>
            </div>
            <div class="flex items-center gap-2 flex-wrap">
              <span class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 w-24 shrink-0">Deep dive</span>
              <For each={DEEP_DIVES}>
                {(d) => <FacetChip label={d.title} value={d.id} active={diveFilter().has(d.id)} onToggle={toggleDive} />}
              </For>
            </div>
          </div>
        </div>
      </SectionCard>

      <SectionCard
        title={`Components (${sorted().length})`}
        subtitle="Click a row to open the detail panel with cross-view navigation links."
      >
        <div class="overflow-x-auto rounded border border-gray-200 dark:border-gray-700">
          <table class="w-full text-xs">
            <thead class="bg-gray-50 dark:bg-gray-900/40 border-b border-gray-200 dark:border-gray-700">
              <tr>
                <SortHeader label="Component"   k="name"        sortKey={sortKey()} sortDir={sortDir()} onClick={onSortClick} />
                <SortHeader label="Trust"       k="trust"       sortKey={sortKey()} sortDir={sortDir()} onClick={onSortClick} />
                <SortHeader label="Specificity" k="specificity" sortKey={sortKey()} sortDir={sortDir()} onClick={onSortClick} />
                <SortHeader label="Stages"      k="stages"      sortKey={sortKey()} sortDir={sortDir()} onClick={onSortClick} />
                <SortHeader label="Modes"       k="modes"       sortKey={sortKey()} sortDir={sortDir()} onClick={onSortClick} />
                <SortHeader label="Deep Dive"   k="deepDive"    sortKey={sortKey()} sortDir={sortDir()} onClick={onSortClick} />
                <SortHeader label="Cluster"     k="cluster"     sortKey={sortKey()} sortDir={sortDir()} onClick={onSortClick} />
              </tr>
            </thead>
            <tbody>
              <Show when={sorted().length > 0} fallback={
                <tr><td colspan={7} class="py-8 text-center text-gray-500 dark:text-gray-400 italic">No components match these filters.</td></tr>
              }>
                <For each={sorted()}>
                  {(c) => (
                    <tr
                      tabIndex={0}
                      onClick={() => setSelected(c)}
                      onKeyDown={(e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); setSelected(c); } }}
                      class={`border-t border-gray-100 dark:border-gray-800 hover:bg-blue-50 dark:hover:bg-blue-900/20 cursor-pointer focus:outline-none focus:ring-2 focus:ring-blue-500 ${selected()?.id === c.id ? 'bg-blue-50 dark:bg-blue-900/20' : ''}`}
                    >
                      <td class="py-2 px-2 align-top">
                        <div class="flex items-start gap-2">
                          <span class={`mt-1 h-2 w-2 rounded-full shrink-0 ${TRUST_COLORS[c.trust].dot}`} aria-hidden="true" />
                          <div class="min-w-0">
                            <div class="font-mono font-semibold text-gray-900 dark:text-white truncate">{c.name}</div>
                            <div class="text-[11px] text-gray-600 dark:text-gray-400 truncate">{c.summary}</div>
                            <div class="text-[10px] text-gray-500 dark:text-gray-500 mt-0.5 font-mono truncate">{c.id}</div>
                          </div>
                        </div>
                      </td>
                      <td class="py-2 px-2 align-top whitespace-nowrap"><TrustBadge trust={c.trust} /></td>
                      <td class="py-2 px-2 align-top whitespace-nowrap"><SpecificityBadge specificity={c.specificity} /></td>
                      <td class="py-2 px-2 align-top">
                        <div class="flex flex-wrap gap-1">
                          <For each={c.stages}>{(s) => <StageBadge stage={s} />}</For>
                        </div>
                      </td>
                      <td class="py-2 px-2 align-top">
                        <div class="flex flex-wrap gap-1">
                          <For each={c.modes}>{(m) => <ModeBadge mode={m} />}</For>
                        </div>
                      </td>
                      <td class="py-2 px-2 align-top whitespace-nowrap text-gray-700 dark:text-gray-300">{c.deepDive}</td>
                      <td class="py-2 px-2 align-top whitespace-nowrap font-mono text-[11px] text-gray-500 dark:text-gray-400">{c.cluster ?? '—'}</td>
                    </tr>
                  )}
                </For>
              </Show>
            </tbody>
          </table>
        </div>
      </SectionCard>

      <DetailPanel component={selected()} onClose={() => setSelected(null)} />
    </Page>
  );
}
