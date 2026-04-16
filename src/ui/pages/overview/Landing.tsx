/**
 * Overview landing page.
 *
 * Dual entry points (Stripe pattern):
 *   - "By perspective" — 4 axis-view cards
 *   - "By subsystem"   — 7 deep-dive cards
 *
 * Live stats bar pulls real runtime data via lib/calculus.ts.
 */

import { createMemo, For } from 'solid-js';
import { A } from '@solidjs/router';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import { VIEWS, DEEP_DIVES } from './data/meta';
import { COMPONENTS } from './data/components';
import { DEEPDIVE_ACCENT, TRUST_COLORS } from './data/palette';
import {
  getCalculusName,
  getFormulaConnectives,
  getAllRules,
  getBundle,
} from '../../lib/calculus';

function Stat(props: { label: string; value: string | number; hint?: string }) {
  return (
    <div class="px-4 py-3 rounded-lg bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 shadow-sm">
      <div class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400">{props.label}</div>
      <div class="text-2xl font-bold font-mono text-gray-900 dark:text-white mt-1">{props.value}</div>
      {props.hint && <div class="text-[11px] text-gray-500 dark:text-gray-500 mt-0.5">{props.hint}</div>}
    </div>
  );
}

export default function Landing() {
  const calcName = createMemo(() => {
    try { return getCalculusName(); } catch { return 'ILL'; }
  });
  const connectiveCount = createMemo(() => {
    try { return getFormulaConnectives().length; } catch { return 0; }
  });
  const ruleCount = createMemo(() => {
    try { return Object.keys(getAllRules()).length; } catch { return 0; }
  });
  const forwardRuleCount = createMemo(() => {
    try {
      const bundle: any = getBundle();
      return (bundle?.forwardRules || bundle?.forward || []).length || 0;
    } catch { return 0; }
  });
  const componentCount = COMPONENTS.length;

  // Trust-distribution histogram (for the orientation block).
  const trustDist = createMemo(() => {
    const buckets = { kernel: 0, infrastructure: 0, optimization: 0, ui: 0 } as Record<string, number>;
    for (const c of COMPONENTS) buckets[c.trust]++;
    return buckets;
  });

  return (
    <Page
      glyph="⧉"
      title="Architecture Overview"
      subtitle="Multiple views of the same system. Pick a perspective (axis view) or a subsystem (deep dive). Every component appears in every view with the same name and color — click it anywhere to see it everywhere."
    >
      {/* Live stats */}
      <div class="grid grid-cols-2 sm:grid-cols-3 md:grid-cols-5 gap-3">
        <Stat label="Calculus" value={calcName()} hint="object logic" />
        <Stat label="Connectives" value={connectiveCount()} hint="loaded" />
        <Stat label="Rules" value={ruleCount()} hint="inference" />
        <Stat label="Forward Rules" value={forwardRuleCount()} hint="bundled" />
        <Stat label="Components" value={componentCount} hint="catalogued" />
      </div>

      {/* Orientation */}
      <SectionCard
        title="Four axes, one system"
        subtitle="The original L0–L5 lasagna forced four independent dimensions onto a single vertical axis, creating false hierarchies. The overview separates them."
      >
        <div class="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-3">
          <For each={[
            // Static classes only — Tailwind JIT needs the literal class names visible.
            { ax: 'Trust', desc: 'Soundness impact of bugs', gradient: 'Kernel → Infrastructure → Optimization → UI',
              swatches: ['bg-emerald-400', 'bg-amber-400', 'bg-orange-400', 'bg-gray-400'] },
            { ax: 'Specificity', desc: 'Domain knowledge encoded', gradient: 'Framework → Logic → Theory → Program → Instance',
              swatches: ['bg-sky-400', 'bg-indigo-400', 'bg-violet-400', 'bg-fuchsia-400', 'bg-pink-400'] },
            { ax: 'Pipeline', desc: 'When the code runs', gradient: 'Define → Parse → Compile → Execute → Certify → Present',
              swatches: ['bg-slate-400', 'bg-teal-400', 'bg-cyan-400', 'bg-blue-400', 'bg-purple-400', 'bg-rose-400'] },
            { ax: 'Mode', desc: 'How proofs are found', gradient: 'Backward · Forward · Symbolic · Certification',
              swatches: ['bg-emerald-400', 'bg-blue-400', 'bg-purple-400', 'bg-orange-400'] },
          ]}>
            {(row) => (
              <div class="rounded-lg border border-gray-200 dark:border-gray-700 p-3 bg-gray-50/50 dark:bg-gray-900/30">
                <div class="font-bold text-gray-900 dark:text-white">{row.ax}</div>
                <div class="text-xs text-gray-500 dark:text-gray-400">{row.desc}</div>
                <div class="mt-2 flex gap-1">
                  <For each={row.swatches}>
                    {(c) => <span class={`h-2 flex-1 rounded-sm ${c}`} />}
                  </For>
                </div>
                <div class="text-[11px] text-gray-600 dark:text-gray-300 mt-2 leading-relaxed">{row.gradient}</div>
              </div>
            )}
          </For>
        </div>
      </SectionCard>

      {/* By perspective */}
      <SectionCard
        title="By perspective"
        subtitle="Four projections of the same architecture graph. Same component in every view."
      >
        <div class="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-4 gap-4">
          <For each={VIEWS}>
            {(v) => (
              <A
                href={`/overview/${v.slug}`}
                class="group rounded-lg border border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800 p-5 hover:shadow-lg hover:border-blue-400 dark:hover:border-blue-500 transition-all"
              >
                <div class="flex items-baseline gap-2">
                  <span class="text-2xl text-blue-500 dark:text-blue-400">{v.glyph}</span>
                  <h4 class="font-bold text-gray-900 dark:text-white">{v.title}</h4>
                </div>
                <p class="italic text-xs text-gray-500 dark:text-gray-400 mt-1">{v.question}</p>
                <p class="text-sm text-gray-700 dark:text-gray-300 mt-3 leading-snug">{v.blurb}</p>
                <div class="mt-3 text-xs font-semibold text-blue-600 dark:text-blue-400 opacity-70 group-hover:opacity-100">
                  Open view →
                </div>
              </A>
            )}
          </For>
        </div>
      </SectionCard>

      {/* By subsystem */}
      <SectionCard
        title="By subsystem"
        subtitle="Seven deep dives into focused sub-systems. Each dive shows the same components tagged elsewhere, in their local context."
      >
        <div class="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 xl:grid-cols-4 gap-3">
          <For each={DEEP_DIVES}>
            {(d) => (
              <A
                href={`/overview/${d.slug}`}
                class="group rounded-lg border border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800 p-4 hover:shadow-md hover:border-gray-400 dark:hover:border-gray-500 transition-all"
              >
                <div class="flex items-baseline gap-2">
                  <span class={`text-xl ${DEEPDIVE_ACCENT[d.id]}`}>{d.glyph}</span>
                  <h4 class="font-bold text-gray-900 dark:text-white">{d.title}</h4>
                </div>
                <p class="font-mono text-[11px] text-gray-500 dark:text-gray-400 mt-1">{d.oneLiner}</p>
                <p class="text-xs text-gray-600 dark:text-gray-300 mt-2 leading-snug">{d.blurb}</p>
              </A>
            )}
          </For>
        </div>
      </SectionCard>

      {/* Trust distribution bar — quick at-a-glance of codebase shape */}
      <SectionCard
        title="Trust distribution"
        subtitle="How many components sit at each trust level. The narrow green wedge is the trust anchor; the wide yellow band is the infrastructure that builds on it."
      >
        <div class="flex items-center gap-2 text-xs">
          <For each={(['kernel', 'infrastructure', 'optimization', 'ui'] as const)}>
            {(t) => (
              <div class="flex-1 flex flex-col gap-1" style={{ "flex-grow": String(trustDist()[t]) }}>
                <div class={`h-8 rounded ${TRUST_COLORS[t].bg} ${TRUST_COLORS[t].border} border flex items-center justify-center font-bold ${TRUST_COLORS[t].text}`}>
                  {trustDist()[t]}
                </div>
                <div class="text-center text-[11px] text-gray-500 dark:text-gray-400">{TRUST_COLORS[t].label}</div>
              </div>
            )}
          </For>
        </div>
      </SectionCard>
    </Page>
  );
}
