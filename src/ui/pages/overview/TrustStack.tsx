/**
 * Trust Stack view — two genuine stacks on a shared foundation.
 *
 * Layout:
 *   [ Backward Prover (L4→L1) ]   ↔ monad bridge ↔   [ Forward Engine (ILL→LNL→Core) ]
 *                           \     /
 *                 Shared Foundation (Kernel Ops + Store)
 *                          opt (cross-cutting wrapper, sidecar)
 *
 * Trust coloring is inherited from each layer; components inside a layer may
 * carry a stronger trust (e.g. L1 kernel is green even while its siblings
 * are yellow). Click any ComponentBox → DetailPanel.
 */

import { For, Show } from 'solid-js';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import LayerBand from './blocks/LayerBand';
import DetailPanel from './blocks/DetailPanel';
import Intro from './blocks/Intro';
import ComponentBox from './blocks/ComponentBox';
import { TrustBadge } from './blocks/Badge';
import { useHashComponent } from './blocks/useHashComponent';
import { layersByStack } from './data/layers';
import { componentsByCluster, getComponent } from './data/components';
import { VIEWS } from './data/meta';
import { TRUST_COLORS } from './data/palette';
import type { Component, Trust } from './data/types';

function Legend() {
  return (
    <div class="flex flex-wrap items-center gap-3 text-xs">
      <span class="font-semibold text-gray-600 dark:text-gray-400 uppercase text-[10px] tracking-wider">Trust</span>
      <For each={(['kernel', 'infrastructure', 'optimization', 'ui'] as Trust[])}>
        {(t) => <TrustBadge trust={t} />}
      </For>
    </div>
  );
}

/** A single column: top-down stack of LayerBands. */
function StackColumn(props: {
  title: string;
  subtitle: string;
  stack: string;
  onSelect: (c: Component) => void;
  selectedId?: string;
  accentClass: string;
}) {
  const layers = layersByStack(props.stack);
  return (
    <div class="space-y-3">
      <header class="text-center">
        <h4 class={`text-sm font-bold uppercase tracking-wider ${props.accentClass}`}>{props.title}</h4>
        <p class="text-xs text-gray-500 dark:text-gray-400">{props.subtitle}</p>
      </header>
      <For each={layers}>
        {(layer) => (
          <LayerBand layer={layer} onSelect={props.onSelect} selectedId={props.selectedId} />
        )}
      </For>
    </div>
  );
}

/** Cross-stack monad bridge — visual connector between L3 backward and the forward engine. */
function MonadBridge(props: { onSelect: (c: Component) => void; selectedId?: string }) {
  const bridge = getComponent('prover.bridge')!;
  return (
    <div class="flex flex-col items-center justify-center gap-2 h-full">
      <div class="flex items-center gap-2">
        <span class="text-2xl text-gray-400 dark:text-gray-500">↔</span>
        <span class="text-[10px] uppercase tracking-wider font-semibold text-gray-500 dark:text-gray-400">Monad Bridge</span>
      </div>
      <div class="w-full max-w-[160px]">
        <ComponentBox component={bridge} onSelect={props.onSelect} selected={props.selectedId === bridge.id} />
      </div>
      <div class="text-[10px] text-gray-500 dark:text-gray-400 text-center leading-tight max-w-[160px]">
        {`{A}`} shifts polarity: backward search at goal position, forward execution inside the lax monad.
      </div>
    </div>
  );
}

/** Cross-cutting optimization sidecar — shows opt wraps engine layers. */
function OptSidecar(props: { onSelect: (c: Component) => void; selectedId?: string }) {
  const opt = componentsByCluster('engine.opt');
  const trust = TRUST_COLORS.optimization;
  return (
    <div class={`rounded-lg border ${trust.border} ${trust.bg} p-3`}>
      <header class="mb-2">
        <h4 class={`font-bold text-sm ${trust.text}`}>opt · Optimization (cross-cutting)</h4>
        <p class="text-[11px] text-gray-600 dark:text-gray-400 mt-0.5">
          Not a stack layer. Each module <code class="font-mono">wrap()</code>s a lower-layer function,
          injected at the composition root. Bare profile disables all.
        </p>
      </header>
      <div class="grid grid-cols-2 sm:grid-cols-3 gap-2">
        <For each={opt}>
          {(c) => <ComponentBox component={c} onSelect={props.onSelect} selected={props.selectedId === c.id} compact />}
        </For>
      </div>
    </div>
  );
}

export default function TrustStack() {
  const meta = VIEWS.find(v => v.id === 'trust')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);
  const foundationLayer = layersByStack('foundation')[0];

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      question={meta.question}
      subtitle="Two genuine stacks — enforced by tests/engine/layer-dag.test.js — on a shared kernel foundation. The narrow green wedge is the trust anchor; a bug in the kernel compromises soundness, a bug in opt only compromises performance."
      rightSlot={<Legend />}
    >
      <DetailPanel component={selected()} onClose={() => setSelected(null)} />

      <Intro>
        This view groups every component in CALC by <strong>trust</strong> — the blast radius of a bug.
        The <em>kernel</em> (green) is the trust anchor: a bug here can accept an invalid proof.
        Everything else can fail (infrastructure yellow), mis-optimize (opt orange), or mis-render (UI gray),
        but cannot lie about what's provable. Click any component box to pin its details at the top of the page.
      </Intro>

      <SectionCard
        title="Two genuine stacks"
        subtitle="Backward prover (left) is a 4-layer pyramid over the kernel. Forward engine (right) is a 3-layer pyramid. The monad bridge connects them at the {·} connective."
      >
        <div class="grid grid-cols-1 lg:grid-cols-[1fr_auto_1fr] gap-4 items-stretch">
          <StackColumn
            title="Backward Prover"
            subtitle="L4 → L1, kernel at the bottom"
            stack="prover"
            accentClass="text-emerald-700 dark:text-emerald-400"
            onSelect={setSelected}
            selectedId={selected()?.id}
          />
          <div class="hidden lg:flex min-h-full items-center">
            <MonadBridge onSelect={setSelected} selectedId={selected()?.id} />
          </div>
          <StackColumn
            title="Forward Engine"
            subtitle="ILL → LNL → Generic Core"
            stack="engine"
            accentClass="text-amber-700 dark:text-amber-400"
            onSelect={setSelected}
            selectedId={selected()?.id}
          />
          {/* On narrow screens, place the bridge below the left stack */}
          <div class="lg:hidden">
            <MonadBridge onSelect={setSelected} selectedId={selected()?.id} />
          </div>
        </div>
      </SectionCard>

      <SectionCard
        title="Cross-cutting optimization"
        subtitle="opt/ modules wrap lower-layer functions — they are not a stack layer. Turning them off (bare profile) preserves soundness; only performance degrades."
      >
        <OptSidecar onSelect={setSelected} selectedId={selected()?.id} />
      </SectionCard>

      <SectionCard
        title="Shared foundation"
        subtitle="Content-addressed store + kernel ops. Both stacks bottom out here; a bug anywhere in this layer is unsound for every prover and every execution mode."
      >
        <Show when={foundationLayer}>
          <LayerBand
            layer={foundationLayer!}
            onSelect={setSelected}
            selectedId={selected()?.id}
            compact
          />
        </Show>
      </SectionCard>

      <SectionCard
        title="How to read this view"
        subtitle="If the code on this panel has a bug, what's the worst it can do?"
      >
        <div class="grid grid-cols-1 md:grid-cols-4 gap-3 text-sm">
          <For each={(['kernel', 'infrastructure', 'optimization', 'ui'] as Trust[])}>
            {(t) => {
              const p = TRUST_COLORS[t];
              const copy: Record<Trust, { head: string; body: string }> = {
                kernel:         { head: 'Unsound',     body: 'A bug here accepts an invalid proof — the calculus lies. Trust anchor: re-verify every step.' },
                infrastructure: { head: 'Incomplete',  body: 'A bug here misses valid proofs or loops forever — still sound, but the prover becomes unreliable.' },
                optimization:   { head: 'Testable',    body: 'Bypass by disabling (bare profile); FFI vs clause differential testing catches drift. Performance-only.' },
                ui:             { head: 'Cosmetic',    body: 'A bug here is a display glitch — the proof/engine underneath is untouched.' },
              };
              return (
                <div class={`rounded-lg border ${p.border} ${p.bg} p-3`}>
                  <div class={`font-bold text-sm ${p.text}`}>{p.label}</div>
                  <div class={`text-xs font-semibold ${p.text} mt-0.5`}>{copy[t].head}</div>
                  <p class="text-xs text-gray-700 dark:text-gray-300 mt-2 leading-snug">{copy[t].body}</p>
                </div>
              );
            }}
          </For>
        </div>
      </SectionCard>

    </Page>
  );
}
