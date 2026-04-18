/**
 * Backward Prover deep dive.
 *
 * L1 Kernel → L2 Generic → L3 Focused → L4 Strategy.
 * Each layer: description, API surface, trust guarantee, key algorithms.
 * L3 focusing has a phase diagram (positive ⇄ negative phase alternation).
 */

import { For } from 'solid-js';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import LayerBand from './blocks/LayerBand';
import DetailPanel from './blocks/DetailPanel';
import Intro from './blocks/Intro';
import { useHashComponent } from './blocks/useHashComponent';
import { layersByStack } from './data/layers';
import { DEEP_DIVES } from './data/meta';
import { DEEPDIVE_ACCENT } from './data/palette';
import type { Component } from './data/types';

interface LayerDoc {
  id: string;
  api: string[];
  algorithms: string[];
  guarantee: string;
}

const LAYER_DOCS: Record<string, LayerDoc> = {
  'prover.l1': {
    id: 'prover.l1',
    api: ['verify(proofTerm) → bool', 'applyRule(state, rule) → state'],
    algorithms: ['Content-addressed term rebuild', 'Premise re-derivation', 'Capture-avoiding substitution check'],
    guarantee: 'Trust anchor. Re-derives every step from rule premises. A bug here is unsound.',
  },
  'prover.l2': {
    id: 'prover.l2',
    api: ['search(goal) → proofTerm?', 'applicable(state) → rule[]', 'step(state, rule) → state[]'],
    algorithms: ['Rule descriptor → premise computation', 'Branching search primitives', 'Proof-term construction'],
    guarantee: 'Sound by construction — every action produces a verifiable kernel term. Incompleteness is possible.',
  },
  'prover.l3': {
    id: 'prover.l3',
    api: ['focus(goal) → proofTerm?', 'phase ∈ {positive, negative}'],
    algorithms: ['Andreoli focusing (1992)', 'Positive phase: eager decomposition of positive connectives', 'Negative phase: invertible rules, any order'],
    guarantee: 'Complete for classical/intuitionistic fragments. Reduces search space by factor ~n! via polarity discipline.',
  },
  'prover.l4': {
    id: 'prover.l4',
    api: ['interactive(goal)', 'auto(goal, depth) → proofTerm?', 'suggest(state) → rule[]'],
    algorithms: ['Manual: one-step interactive', 'Auto: iterative deepening', 'Heuristic rule ordering'],
    guarantee: 'Orthogonal to soundness. A bug here just picks bad rules — completeness may suffer but proofs found remain valid.',
  },
};

function PhaseDiagram() {
  return (
    <svg viewBox="0 0 640 200" class="w-full max-w-3xl mx-auto">
      <defs>
        <marker id="focus-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto-start-reverse">
          <path d="M 0 0 L 8 4 L 0 8 z" fill="currentColor" />
        </marker>
      </defs>

      {/* Negative phase box */}
      <g class="text-red-700 dark:text-red-400">
        <rect x="20" y="40" width="220" height="120" rx="10" class="fill-red-50 dark:fill-red-900/20 stroke-red-400" stroke-width="2" />
        <text x="130" y="68" text-anchor="middle" class="fill-current" font-weight="700" font-size="14">Negative phase</text>
        <text x="130" y="88" text-anchor="middle" class="fill-current" font-size="11">(asynchronous · invertible)</text>
        <text x="130" y="116" text-anchor="middle" class="fill-current" font-size="11" font-family="ui-monospace">{'⊸ᵣ, &ᵣ, {·}ᵣ, ∀ᵣ'}</text>
        <text x="130" y="136" text-anchor="middle" class="fill-current" font-size="11" font-family="ui-monospace">{'⊗ₗ, ⊕ₗ, !ₗ, ∃ₗ, Iₗ, 0ₗ'}</text>
      </g>

      {/* Positive phase box */}
      <g class="text-green-700 dark:text-green-400">
        <rect x="400" y="40" width="220" height="120" rx="10" class="fill-green-50 dark:fill-green-900/20 stroke-green-400" stroke-width="2" />
        <text x="510" y="68" text-anchor="middle" class="fill-current" font-weight="700" font-size="14">Positive phase</text>
        <text x="510" y="88" text-anchor="middle" class="fill-current" font-size="11">(synchronous · focused)</text>
        <text x="510" y="116" text-anchor="middle" class="fill-current" font-size="11" font-family="ui-monospace">{'⊗ᵣ, ⊕ᵣ, !ᵣ, ∃ᵣ, Iᵣ'}</text>
        <text x="510" y="136" text-anchor="middle" class="fill-current" font-size="11" font-family="ui-monospace">{'⊸ₗ, &ₗ, {·}ₗ, ∀ₗ'}</text>
      </g>

      {/* Arrow: negative → positive (focus on stable atom / positive formula) */}
      <g class="text-gray-500 dark:text-gray-400">
        <path d="M 240 80 C 310 60 330 60 400 80" fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#focus-arrow)" />
        <text x="320" y="55" text-anchor="middle" class="fill-current" font-size="11" font-weight="500">Focus on positive</text>

        {/* Arrow: positive → negative (release) */}
        <path d="M 400 130 C 330 150 310 150 240 130" fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#focus-arrow)" stroke-dasharray="4 4" />
        <text x="320" y="170" text-anchor="middle" class="fill-current" font-size="11" font-weight="500">Release (atom / negative)</text>
      </g>
    </svg>
  );
}

function LayerDocPanel(props: { layerId: string }) {
  const doc = () => LAYER_DOCS[props.layerId];
  return (
    <div class="text-xs space-y-3">
      <div>
        <div class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-1">API surface</div>
        <ul class="space-y-1">
          <For each={doc().api}>
            {(line) => <li class="font-mono text-gray-800 dark:text-gray-200 bg-gray-100 dark:bg-gray-900/40 px-2 py-0.5 rounded">{line}</li>}
          </For>
        </ul>
      </div>
      <div>
        <div class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-1">Key algorithms</div>
        <ul class="list-disc pl-4 text-gray-700 dark:text-gray-300 space-y-0.5">
          <For each={doc().algorithms}>{(a) => <li>{a}</li>}</For>
        </ul>
      </div>
      <div class="rounded bg-gray-50 dark:bg-gray-900/40 border border-gray-200 dark:border-gray-700 p-2">
        <div class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-1">Trust guarantee</div>
        <div class="text-gray-700 dark:text-gray-300">{doc().guarantee}</div>
      </div>
    </div>
  );
}

export default function Prover() {
  const meta = DEEP_DIVES.find(d => d.id === 'prover')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);
  const layers = layersByStack('prover');

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      subtitle="Sound by construction, complete via focusing. Each layer adds search discipline on top of a verified kernel. Layer DAG: kernel ← generic ← focused ← strategy (enforced in layer-dag.test.js)."
      accentClass={DEEPDIVE_ACCENT.prover}
    >
      <DetailPanel component={selected()} onClose={() => setSelected(null)} />

      <Intro>
        The <strong>backward prover</strong> searches for a proof of a goal sequent. It's built as four strict
        layers — <em>L1 Kernel</em> verifies, <em>L2 Generic</em> searches, <em>L3 Focused</em> disciplines the
        search with Andreoli focusing, and <em>L4 Strategy</em> picks which rules to try. L1 is the trust anchor;
        L2–L4 can fail to find a proof but cannot accept an invalid one.
      </Intro>

      <SectionCard
        title="The four layers"
        subtitle="Reading bottom-up: kernel verifies, generic searches, focused disciplines, strategy drives."
      >
        <div class="space-y-4">
          <For each={layers}>
            {(layer) => (
              <div class="grid grid-cols-1 lg:grid-cols-[1fr_1fr] gap-3">
                <LayerBand layer={layer} onSelect={setSelected} selectedId={selected()?.id} />
                <LayerDocPanel layerId={layer.id} />
              </div>
            )}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="L3 focusing phase diagram"
        subtitle="Andreoli (1992) focusing alternates two phases based on connective polarity. Negative rules are invertible (apply eagerly, any order); positive rules require a choice (focus once, decompose eagerly)."
      >
        <PhaseDiagram />
        <div class="mt-4 grid grid-cols-1 md:grid-cols-2 gap-3 text-xs text-gray-700 dark:text-gray-300">
          <div class="rounded bg-red-50 dark:bg-red-900/20 border border-red-200 dark:border-red-700 p-3">
            <strong class="text-red-800 dark:text-red-300">Negative phase:</strong> apply all invertible rules until
            none remain. Order doesn't matter — any permutation produces the same result. Terminates by subformula
            measure.
          </div>
          <div class="rounded bg-green-50 dark:bg-green-900/20 border border-green-200 dark:border-green-700 p-3">
            <strong class="text-green-800 dark:text-green-300">Positive phase:</strong> focus on a single formula,
            decompose eagerly. All choices are synchronous (require backtracking). Release on atom or negative
            sub-formula.
          </div>
        </div>
      </SectionCard>

      <SectionCard
        title="Monad bridge to the forward engine"
        subtitle={'The lax monad {A} is the polarity shift point where the backward prover hands control to the forward engine. Three execution profiles control how the handoff is verified.'}
      >
        <div class="flex flex-col md:flex-row items-stretch gap-3 mb-4">
          <div class="flex-1 rounded border border-gray-200 dark:border-gray-700 p-3 bg-gray-50 dark:bg-gray-900/30">
            <div class="font-semibold text-gray-900 dark:text-white text-sm">Backward (search) side</div>
            <p class="text-xs text-gray-600 dark:text-gray-400 mt-1">Focused prover hits {`{A}`} connective in L3 and invokes the bridge.</p>
          </div>
          <div class="md:self-center text-gray-400 dark:text-gray-500 text-2xl text-center">↔</div>
          <div class="flex-1 rounded border border-gray-200 dark:border-gray-700 p-3 bg-gray-50 dark:bg-gray-900/30">
            <div class="font-semibold text-gray-900 dark:text-white text-sm">Forward (execute) side</div>
            <p class="text-xs text-gray-600 dark:text-gray-400 mt-1">Forward engine runs to quiescence; residual state is verified against the inner succedent.</p>
          </div>
        </div>

        <div class="overflow-x-auto">
          <table class="w-full text-xs border-collapse">
            <thead>
              <tr class="text-left">
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Profile</th>
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Forward engine used?</th>
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Verification at the monad step</th>
                <th class="pb-2 pl-3 font-semibold text-gray-600 dark:text-gray-400">Kernel output</th>
              </tr>
            </thead>
            <tbody>
              <tr class="border-t border-gray-200 dark:border-gray-700 align-top">
                <td class="py-2 pr-3 font-mono font-semibold text-emerald-700 dark:text-emerald-400">full (default)</td>
                <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-xs">Yes — runs to quiescence. Opaque leaf from the backward prover's perspective.</td>
                <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-md"><code class="font-mono">rightFocus()</code> checks that the residual linear state matches the inner succedent S of {`{S}`}.</td>
                <td class="py-2 pl-3 text-gray-700 dark:text-gray-300 font-mono text-[11px]">{`{ valid: true, unverified: 'modeSwitch' }`}</td>
              </tr>
              <tr class="border-t border-gray-200 dark:border-gray-700 align-top">
                <td class="py-2 pr-3 font-mono font-semibold text-blue-700 dark:text-blue-400">guided</td>
                <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-xs">Yes — with evidence collection (oracle mode).</td>
                <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-md"><code class="font-mono">guidedTerm()</code> synthesises a complete ILL proof term (copy → loli_l → tensor_r → monad_l chain). <code class="font-mono">check-term.js</code> re-verifies every step.</td>
                <td class="py-2 pl-3 text-gray-700 dark:text-gray-300 font-mono text-[11px]">{`{ valid: true }`} — no unverified gap</td>
              </tr>
              <tr class="border-t border-gray-200 dark:border-gray-700 align-top">
                <td class="py-2 pr-3 font-mono font-semibold text-gray-700 dark:text-gray-400">off</td>
                <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-xs">No — forward engine is bypassed entirely.</td>
                <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-md">Pure backward search inside the monad; intractable for realistic programs. See TODO_0082.</td>
                <td class="py-2 pl-3 text-gray-700 dark:text-gray-300 font-mono text-[11px]">{`{ valid: true }`} if a proof is found at all</td>
              </tr>
            </tbody>
          </table>
        </div>

        <div class="grid grid-cols-1 md:grid-cols-3 gap-3 mt-4 text-xs">
          <div class="rounded border border-emerald-200 dark:border-emerald-700 bg-emerald-50 dark:bg-emerald-900/15 p-3">
            <div class="font-semibold text-emerald-800 dark:text-emerald-200 uppercase tracking-wider">full</div>
            <p class="text-gray-700 dark:text-gray-300 mt-1 leading-snug">Fastest. The kernel admits a single unverified <em>modeSwitch</em> step at the monad, justified by the residual-state check.</p>
          </div>
          <div class="rounded border border-blue-200 dark:border-blue-700 bg-blue-50 dark:bg-blue-900/15 p-3">
            <div class="font-semibold text-blue-800 dark:text-blue-200 uppercase tracking-wider">guided</div>
            <p class="text-gray-700 dark:text-gray-300 mt-1 leading-snug">Fully verified. The forward engine acts as an oracle; every step it took is elaborated into a kernel-checkable ILL term.</p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-600 bg-gray-50 dark:bg-gray-900/20 p-3">
            <div class="font-semibold text-gray-700 dark:text-gray-300 uppercase tracking-wider">off</div>
            <p class="text-gray-700 dark:text-gray-300 mt-1 leading-snug">Reference semantics. Useful only on toy goals; kept to prove the bridge is a strict optimisation, not a requirement.</p>
          </div>
        </div>

        <p class="text-xs text-gray-600 dark:text-gray-400 mt-3 leading-snug">
          Bridge source: <code class="font-mono">lib/prover/bridge.js</code>. The bridge profile is independent
          from the forward-engine optimisation profile (<code class="font-mono">bare</code> /
          <code class="font-mono"> fast</code> / <code class="font-mono">evm</code>) — they compose freely.
        </p>
      </SectionCard>

    </Page>
  );
}
