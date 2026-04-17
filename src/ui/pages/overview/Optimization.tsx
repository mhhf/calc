/**
 * Optimization deep dive.
 *
 * Optimization is not a stack layer. Each module in engine/opt/ provides a
 * wrap() function that replaces a lower-layer function with an instrumented
 * version — the wrapper must have identical observable behavior modulo
 * performance. Turning everything off ("bare" profile) must still work.
 *
 * This page shows:
 *   - the six cross-cutting modules
 *   - the profile matrix (bare / fast / evm) across them
 *   - the injection pattern (schematic SVG: original fn wrapped by opt → same signature)
 *   - the differential testing story (how we trust that wraps preserve semantics)
 */

import { For } from 'solid-js';
import { useHashComponent } from './blocks/useHashComponent';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import DetailPanel from './blocks/DetailPanel';
import Intro from './blocks/Intro';
import ComponentBox from './blocks/ComponentBox';
import { DEEP_DIVES } from './data/meta';
import { DEEPDIVE_ACCENT } from './data/palette';
import { componentsByCluster } from './data/components';
import type { Component } from './data/types';

/** Profile levels — in wrapping order (each profile enables a superset). */
type Profile = 'bare' | 'fast' | 'evm';
const PROFILES: Profile[] = ['bare', 'fast', 'evm'];

interface OptEntry {
  /** Component id; must match components.ts */
  id: string;
  /** Which lower-layer function this module wraps. */
  wraps: string;
  /** How the optimization speeds things up. */
  mechanism: string;
  /** Enabled under these profiles. */
  enabled: Record<Profile, boolean>;
  /** Differential test story. */
  diff: string;
}

const OPTS: OptEntry[] = [
  {
    id: 'engine.opt.fingerprint',
    wraps: 'strategy.candidates()',
    mechanism: 'First-argument hash index — O(1) bucket → O(k) candidates vs O(n) full scan.',
    enabled: { bare: false, fast: true, evm: true },
    diff: 'Check: candidates(fingerprint) ⊆ candidates(predicate-filter) AND set equality after match.',
  },
  {
    id: 'engine.opt.prediction',
    wraps: 'strategy.candidates()',
    mechanism: 'Per-rule applicability pre-check on bound args before full unification.',
    enabled: { bare: false, fast: true, evm: true },
    diff: 'Any predicted-false rule must fail on full match too; else regression.',
  },
  {
    id: 'engine.opt.compiled-clauses',
    wraps: 'backchain.prove()',
    mechanism: 'Zero-subgoal clauses → direct hash lookup; ground-then-lookup compiled into one op.',
    enabled: { bare: false, fast: true, evm: true },
    diff: 'Same bindings as full clause resolution across fuzz inputs (tools/fuzz-ffi.js).',
  },
  {
    id: 'engine.opt.existential-compile',
    wraps: 'backchain.prove() (∃-chain)',
    mechanism: 'Per-goal FFI fast-path for existential resolution; specializes chain at compile time.',
    enabled: { bare: false, fast: true, evm: true },
    diff: 'Compare θ from compiled ∃-chain vs full clause resolution.',
  },
  {
    id: 'engine.opt.ffi',
    wraps: 'backchain.prove() (persistent)',
    mechanism: 'state → FFI → compiled clause → clause. FFI failure is advisory (falls through).',
    enabled: { bare: false, fast: true, evm: true },
    diff: 'noFFI adversarial suite runs without FFI; output must match FFI-on exactly.',
  },
  {
    id: 'engine.opt.structural-memo',
    wraps: 'explore() descent',
    mechanism: 'Control hash → subtree skip; avoids exploring isomorphic states twice.',
    enabled: { bare: false, fast: false, evm: true },
    diff: 'With memo off, explore must visit all same leaves (possibly more copies).',
  },
];

const PROFILE_DESC: Record<Profile, string> = {
  bare: 'All optimizations off. Pure reference semantics. Slow but maximally auditable.',
  fast: 'Common-path optimizations. Baseline for non-heavy workloads.',
  evm:  'All opts + EVM-specific structural memoization. Default for EVM symbolic execution.',
};

function InjectionDiagram() {
  return (
    <svg viewBox="0 0 900 160" class="w-full max-w-3xl mx-auto" role="img" aria-label="Optimization injection schematic">
      <defs>
        <marker id="opt-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto-start-reverse">
          <path d="M 0 0 L 8 4 L 0 8 z" fill="currentColor" />
        </marker>
      </defs>
      <g>
        <rect x="30" y="55" width="180" height="50" rx="8" class="fill-amber-50 dark:fill-amber-900/20 stroke-amber-400" stroke-width="2" />
        <text x="120" y="80" text-anchor="middle" class="fill-amber-800 dark:fill-amber-200" font-weight="700" font-size="13" font-family="ui-monospace">fn(x)</text>
        <text x="120" y="96" text-anchor="middle" class="fill-gray-600 dark:fill-gray-400" font-size="10">Generic Core / LNL fn</text>
      </g>
      <g class="text-gray-500 dark:text-gray-400">
        <path d="M 215 80 L 340 80" fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#opt-arrow)" />
        <text x="278" y="70" text-anchor="middle" font-size="10" class="fill-current">opt.wrap(fn)</text>
      </g>
      <g>
        <rect x="345" y="30" width="260" height="100" rx="8" class="fill-orange-50 dark:fill-orange-900/20 stroke-orange-400" stroke-width="2" />
        <text x="475" y="55" text-anchor="middle" class="fill-orange-800 dark:fill-orange-200" font-weight="700" font-size="13" font-family="ui-monospace">fn'(x)</text>
        <text x="475" y="75" text-anchor="middle" class="fill-gray-700 dark:fill-gray-300" font-size="10">index lookup, cache check, …</text>
        <text x="475" y="93" text-anchor="middle" class="fill-gray-500 dark:fill-gray-400" font-size="10">if hit: return fast-path</text>
        <text x="475" y="109" text-anchor="middle" class="fill-gray-500 dark:fill-gray-400" font-size="10">else: call fn(x)  // fall through</text>
      </g>
      <g class="text-gray-500 dark:text-gray-400">
        <path d="M 610 80 L 735 80" fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#opt-arrow)" />
        <text x="672" y="70" text-anchor="middle" font-size="10" class="fill-current">identical signature</text>
      </g>
      <g>
        <rect x="740" y="55" width="140" height="50" rx="8" class="fill-gray-100 dark:fill-gray-800 stroke-gray-400" stroke-width="2" />
        <text x="810" y="80" text-anchor="middle" class="fill-gray-800 dark:fill-gray-200" font-weight="600" font-size="12">caller</text>
        <text x="810" y="96" text-anchor="middle" class="fill-gray-500 dark:fill-gray-400" font-size="10">unaware of wrap</text>
      </g>
    </svg>
  );
}

export default function Optimization() {
  const meta = DEEP_DIVES.find(d => d.id === 'optimization')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);
  const optComponents = componentsByCluster('engine.opt');

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      subtitle="Six modules that wrap lower-layer functions. Not a stack layer — just cross-cutting instrumentation. Turning them off preserves soundness; only performance changes."
      accentClass={DEEPDIVE_ACCENT.optimization}
    >
      <DetailPanel component={selected()} onClose={() => setSelected(null)} />

      <Intro>
        The <strong>optimization modules</strong> are the only genuinely cross-cutting layer in CALC. Each module
        exports a <code>wrap(fn)</code> that takes a lower-layer function and returns an equivalent but faster
        one; the composition root decides which wrappers to apply. Profiles (<em>bare</em>, <em>fast</em>,
        <em>evm</em>) are just presets for which wrappers to enable. Disabling everything keeps the engine sound,
        it just gets slower.
      </Intro>

      <SectionCard
        title="The six modules"
        subtitle="Each opt module exports a wrap(fn) with an identical signature to the function it instruments. A composition root wires them in at assembly time."
      >
        <div class="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 gap-2">
          <For each={optComponents}>
            {(c) => (
              <ComponentBox
                component={c}
                onSelect={setSelected}
                selected={selected()?.id === c.id}
              />
            )}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="Injection pattern"
        subtitle="Identical signature guarantees the caller cannot observe whether wrapping happened. The optimization is required to fall through to the original function on miss — that's the safety property."
      >
        <InjectionDiagram />
      </SectionCard>

      <SectionCard
        title="Profile matrix"
        subtitle="Three profiles: bare (nothing), fast (common-path), evm (all). A profile is a Set of modules to wrap. Differential tests run all profiles and compare outputs."
      >
        <div class="overflow-x-auto">
          <table class="w-full text-xs border-collapse">
            <thead>
              <tr class="text-left">
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Module</th>
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Wraps</th>
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Mechanism</th>
                <For each={PROFILES}>
                  {(p) => (
                    <th class="pb-2 px-2 text-center font-semibold text-gray-600 dark:text-gray-400">{p}</th>
                  )}
                </For>
                <th class="pb-2 pl-3 font-semibold text-gray-600 dark:text-gray-400">Differential test</th>
              </tr>
            </thead>
            <tbody>
              <For each={OPTS}>
                {(o) => (
                  <tr class="border-t border-gray-200 dark:border-gray-700 align-top">
                    <td class="py-2 pr-3 font-mono text-gray-800 dark:text-gray-200">{o.id.replace('engine.opt.', '')}</td>
                    <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 font-mono text-[11px]">{o.wraps}</td>
                    <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-sm">{o.mechanism}</td>
                    <For each={PROFILES}>
                      {(p) => (
                        <td class="py-2 px-2 text-center">
                          <span class={`inline-block w-4 h-4 rounded-full ${o.enabled[p] ? 'bg-orange-500 dark:bg-orange-400' : 'border border-gray-300 dark:border-gray-600'}`}
                                title={`${p}: ${o.enabled[p] ? 'on' : 'off'}`} />
                        </td>
                      )}
                    </For>
                    <td class="py-2 pl-3 text-gray-700 dark:text-gray-300 leading-snug max-w-sm">{o.diff}</td>
                  </tr>
                )}
              </For>
            </tbody>
          </table>
        </div>

        <div class="grid grid-cols-1 md:grid-cols-3 gap-3 mt-4 text-xs">
          <For each={PROFILES}>
            {(p) => (
              <div class="rounded border border-orange-200 dark:border-orange-700 bg-orange-50 dark:bg-orange-900/15 p-3">
                <div class="font-semibold text-orange-800 dark:text-orange-200 uppercase tracking-wider">{p}</div>
                <p class="text-gray-700 dark:text-gray-300 mt-1 leading-snug">{PROFILE_DESC[p]}</p>
              </div>
            )}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="Why optimization is optimization, not logic"
        subtitle="If an opt module's output ever differs from the unwrapped function, the module is buggy — never the calculus."
      >
        <div class="grid grid-cols-1 md:grid-cols-2 gap-3 text-sm">
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">FFI is optimization, theory is semantics</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Every FFI predicate has backward clause definitions. The clause version is the ground truth;
              the FFI is a fast path. FFI failure → fall through to clauses. Drop-in replacement.
            </p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Testable by construction</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              The bare profile disables everything — a trivially-comparable reference. Every opt passes
              a differential test: run with/without the module and compare outputs byte-for-byte.
            </p>
          </div>
        </div>
      </SectionCard>

    </Page>
  );
}
