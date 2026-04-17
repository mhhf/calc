/**
 * Forward Engine deep dive.
 *
 * Covers:
 *   - Three-layer architecture: Generic Core → LNL → ILL (bottom-up)
 *   - matchOpts composition: 4 protocol factories frozen at assembly
 *   - Strategy stack: fingerprint → disc-tree → predicate filter
 *   - Two entry points: exec (committed choice) vs explore (exhaustive DFS)
 */

import { For } from 'solid-js';
import { useHashComponent } from './blocks/useHashComponent';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import LayerBand from './blocks/LayerBand';
import DetailPanel from './blocks/DetailPanel';
import Intro from './blocks/Intro';
import ComponentBox from './blocks/ComponentBox';
import { DEEP_DIVES } from './data/meta';
import { DEEPDIVE_ACCENT } from './data/palette';
import { layersByStack } from './data/layers';
import { getComponent } from './data/components';
import type { Component } from './data/types';

interface Factory {
  id: string;
  name: string;
  input: string;
  output: string;
  blurb: string;
}

const FACTORIES: Factory[] = [
  {
    id: 'pattern',
    name: 'pattern',
    input: 'compiled rule descriptor',
    output: 'match(state, rule) → {theta, consumed}',
    blurb: 'Structural unification against fact set. Builds per-rule binding skeletons; metavar analysis at compile-time; O(1) lookup via typed-array groups.',
  },
  {
    id: 'strategy',
    name: 'strategy',
    input: 'fact change delta',
    output: 'candidates(state) → iterable<rule>',
    blurb: 'Rule-selection stack: fingerprint index (exact head args) → discrimination tree (shape) → predicate catch-all. Each layer prunes before passing to the next.',
  },
  {
    id: 'backchain',
    name: 'backchain',
    input: 'persistent goal',
    output: 'prove(goal) → theta',
    blurb: 'SLD-style resolution for persistent predicates: state lookup → FFI → compiled clause → full clause resolution. FFI failure is advisory.',
  },
  {
    id: 'ffi',
    name: 'ffi',
    input: 'predicate + grounded args',
    output: 'result or fail',
    blurb: 'Foreign-function dispatch. Arithmetic (binlit), hashing (sha3), memory, arrlit. Every FFI predicate has backward clause definitions — FFI is optimization.',
  },
];

interface ModeRow {
  name: string;
  entry: string;
  semantics: string;
  state: string;
  use: string;
}

const MODES: ModeRow[] = [
  {
    name: 'exec()',
    entry: 'engine.forward',
    semantics: 'Committed-choice: apply any applicable rule; backtrack only on stuck.',
    state: 'Mutable — single fact-set threaded through the loop.',
    use: 'Concrete execution. EVM transaction replay. Forward-chaining simulation.',
  },
  {
    name: 'explore()',
    entry: 'engine.explore',
    semantics: 'Exhaustive DFS with undo log. Every rule branch is explored; memo prunes visited subtrees.',
    state: 'Mutable + Arena undo log (fact-set).',
    use: 'Symbolic execution. Contract verification. Branch coverage.',
  },
  {
    name: 'backchain()',
    entry: 'engine.backchain',
    semantics: 'SLD-style resolution against persistent clauses. Ordered alternative chains.',
    state: 'Bindings only — no side-effects on fact set.',
    use: 'Proving persistent goals inside forward rules (guards, arithmetic).',
  },
];

function CompositionDiagram() {
  return (
    <svg viewBox="0 0 1000 250" class="w-full max-w-4xl mx-auto" role="img" aria-label="matchOpts composition diagram">
      <defs>
        <marker id="eng-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto-start-reverse">
          <path d="M 0 0 L 8 4 L 0 8 z" fill="currentColor" />
        </marker>
      </defs>
      {/* Generic Core layer */}
      <g>
        <rect x="40" y="170" width="920" height="60" rx="10" class="fill-amber-50 dark:fill-amber-900/20 stroke-amber-400" stroke-width="2" />
        <text x="60" y="198" class="fill-amber-800 dark:fill-amber-200" font-weight="700" font-size="13">Generic Core</text>
        <text x="60" y="216" class="fill-gray-600 dark:fill-gray-400" font-size="11">exec · explore · match · strategy · backchain</text>
      </g>
      {/* matchOpts — interface layer */}
      <g>
        <rect x="40" y="105" width="920" height="50" rx="8" class="fill-white dark:fill-gray-800 stroke-gray-400" stroke-dasharray="4 2" stroke-width="1.5" />
        <text x="60" y="132" class="fill-gray-700 dark:fill-gray-300" font-weight="700" font-size="13">matchOpts</text>
        <text x="170" y="132" class="fill-gray-500 dark:fill-gray-400" font-size="11" font-family="ui-monospace">
          {'{ pattern, strategy, backchain, ffi }'}
        </text>
        {/* 4 factory chips */}
        <For each={FACTORIES}>
          {(f, i) => {
            const x = 480 + i() * 120;
            return (
              <g class="text-amber-700 dark:text-amber-400">
                <rect x={x} y={115} width={110} height={28} rx={4} class="fill-amber-100 dark:fill-amber-900/40 stroke-current" stroke-width="1" />
                <text x={x + 55} y={133} text-anchor="middle" font-size="10" font-weight="600" class="fill-current" font-family="ui-monospace">{f.name}()</text>
              </g>
            );
          }}
        </For>
      </g>
      {/* Assembly providers: LNL + ILL layers on top */}
      <g>
        <rect x="40" y="30" width="440" height="50" rx="8" class="fill-sky-50 dark:fill-sky-900/20 stroke-sky-400" stroke-width="2" />
        <text x="60" y="50" class="fill-sky-800 dark:fill-sky-200" font-weight="700" font-size="13">LNL</text>
        <text x="60" y="68" class="fill-gray-600 dark:fill-gray-400" font-size="11">persistent · loli · loli-drain · existential</text>
      </g>
      <g>
        <rect x="520" y="30" width="440" height="50" rx="8" class="fill-indigo-50 dark:fill-indigo-900/20 stroke-indigo-400" stroke-width="2" />
        <text x="540" y="50" class="fill-indigo-800 dark:fill-indigo-200" font-weight="700" font-size="13">ILL</text>
        <text x="540" y="68" class="fill-gray-600 dark:fill-gray-400" font-size="11">connectives · FFI · binlit-theory · calculus-config</text>
      </g>
      {/* Arrows from LNL + ILL down into matchOpts */}
      <g class="text-gray-500 dark:text-gray-400">
        <path d="M 260 82 L 260 105" fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#eng-arrow)" />
        <text x="278" y="96" font-size="9" class="fill-current">provides</text>
        <path d="M 740 82 L 740 105" fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#eng-arrow)" />
        <text x="758" y="96" font-size="9" class="fill-current">provides</text>
      </g>
      {/* Arrow from matchOpts down into Generic Core */}
      <g class="text-gray-500 dark:text-gray-400">
        <path d="M 500 155 L 500 170" fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#eng-arrow)" />
        <text x="510" y="166" font-size="9" class="fill-current">callbacks wired at runtime</text>
      </g>
    </svg>
  );
}

function StrategyStack(props: { onSelect: (c: Component) => void; selectedId?: string }) {
  const strat = getComponent('engine.strategy')!;
  const rows = [
    { title: 'Fingerprint index',        detail: 'Per-predicate hash-of-first-arg → bucket. Fast O(1) rejection when rule head disagrees on ground prefix.' },
    { title: 'Discrimination tree',      detail: 'Shape-indexed trie for structural prefix matching. Finer than fingerprint — handles variable-position arguments.' },
    { title: 'Predicate filter',         detail: 'Catch-all: if no index hits, walk all rules with matching head predicate. Always sound, always complete.' },
  ];
  return (
    <div class="space-y-2">
      <div class="mb-2">
        <ComponentBox component={strat} onSelect={props.onSelect} selected={props.selectedId === strat.id} />
      </div>
      <ul class="space-y-1.5">
        <For each={rows}>
          {(r, i) => (
            <li class="flex items-start gap-2 text-xs">
              <span class="font-mono text-[10px] rounded bg-amber-100 dark:bg-amber-900/30 text-amber-800 dark:text-amber-200 w-8 text-center py-0.5 shrink-0">T{i() + 1}</span>
              <div class="min-w-0">
                <div class="font-semibold text-gray-900 dark:text-white">{r.title}</div>
                <div class="text-gray-600 dark:text-gray-400 leading-snug">{r.detail}</div>
              </div>
            </li>
          )}
        </For>
      </ul>
    </div>
  );
}

export default function Engine() {
  const meta = DEEP_DIVES.find(d => d.id === 'engine')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);
  const layers = layersByStack('engine');

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      subtitle="Stackified forward + symbolic engine. A generic core is parameterized by matchOpts — four factories that LNL and ILL layers provide. Optimization wraps, never inserts."
      accentClass={DEEPDIVE_ACCENT.engine}
    >
      <DetailPanel component={selected()} onClose={() => setSelected(null)} />

      <Intro>
        The <strong>forward engine</strong> runs a program from an initial state toward a final one by applying
        rules. It's three strict layers: a <em>generic core</em> (match / strategy / forward / explore), an
        <em> LNL</em> layer that adds the linear-vs-persistent distinction, and an <em>ILL</em> layer that plugs
        in connectives, theories, and FFI. Optimizations <em>wrap</em> layers at the composition root — they
        never add their own layer. Turn them off (bare profile) and the engine is slower, never less sound.
      </Intro>

      <SectionCard
        title="Three-layer stack"
        subtitle="Bottom-up: Generic Core is the core loop; LNL adds the linear/persistent distinction; ILL plugs in connectives, theories, and FFI. Each higher layer PROVIDES callbacks to the next lower one."
      >
        <div class="space-y-3">
          <For each={layers}>
            {(layer) => <LayerBand layer={layer} onSelect={setSelected} selectedId={selected()?.id} />}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="matchOpts composition"
        subtitle="The point where the generic engine is assembled for a specific calculus. Four protocol factories are frozen into a single object; the core engine dispatches through them without knowing what's above."
      >
        <CompositionDiagram />
        <div class="grid grid-cols-1 md:grid-cols-2 gap-3 mt-4">
          <For each={FACTORIES}>
            {(f) => (
              <div class="rounded border border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800/40 p-3">
                <div class="flex items-baseline justify-between gap-2">
                  <h4 class="font-mono font-bold text-amber-700 dark:text-amber-300">{f.name}()</h4>
                  <span class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400">Factory</span>
                </div>
                <div class="text-xs mt-2 space-y-1">
                  <div><span class="uppercase text-[10px] tracking-wider text-gray-500 dark:text-gray-400">in</span> <span class="text-gray-700 dark:text-gray-300">{f.input}</span></div>
                  <div><span class="uppercase text-[10px] tracking-wider text-gray-500 dark:text-gray-400">out</span> <span class="text-gray-700 dark:text-gray-300">{f.output}</span></div>
                </div>
                <p class="text-xs text-gray-600 dark:text-gray-400 mt-2 leading-snug">{f.blurb}</p>
              </div>
            )}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="Strategy stack"
        subtitle="Rule selection is a pipeline of increasingly general indexes. Tier 1 is free-by-index; Tier 3 is complete but linear. The tiers are AND-composed — a rule must pass each layer."
      >
        <StrategyStack onSelect={setSelected} selectedId={selected()?.id} />
      </SectionCard>

      <SectionCard
        title="Entry points"
        subtitle="Three modes, one compiled rule set. The modes differ in strategy (committed vs exhaustive) and in what they produce."
      >
        <div class="overflow-x-auto">
          <table class="w-full text-xs border-collapse">
            <thead>
              <tr class="text-left">
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Entry</th>
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Semantics</th>
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">State model</th>
                <th class="pb-2 font-semibold text-gray-600 dark:text-gray-400">Used for</th>
              </tr>
            </thead>
            <tbody>
              <For each={MODES}>
                {(m) => {
                  const comp = getComponent(m.entry);
                  return (
                    <tr class="border-t border-gray-200 dark:border-gray-700">
                      <td class="py-2 pr-3 align-top">
                        <div class="font-mono font-bold text-gray-900 dark:text-white">{m.name}</div>
                        {comp && (
                          <button
                            type="button"
                            onClick={() => setSelected(comp)}
                            class="text-[10px] text-blue-600 dark:text-blue-400 hover:underline"
                          >
                            {comp.id}
                          </button>
                        )}
                      </td>
                      <td class="py-2 pr-3 align-top text-gray-700 dark:text-gray-300 leading-snug max-w-md">{m.semantics}</td>
                      <td class="py-2 pr-3 align-top text-gray-700 dark:text-gray-300 leading-snug max-w-md">{m.state}</td>
                      <td class="py-2 align-top text-gray-700 dark:text-gray-300 leading-snug max-w-md">{m.use}</td>
                    </tr>
                  );
                }}
              </For>
            </tbody>
          </table>
        </div>
      </SectionCard>

      <SectionCard
        title="Why matchOpts matters"
        subtitle="Single assembly point means a single place to understand, audit, and optimize. Swap ILL for NumAL by swapping the top layer only."
      >
        <div class="grid grid-cols-1 md:grid-cols-3 gap-3 text-sm">
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">One rule set, three modes</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              exec, explore, and backchain all use the same compiled rules. A speedup at compile-time
              benefits every entry point simultaneously.
            </p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Optimization wraps, never inserts</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Opt modules <code class="font-mono">wrap()</code> factory functions at composition. They
              are not a stack layer. Bare profile disables all — engine still works.
            </p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Calculus pluggability</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              The ILL layer could be replaced with a different logic (NumAL, LL) by swapping the top
              provider. Generic Core + LNL are calculus-agnostic.
            </p>
          </div>
        </div>
      </SectionCard>

    </Page>
  );
}
