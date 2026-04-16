/**
 * Applications deep dive — ILL → binary arithmetic → EVM → multisig.
 *
 * Shows:
 *   - connective palette (pulled live from getFormulaConnectives)
 *   - binary arithmetic theory summary + FFI provenance
 *   - EVM state evolution diagram (stack / memory / storage / PC)
 *   - multisig symbolic instance
 *   - how to add a new program
 */

import { createMemo, For, Show } from 'solid-js';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import DetailPanel from './blocks/DetailPanel';
import ComponentBox from './blocks/ComponentBox';
import { useHashComponent } from './blocks/useHashComponent';
import { DEEP_DIVES } from './data/meta';
import { DEEPDIVE_ACCENT } from './data/palette';
import { getComponent } from './data/components';
import { getFormulaConnectives } from '../../lib/calculus';
import type { Component } from './data/types';

function ConnectivePalette() {
  const conns = createMemo(() => {
    try { return getFormulaConnectives(); } catch { return []; }
  });
  return (
    <div class="grid grid-cols-2 sm:grid-cols-3 md:grid-cols-4 gap-2">
      <For each={conns()}>
        {(c) => (
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 px-3 py-2">
            <div class="flex items-center justify-between">
              <div class="font-bold text-gray-900 dark:text-white">{c.name}</div>
              <div class="font-mono text-xs text-gray-500">{c.ascii}</div>
            </div>
            <div class="text-[11px] text-gray-500 dark:text-gray-400 flex items-center gap-1.5 mt-1">
              <span class={
                c.polarity === 'positive'
                  ? 'text-green-600 dark:text-green-400'
                  : c.polarity === 'negative'
                    ? 'text-red-600 dark:text-red-400'
                    : 'text-gray-500'
              }>
                {c.polarity}
              </span>
              <Show when={c.category}>
                <span class="opacity-60">· {c.category}</span>
              </Show>
            </div>
          </div>
        )}
      </For>
      <Show when={conns().length === 0}>
        <div class="text-xs text-gray-500 dark:text-gray-400 italic col-span-full">Calculus not loaded — connective palette unavailable in this context.</div>
      </Show>
    </div>
  );
}

function EVMStateDiagram() {
  // Simplified EVM state evolution: instruction consumes/produces on stack / memory / storage / pc
  return (
    <svg viewBox="0 0 700 280" class="w-full max-w-4xl mx-auto">
      <defs>
        <marker id="evm-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto-start-reverse">
          <path d="M 0 0 L 8 4 L 0 8 z" fill="currentColor" />
        </marker>
      </defs>

      {/* State slots */}
      <g class="text-gray-800 dark:text-gray-100">
        {([
          { x: 40,  y: 40,  w: 160, h: 60, label: 'Stack',    fact: 'stack(S)',          desc: 'LIFO; ops push/pop' },
          { x: 40,  y: 120, w: 160, h: 60, label: 'Memory',   fact: 'mem(M)',            desc: 'arrlit (byte array)' },
          { x: 40,  y: 200, w: 160, h: 60, label: 'Storage',  fact: 'storage(K, V)',     desc: 'persistent; linear' },
          { x: 260, y: 40,  w: 160, h: 60, label: 'PC',       fact: 'pc(P)',             desc: 'program counter' },
          { x: 260, y: 120, w: 160, h: 60, label: 'Code',     fact: 'bytecode(BC) *',    desc: 'preserved; shared' },
          { x: 260, y: 200, w: 160, h: 60, label: 'Gas',      fact: 'gas(N)',            desc: 'bounded resource' },
        ]).map((box) => (
          <g>
            <rect x={box.x} y={box.y} width={box.w} height={box.h} rx={6}
              class="fill-slate-50 dark:fill-slate-900/50 stroke-slate-300 dark:stroke-slate-700" stroke-width="1.5" />
            <text x={box.x + 10} y={box.y + 22} class="fill-current" font-weight="700" font-size="13">{box.label}</text>
            <text x={box.x + 10} y={box.y + 40} class="fill-current" font-family="ui-monospace" font-size="11">{box.fact}</text>
            <text x={box.x + 10} y={box.y + 54} class="fill-current opacity-60" font-size="10">{box.desc}</text>
          </g>
        ))}
      </g>

      {/* Opcode flow → updates PC, consumes stack args, produces new stack, maybe memory/storage */}
      <g class="text-blue-600 dark:text-blue-400">
        <rect x={490} y={100} width={180} height={80} rx={8}
          class="fill-blue-50 dark:fill-blue-900/20 stroke-blue-400" stroke-width="2" />
        <text x={580} y={130} text-anchor="middle" class="fill-current" font-weight="700" font-size="13">Opcode step</text>
        <text x={580} y={152} text-anchor="middle" class="fill-current" font-family="ui-monospace" font-size="11">ADD, MUL, SLOAD, …</text>
        <text x={580} y={168} text-anchor="middle" class="fill-current opacity-70" font-size="10">one forward rule each</text>
      </g>

      {/* Arrows into opcode */}
      <g class="text-gray-500 dark:text-gray-400">
        <path d="M 200 70 C 300 70 400 140 490 140" fill="none" stroke="currentColor" stroke-width="1.3" marker-end="url(#evm-arrow)" />
        <path d="M 200 150 L 490 150" fill="none" stroke="currentColor" stroke-width="1.3" marker-end="url(#evm-arrow)" />
        <path d="M 200 230 C 300 230 400 160 490 160" fill="none" stroke="currentColor" stroke-width="1.3" marker-end="url(#evm-arrow)" />
        <path d="M 420 70  C 450 90  470 110 490 130" fill="none" stroke="currentColor" stroke-width="1.3" marker-end="url(#evm-arrow)" />
        <path d="M 420 150 L 490 150" fill="none" stroke="currentColor" stroke-width="1.3" marker-end="url(#evm-arrow)" />
        <path d="M 420 230 C 450 210 470 180 490 170" fill="none" stroke="currentColor" stroke-width="1.3" marker-end="url(#evm-arrow)" />

        {/* Loop back to pc (PC increment) */}
        <path d="M 670 140 C 720 140 720 40 400 40 L 340 40" fill="none" stroke="currentColor" stroke-width="1.3"
          stroke-dasharray="4 4" marker-end="url(#evm-arrow)" />
        <text x={560} y="30" text-anchor="middle" class="fill-current" font-size="10">PC ← PC + 1 (or jump)</text>
      </g>
    </svg>
  );
}

function ExecutionModes() {
  const rows = [
    { mode: 'Concrete forward', who: 'exec()', how: 'Committed choice: first match wins, no backtracking', when: 'Programs with unique execution path (EVM bytecode)' },
    { mode: 'Symbolic explore',  who: 'explore()', how: 'Exhaustive DFS with mutation/undo log; structural memo skips equivalent subtrees', when: 'Symbolic multisig; find all reachable states' },
    { mode: 'Backward search',    who: 'prove()',   how: 'Andreoli focusing in L3 + strategy in L4',         when: 'Derivability judgments; generating proof certificates' },
    { mode: 'Guided (bridge)',    who: 'lax-monad profile=guided', how: 'Backward asks forward for witnesses; forward delegates non-monadic proofs back', when: 'Programs that mix derivability with execution' },
  ];
  return (
    <div class="overflow-x-auto">
      <table class="w-full text-sm">
        <thead>
          <tr class="text-left text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400">
            <th class="px-3 py-2 font-semibold">Mode</th>
            <th class="px-3 py-2 font-semibold">API</th>
            <th class="px-3 py-2 font-semibold">How it works</th>
            <th class="px-3 py-2 font-semibold">Typical use</th>
          </tr>
        </thead>
        <tbody class="divide-y divide-gray-200 dark:divide-gray-700">
          <For each={rows}>
            {(r) => (
              <tr class="hover:bg-gray-50 dark:hover:bg-gray-700/30">
                <td class="px-3 py-2 font-semibold text-gray-900 dark:text-white">{r.mode}</td>
                <td class="px-3 py-2 font-mono text-xs text-blue-700 dark:text-blue-400">{r.who}</td>
                <td class="px-3 py-2 text-gray-700 dark:text-gray-300">{r.how}</td>
                <td class="px-3 py-2 text-gray-500 dark:text-gray-400 text-xs">{r.when}</td>
              </tr>
            )}
          </For>
        </tbody>
      </table>
    </div>
  );
}

export default function Apps() {
  const meta = DEEP_DIVES.find(d => d.id === 'applications')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);

  const components = [
    getComponent('calc.ill'),
    getComponent('calc.ill.bin'),
    getComponent('calc.ill.evm'),
    getComponent('calc.ill.multisig'),
    getComponent('engine.ill.connectives'),
    getComponent('engine.ill.binlit-theory'),
    getComponent('engine.ill.bytecode-normalize'),
    getComponent('engine.ill.ffi'),
  ].filter(Boolean) as Component[];

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      subtitle="CALC ships with one logic (ILL) and one fully-developed program family (EVM). New programs plug in at the ill/ layer — theories and FFI are optional."
      accentClass={DEEPDIVE_ACCENT.applications}
    >
      <SectionCard
        title="ILL connective palette"
        subtitle="Loaded live from the bundled calculus. Polarity drives the focusing phase (green = eager, red = invertible)."
      >
        <ConnectivePalette />
      </SectionCard>

      <SectionCard
        title="Binary arithmetic theory"
        subtitle="Theory of bounded naturals: bits normalized by binlit ↔ i/o/e, comparison by gt/lt/eq, FFI acceleration for speed."
      >
        <div class="grid grid-cols-1 md:grid-cols-3 gap-3 text-sm">
          <div class="rounded bg-gray-50 dark:bg-gray-900/30 border border-gray-200 dark:border-gray-700 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Representation</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              <code class="font-mono">binlit(n)</code> is a natural number literal. The binlit theory rewrites it
              to a bit tree <code class="font-mono">i/o/e</code> at matching time — so <code class="font-mono">5</code>
              and <code class="font-mono">i(o(i(e)))</code> are definitionally equal.
            </p>
          </div>
          <div class="rounded bg-gray-50 dark:bg-gray-900/30 border border-gray-200 dark:border-gray-700 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Provability (backward)</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Every arithmetic predicate has backward clauses: <code class="font-mono">!plus A B C</code>,
              <code class="font-mono">!eq X Y</code>, etc. FFI is an optimization; turning it off degrades
              performance but never soundness.
            </p>
          </div>
          <div class="rounded bg-gray-50 dark:bg-gray-900/30 border border-gray-200 dark:border-gray-700 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">ZK chip</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Binlit chip encodes plus / times / eq / lt as Plonky3 rows; witness generation proves the
              binlit result matches the bit-tree derivation step-by-step.
            </p>
          </div>
        </div>
      </SectionCard>

      <SectionCard
        title="EVM state evolution"
        subtitle="Stack, memory, storage, pc, code, gas — each is a linear fact (or preserved, for shared code). An opcode step is one forward rule: consume arguments, produce new state."
      >
        <EVMStateDiagram />
      </SectionCard>

      <SectionCard
        title="Execution modes"
        subtitle="Forward engine exposes four modes; the right choice depends on whether the program is concrete or symbolic and whether you need a certificate."
      >
        <ExecutionModes />
      </SectionCard>

      <SectionCard
        title="Application components"
        subtitle="Every application touchpoint in the registry. Click to jump."
      >
        <div class="grid grid-cols-1 sm:grid-cols-2 md:grid-cols-3 gap-2">
          <For each={components}>
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
        title="Adding a new program"
        subtitle="The playbook, distilled from EVM and multisig."
      >
        <ol class="list-decimal pl-5 space-y-2 text-sm text-gray-700 dark:text-gray-300">
          <li>Define state predicates (linear vs persistent) in <code class="font-mono text-xs">.calc</code>.</li>
          <li>Write forward rules in <code class="font-mono text-xs">.ill</code> — one per state-transition.</li>
          <li>Add theories if domain-specific (binary arithmetic, sha3) — usually via an existing FFI module.</li>
          <li>If ZK is required, declare chips in <code class="font-mono text-xs">zk/sequent-certifier/chips/</code>. Custom chips handle program-specific semantics.</li>
          <li>Add tests: <code class="font-mono text-xs">.ill</code>-native in <code class="font-mono text-xs">calculus/ill/tests/</code>, JS drivers in <code class="font-mono text-xs">tests/</code>.</li>
          <li>Benchmark with <code class="font-mono text-xs">bench:engine</code> / <code class="font-mono text-xs">bench:explore</code> and lock in via <code class="font-mono text-xs">bench:diff</code>.</li>
        </ol>
      </SectionCard>

      <DetailPanel component={selected()} onClose={() => setSelected(null)} />
    </Page>
  );
}
