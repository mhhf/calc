/**
 * Compilation Pipeline deep dive.
 *
 * Six passes from source to running engine:
 *   Parse → Compile → Compose → Assemble → Runtime → Certify
 *
 * Plus the fusion-symex spectrum: a horizontal slider where "how aggressively
 * do we fuse rules at compile-time" meets "how much do we defer to runtime
 * symbolic exploration". Grade-0 at the left (most compile-time work),
 * pure symbolic exec at the right (all work at runtime).
 */

import { For } from 'solid-js';
import { useHashComponent } from './blocks/useHashComponent';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import DetailPanel from './blocks/DetailPanel';
import Intro from './blocks/Intro';
import ComponentBox from './blocks/ComponentBox';
import { StageBadge } from './blocks/Badge';
import { DEEP_DIVES } from './data/meta';
import { DEEPDIVE_ACCENT } from './data/palette';
import { getComponent } from './data/components';
import type { Component, Stage } from './data/types';

interface Pass {
  id: string;
  /** Canonical stage this pass belongs to (for color alignment with Pipeline view). */
  stage: Stage;
  title: string;
  oneLiner: string;
  input: string;
  output: string;
  components: string[]; // component ids
  details: string;
}

const PASSES: Pass[] = [
  {
    id: 'parse',
    stage: 'parse',
    title: 'Parse',
    oneLiner: 'Source text → AST',
    input: '.calc + .rules + .ill files',
    output: 'Abstract syntax tree (content-addressed in the store)',
    components: ['parser.earley', 'parser.earley-grammar', 'parser.declarations', 'parser.sequent', 'parser.rules', 'parser.meta'],
    details:
      'A single Earley core runs against three generated grammars: meta (@extends chains), program (ILL connectives + user types), and rules (sequent notation). Grammars are generated from .calc annotations.',
  },
  {
    id: 'compile',
    stage: 'compile',
    title: 'Compile',
    oneLiner: 'AST → rule descriptors + compiled clauses',
    input: 'Rule AST, bound variable analysis',
    output: 'Compiled rule: de Bruijn slots, metavar classes, premise skeleton',
    components: ['engine.compile', 'prover.rule-interpreter', 'engine.convert'],
    details:
      'Every rule is analyzed once: which meta-variables are bound by the head, which are existential, which slots are preserved. The output is a flat descriptor re-executed per step — no re-parsing at runtime.',
  },
  {
    id: 'compose',
    stage: 'compile',
    title: 'Compose',
    oneLiner: 'Rule algebra: cut-elim, specialization, fusion, SROA',
    input: 'Compiled rules + grade-0 predicate map',
    output: 'A smaller/faster rule set, semantically equivalent',
    components: ['engine.compile', 'engine.opt.compiled-clauses'],
    details:
      'Grade-0 erasure (Atkey 2018, Choudhury et al. 2021) lets us treat certain persistent facts as compile-time scaffolding. Passes: (1) cut-elim between rules, (2) specialization against ground grade-0 clauses, (3) basic-block fusion of deterministic chains, (4) scalar replacement of aggregates.',
  },
  {
    id: 'assemble',
    stage: 'compile',
    title: 'Assemble',
    oneLiner: 'Wire up matchOpts, strategies, FFI dispatch',
    input: 'Composed rules + optimization profile (bare / fast / evm)',
    output: 'A running engine binding with closures frozen',
    components: ['engine.match', 'engine.strategy', 'engine.ill.calculus-config'],
    details:
      'matchOpts is composed from four protocol factories: pattern, strategy, backchain, ffi. Optimizations (compiled-clauses, fingerprint, prediction, etc.) wrap specific layer functions via wrap() at this single assembly point.',
  },
  {
    id: 'runtime',
    stage: 'execute',
    title: 'Runtime',
    oneLiner: 'Forward / backward / symbolic execution',
    input: 'Initial state (facts multiset) + assembled engine',
    output: 'Proof term OR terminal state OR set of symbolic leaves',
    components: ['engine.forward', 'engine.explore', 'prover.focused'],
    details:
      'Three modes dispatch on the same compiled rule set: exec() (committed choice), explore() (exhaustive DFS + undo log), prover.focused() (Andreoli focusing). All three see identical rule descriptors, so optimization work at compile-time benefits everyone.',
  },
  {
    id: 'certify',
    stage: 'certify',
    title: 'Certify',
    oneLiner: 'Proof term → Plonky3 witness → STARK',
    input: 'Proof term (any mode)',
    output: 'Plonky3 witness + SNARK proof',
    components: ['zk.sequent-certifier', 'zk.chips'],
    details:
      '14 buses carry values between chips. Rule chip dispatches premises; binlit / sha3 / memory / arrlit chips verify FFI calls; custom chips encode per-program semantics (EVM opcodes). Verification never re-implements the prover — it re-checks the proof term via rule chip lookup.',
  },
];

const SPECTRUM_POINTS: { x: number; label: string; tooltip: string }[] = [
  { x: 4,  label: 'grade-0 erase',   tooltip: 'Persistent facts with grade 0 are compile-time scaffolding. Erased; no runtime cost.' },
  { x: 22, label: 'specialize',      tooltip: 'Resolve persistent goals against ground clauses at compile-time.' },
  { x: 40, label: 'BB fusion',       tooltip: 'Merge deterministic rule chains (e.g. opcode dispatch → single fused rule).' },
  { x: 58, label: 'SROA',            tooltip: 'Scalar replacement of aggregates: unpack tensors so unused components vanish.' },
  { x: 76, label: 'prediction',      tooltip: 'Pre-filter rule applicability at runtime (cheap, before full match).' },
  { x: 94, label: 'symbolic exec',   tooltip: 'All work deferred. Engine explores every reachable state.' },
];

function PipelineDiagram() {
  return (
    <svg viewBox="0 0 1200 110" class="w-full max-w-5xl mx-auto" role="img" aria-label="Compilation pipeline diagram">
      <defs>
        <marker id="comp-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto-start-reverse">
          <path d="M 0 0 L 8 4 L 0 8 z" fill="currentColor" />
        </marker>
      </defs>
      <g class="text-gray-500 dark:text-gray-400">
        <For each={PASSES}>
          {(pass, i) => {
            const step = 1200 / PASSES.length;
            const cx = step * (i() + 0.5);
            return (
              <>
                <rect x={cx - 55} y={25} width={110} height={50} rx="8"
                      class="fill-white dark:fill-gray-800 stroke-current" stroke-width="1.5" />
                <text x={cx} y={48} text-anchor="middle" font-size="12" font-weight="700"
                      class="fill-gray-900 dark:fill-white">{pass.title}</text>
                <text x={cx} y={66} text-anchor="middle" font-size="9"
                      class="fill-gray-500 dark:fill-gray-400" font-family="ui-monospace">{pass.id}</text>
                {i() < PASSES.length - 1 && (
                  <path d={`M ${cx + 58} 50 L ${cx + step - 58} 50`}
                        fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#comp-arrow)" />
                )}
              </>
            );
          }}
        </For>
      </g>
    </svg>
  );
}

function FusionSymexSpectrum() {
  return (
    <div class="relative">
      <svg viewBox="0 0 1000 80" class="w-full" role="img" aria-label="Fusion-symex spectrum">
        {/* Gradient bar */}
        <defs>
          <linearGradient id="spectrum-grad" x1="0" y1="0" x2="1" y2="0">
            <stop offset="0%" stop-color="#059669" />
            <stop offset="33%" stop-color="#0891b2" />
            <stop offset="66%" stop-color="#7c3aed" />
            <stop offset="100%" stop-color="#ec4899" />
          </linearGradient>
        </defs>
        <rect x="40" y="28" width="920" height="14" rx="7" fill="url(#spectrum-grad)" opacity="0.85" />
        {/* Axis endpoint labels */}
        <text x="40" y="22" font-size="11" font-weight="600" class="fill-gray-700 dark:fill-gray-300">
          compile-time
        </text>
        <text x="960" y="22" text-anchor="end" font-size="11" font-weight="600" class="fill-gray-700 dark:fill-gray-300">
          run-time
        </text>
        {/* Checkpoint ticks */}
        <g class="text-gray-700 dark:text-gray-300">
          <For each={SPECTRUM_POINTS}>
            {(pt) => {
              const x = 40 + (pt.x / 100) * 920;
              return (
                <>
                  <line x1={x} y1={22} x2={x} y2={48} stroke="currentColor" stroke-width="1.5" />
                  <circle cx={x} cy={35} r="5" class="fill-white dark:fill-gray-900 stroke-current" stroke-width="1.5">
                    <title>{pt.tooltip}</title>
                  </circle>
                  <text x={x} y={64} text-anchor="middle" font-size="10" class="fill-current">
                    {pt.label}
                  </text>
                </>
              );
            }}
          </For>
        </g>
      </svg>
    </div>
  );
}

function PassCard(props: { pass: Pass; onSelect: (c: Component) => void; selectedId?: string }) {
  const comps = () => props.pass.components.map(id => getComponent(id)).filter(Boolean) as Component[];
  return (
    <div class="rounded-lg border border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800/40 p-4">
      <div class="flex items-center justify-between gap-2 flex-wrap">
        <div class="flex items-center gap-2">
          <span class="font-mono text-xs bg-cyan-100 dark:bg-cyan-900/30 text-cyan-800 dark:text-cyan-200 px-1.5 py-0.5 rounded">
            {props.pass.id}
          </span>
          <h4 class="font-bold text-gray-900 dark:text-white">{props.pass.title}</h4>
          <StageBadge stage={props.pass.stage} />
        </div>
        <span class="text-xs text-gray-500 dark:text-gray-400 italic">{props.pass.oneLiner}</span>
      </div>
      <div class="grid grid-cols-1 md:grid-cols-2 gap-2 mt-3 text-xs">
        <div class="rounded bg-gray-50 dark:bg-gray-900/30 border border-gray-200 dark:border-gray-700 p-2">
          <span class="uppercase text-[10px] tracking-wider text-gray-500 dark:text-gray-400">Input</span>
          <div class="text-gray-800 dark:text-gray-200 mt-0.5">{props.pass.input}</div>
        </div>
        <div class="rounded bg-gray-50 dark:bg-gray-900/30 border border-gray-200 dark:border-gray-700 p-2">
          <span class="uppercase text-[10px] tracking-wider text-gray-500 dark:text-gray-400">Output</span>
          <div class="text-gray-800 dark:text-gray-200 mt-0.5">{props.pass.output}</div>
        </div>
      </div>
      <p class="text-sm text-gray-700 dark:text-gray-300 mt-3 leading-snug">{props.pass.details}</p>
      <div class="mt-3">
        <div class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-1.5">
          Components
        </div>
        <div class="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 gap-2">
          <For each={comps()}>
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
    </div>
  );
}

export default function Compilation() {
  const meta = DEEP_DIVES.find(d => d.id === 'compilation')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      subtitle="Every calculus is compiled. Rules flow through six passes, each reducing the runtime cost or enabling an optimization."
      accentClass={DEEPDIVE_ACCENT.compilation}
    >
      <DetailPanel component={selected()} onClose={() => setSelected(null)} />

      <Intro>
        The <strong>compilation pipeline</strong> takes a <code>.calc</code> definition plus a <code>.rules</code>
        file and produces a runnable, cached calculus bundle. It runs six passes — parse, compile, compose,
        assemble, runtime-prep, certify — each either shrinking the runtime cost or unlocking a new optimization.
        Every pre-runtime pass is paid once per bundle and cached in <code>out/ill.json</code>.
      </Intro>

      <SectionCard
        title="Six passes"
        subtitle="Parse → Compile → Compose → Assemble → Runtime → Certify. All pre-runtime work is paid once per calculus bundle and cached in out/ill.json."
      >
        <PipelineDiagram />
      </SectionCard>

      <SectionCard
        title="Fusion-symex spectrum"
        subtitle="The fundamental compile-time vs run-time trade-off. Knobs on the left shift work into compile; knobs on the right let runtime explore symbolically. Profiles (bare, fast, evm) pick points on this axis."
      >
        <FusionSymexSpectrum />
        <div class="grid grid-cols-1 md:grid-cols-2 gap-3 mt-4 text-xs text-gray-700 dark:text-gray-300">
          <div class="rounded border border-emerald-200 dark:border-emerald-700 bg-emerald-50 dark:bg-emerald-900/15 p-3">
            <div class="font-semibold text-emerald-800 dark:text-emerald-200">Left: more compile-time</div>
            <p class="mt-1">Grade-0 facts erased. Rule chains fused into single steps. Persistent goals specialized against ground clauses. Big compile investment → tiny inner loop.</p>
          </div>
          <div class="rounded border border-pink-200 dark:border-pink-700 bg-pink-50 dark:bg-pink-900/15 p-3">
            <div class="font-semibold text-pink-800 dark:text-pink-200">Right: more run-time</div>
            <p class="mt-1">Runtime strategy stack + prediction. Symbolic explorer investigates all reachable states; memo prunes visited subtrees. Less compile investment → more flexible runtime.</p>
          </div>
        </div>
      </SectionCard>

      <SectionCard
        title="Per-pass detail"
        subtitle="Input, output, and the components that implement each pass. Click any component to open its detail panel."
      >
        <div class="space-y-3">
          <For each={PASSES}>
            {(p) => <PassCard pass={p} onSelect={setSelected} selectedId={selected()?.id} />}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="Grade-0 erasure"
        subtitle="The theorem that justifies treating certain facts as compile-time scaffolding without changing runtime semantics."
      >
        <div class="grid grid-cols-1 md:grid-cols-3 gap-3 text-sm">
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">The statement</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              In a graded linear logic, facts with grade 0 contribute to provability but not to computational
              behavior at runtime. They can be erased, yielding an equi-provable (but smaller) rule set.
            </p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Why it matters</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Our metadata and scaffolding facts (type judgments, calculus-config entries, witnesses about
              parse structure) can be used during compile passes and then completely erased — they are never
              looked up at runtime.
            </p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">References</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Atkey 2018 (Syntax and Semantics of Quantitative Type Theory);
              Choudhury, Eades, Krishnaswami, Weirich (POPL 2021);
              CALC's <code class="font-mono">doc/theory/0017</code> and <code class="font-mono">doc/documentation/sell-graded-modality.md</code>.
            </p>
          </div>
        </div>
      </SectionCard>

    </Page>
  );
}
