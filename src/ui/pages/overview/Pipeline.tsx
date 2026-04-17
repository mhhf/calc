/**
 * Pipeline view — when does each component run?
 *
 * Horizontal swim-lane: six stages (define → parse → compile → execute →
 * certify → present). Each component is projected into every stage it
 * participates in, so a component that spans multiple stages appears multiple
 * times — truthful, because "when does this run" is a multi-valued question.
 *
 * Below the lanes: a stage-transition legend (what happens BETWEEN stages)
 * and an execution-mode decomposition (concrete forward, explore, backward,
 * certification) showing which stages each mode traverses.
 */

import { For, Show } from 'solid-js';
import { useHashComponent } from './blocks/useHashComponent';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import DetailPanel from './blocks/DetailPanel';
import Intro from './blocks/Intro';
import ComponentBox from './blocks/ComponentBox';
import { StageBadge, ModeBadge } from './blocks/Badge';
import { COMPONENTS } from './data/components';
import { VIEWS } from './data/meta';
import { STAGE_COLORS } from './data/palette';
import type { Component, Stage, Mode } from './data/types';

const STAGE_ORDER: Stage[] = ['define', 'parse', 'compile', 'execute', 'certify', 'present'];

const STAGE_SUMMARY: Record<Stage, string> = {
  define:  '.calc + .rules source — connective tables, inference rules, prelude',
  parse:   'Text → AST. One Earley core, three grammars (meta / rules / program).',
  compile: 'AST → IR. Rule compilation, clause compilation, bytecode normalize.',
  execute: 'Run it. Backward focusing, committed-choice forward, exhaustive DFS.',
  certify: 'Proof term → Plonky3 witness. 14 buses + chips.',
  present: 'Web UI, docs, debug display — the outermost, testable-only layer.',
};

/** Transitions — short description of what happens between adjacent stages. */
const TRANSITIONS: { from: Stage; to: Stage; label: string; detail: string }[] = [
  { from: 'define',  to: 'parse',   label: 'tokenize',   detail: 'Source file → token stream. @extends chain resolved.' },
  { from: 'parse',   to: 'compile', label: 'compile',    detail: 'AST → rule descriptors → compiled clauses + FFI dispatch table.' },
  { from: 'compile', to: 'execute', label: 'assemble',   detail: 'Compiled rules wired through matchOpts; initial state content-addressed.' },
  { from: 'execute', to: 'certify', label: 'transcribe', detail: 'Proof term → bus assignment → chip traces → Plonky3 witness.' },
  { from: 'certify', to: 'present', label: 'display',    detail: 'Witness / proof / execution trace rendered in the web UI or docs.' },
];

interface ModeInfo { stages: Stage[]; blurb: string }
const MODE_STAGES: Record<Mode, ModeInfo> = {
  backward:       { stages: ['define', 'parse', 'compile', 'execute', 'present'],           blurb: 'Andreoli focusing: L4→L3→L2→L1 over compiled rule descriptors.' },
  forward:        { stages: ['define', 'parse', 'compile', 'execute', 'present'],           blurb: 'Committed-choice multiset rewriting. exec() returns a single terminal state.' },
  symbolic:       { stages: ['define', 'parse', 'compile', 'execute', 'present'],           blurb: 'Exhaustive DFS with undo-log; explore() returns all reachable leaves.' },
  certification:  { stages: ['execute', 'certify', 'present'],                              blurb: 'Takes a proof term (produced by any mode above) and compiles it to Plonky3.' },
};
const MODE_ROWS: { mode: Mode; info: ModeInfo }[] =
  (['backward', 'forward', 'symbolic', 'certification'] as Mode[]).map(m => ({ mode: m, info: MODE_STAGES[m] }));

interface StageLaneProps {
  stage: Stage;
  components: Component[];
  onSelect: (c: Component) => void;
  selectedId?: string;
}

function StageLane(props: StageLaneProps) {
  const p = () => STAGE_COLORS[props.stage];
  return (
    <div class={`rounded-lg border ${p().border} ${p().bg} flex flex-col min-h-[18rem]`}>
      <header class={`px-3 py-2 border-b ${p().border} flex items-center gap-2`}>
        <StageBadge stage={props.stage} />
        <span class={`text-[11px] text-gray-600 dark:text-gray-400`}>
          {props.components.length} component{props.components.length === 1 ? '' : 's'}
        </span>
      </header>
      <p class="text-[11px] text-gray-700 dark:text-gray-300 px-3 pt-2 leading-snug">
        {STAGE_SUMMARY[props.stage]}
      </p>
      <div class="p-2 flex-1 flex flex-col gap-1.5">
        <For each={props.components}>
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
  );
}

/** Between-stage arrow bar showing transitions on a horizontal strip. */
function TransitionBar() {
  return (
    <svg viewBox="0 0 1200 90" class="w-full max-w-5xl mx-auto" role="img" aria-label="Stage transitions">
      <defs>
        <marker id="pipe-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto-start-reverse">
          <path d="M 0 0 L 8 4 L 0 8 z" fill="currentColor" />
        </marker>
      </defs>
      {/* 6 stages with 5 transitions — evenly spread */}
      <g class="text-gray-500 dark:text-gray-400">
        <For each={TRANSITIONS}>
          {(t, i) => {
            const step = 1200 / 6;
            const x0 = step * (i() + 0.5);
            const x1 = step * (i() + 1.5);
            return (
              <>
                <circle cx={x0} cy={45} r="7" class="fill-current" />
                <path d={`M ${x0 + 8} 45 L ${x1 - 8} 45`} fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#pipe-arrow)" />
                <text x={(x0 + x1) / 2} y={36} text-anchor="middle" font-size="10" class="fill-current">
                  {t.label}
                </text>
              </>
            );
          }}
        </For>
        {/* trailing terminal circle for the last stage */}
        <circle cx={1200 / 6 * 5.5} cy={45} r="7" class="fill-current" />
      </g>
      {/* stage name labels underneath */}
      <g class="text-gray-700 dark:text-gray-300">
        <For each={STAGE_ORDER}>
          {(s, i) => (
            <text x={1200 / 6 * (i() + 0.5)} y={75} text-anchor="middle" font-size="11" font-weight="600" class="fill-current">
              {STAGE_COLORS[s].label}
            </text>
          )}
        </For>
      </g>
    </svg>
  );
}

export default function Pipeline() {
  const meta = VIEWS.find(v => v.id === 'pipeline')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);

  const byStage = (s: Stage) => COMPONENTS.filter(c => c.stages.includes(s));

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      question={meta.question}
      subtitle={meta.blurb}
      rightSlot={
        <div class="flex items-center gap-1 text-xs overflow-x-auto">
          <span class="uppercase tracking-wider font-semibold text-gray-500 dark:text-gray-400 text-[10px] whitespace-nowrap">Stage →</span>
          <For each={STAGE_ORDER}>{(s) => <StageBadge stage={s} />}</For>
        </div>
      }
    >
      <DetailPanel component={selected()} onClose={() => setSelected(null)} />

      <Intro>
        The <strong>pipeline</strong> axis asks <em>when</em> each piece of code runs.
        Early stages (define → parse → compile) happen once per program load;
        later stages (execute → certify → present) run per query.
        Each swim-lane below lists every component that participates in that stage —
        a single component can show up in several stages, and that's the truth, not a duplication.
      </Intro>

      <SectionCard
        title="Stage lanes"
        subtitle="Every component appears in every stage it touches. A single component may participate in multiple stages — that's truthful, not a duplication. Click to open the detail panel."
      >
        <div class="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 xl:grid-cols-6 gap-2">
          <For each={STAGE_ORDER}>
            {(s) => (
              <StageLane
                stage={s}
                components={byStage(s)}
                onSelect={setSelected}
                selectedId={selected()?.id}
              />
            )}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="Between the stages"
        subtitle="What happens in the transition from one stage to the next."
      >
        <TransitionBar />
        <div class="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-5 gap-2 mt-3">
          <For each={TRANSITIONS}>
            {(t) => (
              <div class="rounded border border-gray-200 dark:border-gray-700 p-2 text-xs">
                <div class="flex items-center gap-1 mb-1">
                  <StageBadge stage={t.from} />
                  <span class="text-gray-400">→</span>
                  <StageBadge stage={t.to} />
                </div>
                <div class="font-semibold text-gray-800 dark:text-gray-200">{t.label}</div>
                <p class="text-gray-600 dark:text-gray-400 mt-0.5 leading-snug">{t.detail}</p>
              </div>
            )}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="Mode × stage matrix"
        subtitle="Each execution mode consumes a subset of the pipeline stages. Certification is downstream — it consumes the proof term produced by any of the proof modes."
      >
        <div class="overflow-x-auto">
          <table class="w-full text-xs border-collapse">
            <thead>
              <tr>
                <th class="text-left pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400 whitespace-nowrap">Mode</th>
                <For each={STAGE_ORDER}>
                  {(s) => (
                    <th class="pb-2 px-1 text-center font-semibold text-gray-600 dark:text-gray-400">
                      <StageBadge stage={s} />
                    </th>
                  )}
                </For>
                <th class="text-left pb-2 pl-3 font-semibold text-gray-600 dark:text-gray-400">Notes</th>
              </tr>
            </thead>
            <tbody>
              <For each={MODE_ROWS}>
                {(row) => (
                  <tr class="border-t border-gray-200 dark:border-gray-700">
                    <td class="py-2 pr-3"><ModeBadge mode={row.mode} /></td>
                    <For each={STAGE_ORDER}>
                      {(s) => (
                        <td class="py-2 px-1 text-center">
                          <Show when={row.info.stages.includes(s)} fallback={<span class="text-gray-300 dark:text-gray-700">·</span>}>
                            <span class={`inline-block w-3 h-3 rounded-full ${STAGE_COLORS[s].border} border-2`} />
                          </Show>
                        </td>
                      )}
                    </For>
                    <td class="py-2 pl-3 text-gray-700 dark:text-gray-300 leading-snug max-w-md">{row.info.blurb}</td>
                  </tr>
                )}
              </For>
            </tbody>
          </table>
        </div>
      </SectionCard>

      <SectionCard
        title="Why this matters"
        subtitle="The stage axis is orthogonal to the trust axis. A kernel component (trust=kernel) runs at the execute stage; a UI component runs at the present stage; a compile-stage component runs once and caches."
      >
        <div class="grid grid-cols-1 md:grid-cols-3 gap-3 text-sm">
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Compile-time vs run-time</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Compile-stage cost is paid once per calculus load and cached in <code class="font-mono">out/ill.json</code>.
              Execute-stage cost is paid per proof / per step. Optimizations typically move work left
              (from execute → compile).
            </p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Compile ≠ compilation deep dive</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              The <em>Compilation</em> deep dive covers the full pipeline. The <em>compile</em> stage here is just
              the moment at which AST → IR happens.
            </p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Certify is a late stage</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Witness generation runs AFTER execute. A proof term is the input; a Plonky3 STARK is the
              output. ZK circuits never re-implement the prover — they only re-verify.
            </p>
          </div>
        </div>
      </SectionCard>

    </Page>
  );
}
