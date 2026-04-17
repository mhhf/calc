/**
 * Parser System deep dive.
 *
 * CALC uses ONE Earley core (lib/parser/earley.js) with THREE generated
 * grammars for three parsing paths:
 *
 *   1. Meta path   — .calc declarations, @extends chain resolution
 *   2. Program path — ILL formulas using user-defined types and connectives
 *   3. Rules path   — .rules files in sequent notation (antecedent ⊢ succedent)
 *
 * Each path shares the same recognizer and chart; they differ only in the
 * grammar fed in. Opt-in extensions ($ preserved sugar, precedence levels,
 * forward-rule syntax) are toggled by flags at grammar-gen time.
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
import { getComponent } from './data/components';
import type { Component } from './data/types';

interface Path {
  id: 'meta' | 'program' | 'rules';
  title: string;
  source: string;
  input: string;
  output: string;
  grammarSource: string;
  extensions: string[];
  components: string[];
  example: string;
}

const PATHS: Path[] = [
  {
    id: 'meta',
    title: 'Meta path',
    source: '.calc files',
    input: 'Calculus declarations (types, grammars, roles, @extends)',
    output: 'Declaration table + generated grammars',
    grammarSource: 'Static meta-grammar (fixed across all calculi)',
    extensions: ['@extends chain resolution'],
    components: ['parser.meta', 'parser.declarations'],
    example: '@extends ill.calc\n%type bits : type.\n%grammar bits ::= "0" | "1".\n%role store : resource.',
  },
  {
    id: 'program',
    title: 'Program path',
    source: '.ill files + formulas in code/UI',
    input: 'ILL formulas with user-defined types',
    output: 'Content-addressed AST (hashes)',
    grammarSource: 'Generated from .calc (connective table + user grammars)',
    extensions: ['Connective precedence', 'Binlit sugar', 'Arrlit sugar'],
    components: ['parser.earley', 'parser.earley-grammar'],
    example: '!plus(X, Y, Z) -o { lookup(X) * lookup(Y) * eq(Z, X + Y) }',
  },
  {
    id: 'rules',
    title: 'Rules path',
    source: '.rules files',
    input: 'Sequent notation (antecedent ⊢ succedent) + rule name',
    output: 'Rule descriptors (consumed / produced / premises)',
    grammarSource: 'Generated from .calc + sequent grammar + preserved ($) sugar',
    extensions: ['$preserved sugar', 'forward rule syntax'],
    components: ['parser.rules', 'parser.sequent'],
    example: 'evm/add:\n  $bytecode BC *\n  pc PC * stack (A :: B :: S)\n  -o { pc PC\' * stack ((A + B) :: S) }.',
  },
];

function PathsDiagram() {
  return (
    <svg viewBox="0 0 1100 260" class="w-full max-w-4xl mx-auto" role="img" aria-label="Parser paths diagram">
      <defs>
        <marker id="parser-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto-start-reverse">
          <path d="M 0 0 L 8 4 L 0 8 z" fill="currentColor" />
        </marker>
      </defs>
      {/* Three source boxes on the left */}
      <g>
        <rect x="30" y="20" width="200" height="50" rx="8" class="fill-teal-50 dark:fill-teal-900/20 stroke-teal-400" stroke-width="2" />
        <text x="130" y="43" text-anchor="middle" class="fill-teal-800 dark:fill-teal-200" font-weight="700" font-size="12">.calc files</text>
        <text x="130" y="60" text-anchor="middle" class="fill-gray-600 dark:fill-gray-400" font-size="10">meta path</text>

        <rect x="30" y="100" width="200" height="50" rx="8" class="fill-teal-50 dark:fill-teal-900/20 stroke-teal-400" stroke-width="2" />
        <text x="130" y="123" text-anchor="middle" class="fill-teal-800 dark:fill-teal-200" font-weight="700" font-size="12">.ill formulas</text>
        <text x="130" y="140" text-anchor="middle" class="fill-gray-600 dark:fill-gray-400" font-size="10">program path</text>

        <rect x="30" y="180" width="200" height="50" rx="8" class="fill-teal-50 dark:fill-teal-900/20 stroke-teal-400" stroke-width="2" />
        <text x="130" y="203" text-anchor="middle" class="fill-teal-800 dark:fill-teal-200" font-weight="700" font-size="12">.rules files</text>
        <text x="130" y="220" text-anchor="middle" class="fill-gray-600 dark:fill-gray-400" font-size="10">rules path</text>
      </g>
      {/* Grammar gen boxes */}
      <g>
        <rect x="310" y="20" width="200" height="50" rx="8" class="fill-white dark:fill-gray-800 stroke-gray-400" stroke-dasharray="3 3" stroke-width="1.5" />
        <text x="410" y="43" text-anchor="middle" class="fill-gray-800 dark:fill-gray-200" font-weight="600" font-size="11">meta grammar (static)</text>
        <text x="410" y="60" text-anchor="middle" class="fill-gray-500 dark:fill-gray-400" font-size="9">@extends / declarations</text>

        <rect x="310" y="100" width="200" height="50" rx="8" class="fill-white dark:fill-gray-800 stroke-gray-400" stroke-dasharray="3 3" stroke-width="1.5" />
        <text x="410" y="123" text-anchor="middle" class="fill-gray-800 dark:fill-gray-200" font-weight="600" font-size="11">program grammar</text>
        <text x="410" y="140" text-anchor="middle" class="fill-gray-500 dark:fill-gray-400" font-size="9">generated from .calc</text>

        <rect x="310" y="180" width="200" height="50" rx="8" class="fill-white dark:fill-gray-800 stroke-gray-400" stroke-dasharray="3 3" stroke-width="1.5" />
        <text x="410" y="203" text-anchor="middle" class="fill-gray-800 dark:fill-gray-200" font-weight="600" font-size="11">sequent grammar</text>
        <text x="410" y="220" text-anchor="middle" class="fill-gray-500 dark:fill-gray-400" font-size="9">sequent notation + $ sugar</text>
      </g>
      {/* Single Earley core */}
      <g>
        <rect x="590" y="90" width="220" height="70" rx="12" class="fill-teal-100 dark:fill-teal-900/40 stroke-teal-500" stroke-width="2.5" />
        <text x="700" y="118" text-anchor="middle" class="fill-teal-900 dark:fill-teal-100" font-weight="700" font-size="14">Earley core</text>
        <text x="700" y="136" text-anchor="middle" class="fill-gray-700 dark:fill-gray-300" font-size="10">recognizer · chart · extraction</text>
        <text x="700" y="152" text-anchor="middle" class="fill-gray-500 dark:fill-gray-400" font-size="9" font-family="ui-monospace">lib/parser/earley.js</text>
      </g>
      {/* Outputs */}
      <g>
        <rect x="870" y="20" width="200" height="50" rx="8" class="fill-indigo-50 dark:fill-indigo-900/20 stroke-indigo-400" stroke-width="2" />
        <text x="970" y="43" text-anchor="middle" class="fill-indigo-800 dark:fill-indigo-200" font-weight="700" font-size="12">declarations table</text>
        <text x="970" y="60" text-anchor="middle" class="fill-gray-600 dark:fill-gray-400" font-size="10">types · grammars · roles</text>

        <rect x="870" y="100" width="200" height="50" rx="8" class="fill-indigo-50 dark:fill-indigo-900/20 stroke-indigo-400" stroke-width="2" />
        <text x="970" y="123" text-anchor="middle" class="fill-indigo-800 dark:fill-indigo-200" font-weight="700" font-size="12">content-addressed AST</text>
        <text x="970" y="140" text-anchor="middle" class="fill-gray-600 dark:fill-gray-400" font-size="10">hashes into store</text>

        <rect x="870" y="180" width="200" height="50" rx="8" class="fill-indigo-50 dark:fill-indigo-900/20 stroke-indigo-400" stroke-width="2" />
        <text x="970" y="203" text-anchor="middle" class="fill-indigo-800 dark:fill-indigo-200" font-weight="700" font-size="12">rule descriptors</text>
        <text x="970" y="220" text-anchor="middle" class="fill-gray-600 dark:fill-gray-400" font-size="10">consumed / produced / deps</text>
      </g>
      {/* Arrows */}
      <g class="text-gray-500 dark:text-gray-400">
        <For each={[45, 125, 205]}>
          {(y) => (
            <>
              <path d={`M 230 ${y} L 310 ${y}`} fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#parser-arrow)" />
              <path d={`M 510 ${y} L 590 125`} fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#parser-arrow)" />
              <path d={`M 810 125 L 870 ${y}`} fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#parser-arrow)" />
            </>
          )}
        </For>
      </g>
    </svg>
  );
}

function PathCard(props: { path: Path; onSelect: (c: Component) => void; selectedId?: string }) {
  const comps = () => props.path.components.map(id => getComponent(id)).filter(Boolean) as Component[];
  return (
    <div class="rounded-lg border border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800/40 p-4">
      <div class="flex items-baseline justify-between gap-2 flex-wrap">
        <div class="flex items-center gap-2">
          <span class="font-mono text-xs bg-teal-100 dark:bg-teal-900/30 text-teal-800 dark:text-teal-200 px-1.5 py-0.5 rounded">
            {props.path.id}
          </span>
          <h4 class="font-bold text-gray-900 dark:text-white">{props.path.title}</h4>
        </div>
        <span class="text-[11px] text-gray-500 dark:text-gray-400 italic">{props.path.source}</span>
      </div>
      <div class="grid grid-cols-1 md:grid-cols-2 gap-2 mt-3 text-xs">
        <div class="rounded bg-gray-50 dark:bg-gray-900/30 border border-gray-200 dark:border-gray-700 p-2">
          <span class="uppercase text-[10px] tracking-wider text-gray-500 dark:text-gray-400">Input</span>
          <div class="text-gray-800 dark:text-gray-200 mt-0.5">{props.path.input}</div>
        </div>
        <div class="rounded bg-gray-50 dark:bg-gray-900/30 border border-gray-200 dark:border-gray-700 p-2">
          <span class="uppercase text-[10px] tracking-wider text-gray-500 dark:text-gray-400">Output</span>
          <div class="text-gray-800 dark:text-gray-200 mt-0.5">{props.path.output}</div>
        </div>
      </div>
      <div class="mt-3 text-xs">
        <span class="uppercase text-[10px] tracking-wider text-gray-500 dark:text-gray-400">Grammar</span>
        <span class="ml-2 text-gray-800 dark:text-gray-200">{props.path.grammarSource}</span>
      </div>
      <div class="mt-1 text-xs">
        <span class="uppercase text-[10px] tracking-wider text-gray-500 dark:text-gray-400">Extensions</span>
        <span class="ml-2">
          <For each={props.path.extensions}>
            {(e, i) => (
              <>
                <span class="inline-block rounded bg-teal-50 dark:bg-teal-900/20 text-teal-800 dark:text-teal-200 border border-teal-200 dark:border-teal-700 px-1.5 py-0.5 mr-1 text-[11px]">{e}</span>
                {i() < props.path.extensions.length - 1 && <span />}
              </>
            )}
          </For>
        </span>
      </div>
      <pre class="mt-3 text-[11px] bg-gray-900 dark:bg-black text-gray-100 p-3 rounded font-mono overflow-x-auto whitespace-pre leading-relaxed">{props.path.example}</pre>
      <div class="mt-3">
        <div class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-1.5">
          Components
        </div>
        <div class="grid grid-cols-1 sm:grid-cols-2 gap-2">
          <For each={comps()}>
            {(c) => <ComponentBox component={c} onSelect={props.onSelect} selected={props.selectedId === c.id} compact />}
          </For>
        </div>
      </div>
    </div>
  );
}

export default function Parser() {
  const meta = DEEP_DIVES.find(d => d.id === 'parser')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      subtitle="One Earley engine, three grammars. Share the recognizer — a bug in Earley is visible across every parsing path. Grammars are generated from .calc annotations; opt-in extensions are flags."
      accentClass={DEEPDIVE_ACCENT.parser}
    >
      <DetailPanel component={selected()} onClose={() => setSelected(null)} />

      <Intro>
        Every flavor of CALC input goes through the <strong>same Earley recognizer</strong>, only the grammar
        differs. Three paths: <em>meta</em> (parses the calculus description itself — <code>.calc</code>),
        <em> program</em> (parses user programs — <code>.ill</code>), and <em>rules</em> (parses inference rules in
        sequent notation). The payoff: a bug in Earley is visible across every parsing path, and grammar
        extensions enable features uniformly.
      </Intro>

      <SectionCard
        title="Three paths, one core"
        subtitle="Every flavor of CALC input is parsed by the same Earley recognizer against a different generated grammar."
      >
        <PathsDiagram />
      </SectionCard>

      <SectionCard
        title="Path detail"
        subtitle="Per-path input / output / grammar source / extensions / example syntax. Click components to open the detail panel."
      >
        <div class="grid grid-cols-1 lg:grid-cols-3 gap-3">
          <For each={PATHS}>
            {(p) => <PathCard path={p} onSelect={setSelected} selectedId={selected()?.id} />}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="Why one core?"
        subtitle="A shared recognizer means each path inherits soundness, ambiguity detection, and diagnostic quality from a single audited implementation."
      >
        <div class="grid grid-cols-1 md:grid-cols-3 gap-3 text-sm">
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Single source of ambiguity</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Earley handles arbitrary context-free grammars including ambiguous ones. Our grammar-gen
              layer picks parse trees deterministically via precedence annotations — all three paths
              inherit this consistency.
            </p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Opt-in extensions</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              The <code class="font-mono">$P</code> preserved-resource sugar is a rules-path extension.
              Other paths don't see it. Extensions are flags on grammar generation — never hacks in
              the recognizer.
            </p>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="font-semibold text-gray-900 dark:text-white">Bundled for the web</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Parser tables, connective precedences, and renderer formats are precomputed into
              <code class="font-mono">out/ill.json</code>. The browser never re-runs grammar generation.
            </p>
          </div>
        </div>
      </SectionCard>

    </Page>
  );
}
