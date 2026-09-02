/**
 * Optimization deep dive.
 *
 * Optimization is not a stack layer. Each profile flag in optimizer.js
 * toggles a wrapper that replaces a lower-layer function with an
 * instrumented version — the wrapper must have identical observable
 * behavior modulo performance. Turning everything off ("bare" profile)
 * must still work.
 *
 * This page shows:
 *   - the six opt/ modules (component catalog)
 *   - the full profile-flag matrix (10 flags × 3 profiles)
 *   - how a profile is selected (argument vs CALC_PROFILE vs default)
 *   - the injection pattern (schematic SVG: original fn wrapped by opt → same signature)
 *   - the differential testing story (how we trust that wraps preserve semantics)
 *   - the cache layers (2 runtime + 1 disk) and their activation flags
 *
 * Source of truth for the matrix: lib/engine/optimizer.js (PROFILES).
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

/**
 * Profile-flag row. Mirrors PROFILES in lib/engine/optimizer.js.
 * A "flag" is the boolean key in the PROFILES object; a "module" is the
 * file(s) that implement the wrapper gated by the flag.
 */
interface FlagRow {
  /** Key in PROFILES — matches optimizer.js exactly. */
  flag: string;
  /** File(s) that implement the wrapper. */
  modules: string;
  /** Which lower-layer function is wrapped. */
  wraps: string;
  /** How the optimization speeds things up. */
  mechanism: string;
  /** Enabled under these profiles — must match optimizer.js. */
  enabled: Record<Profile, boolean>;
  /** Differential test story. */
  diff: string;
}

const FLAGS: FlagRow[] = [
  {
    flag: 'ffi',
    modules: 'opt/ffi.js + opt/compiled-clauses.js + opt/existential-compile.js',
    wraps: 'backchain.prove() (persistent)',
    mechanism: 'Persistent-goal fast path: state → FFI → compiled clause → full clause resolution. FFI failure is advisory (falls through). Also gates compiled ∃-chain and zero-subgoal clause dispatch.',
    enabled: { bare: false, fast: true, evm: true },
    diff: 'noFFI adversarial suite (npm run test:noffi) runs with FFI off; output must match FFI-on exactly. Fuzzer: tools/fuzz-ffi.js.',
  },
  {
    flag: 'compiledSub',
    modules: 'rule-analysis.js',
    wraps: 'applyIndexed (consequent instantiation)',
    mechanism: 'Precompiled Store.put recipes — bypasses recursive applyIndexed walk of the consequent.',
    enabled: { bare: false, fast: true, evm: true },
    diff: 'Resulting fact hashes identical to unoptimised path.',
  },
  {
    flag: 'preserved',
    modules: 'preserved.js',
    wraps: 'consume/produce',
    mechanism: 'Skip consume-then-re-produce for facts that appear unchanged in consequent ($P sugar).',
    enabled: { bare: false, fast: true, evm: true },
    diff: 'Final state identical; Arena trace differs but observables do not.',
  },
  {
    flag: 'fingerprint',
    modules: 'opt/fingerprint.js',
    wraps: 'strategy.candidates()',
    mechanism: 'O(1) first-arg hash bucket; auto-detects discriminating predicates from rule structure.',
    enabled: { bare: false, fast: false, evm: true },
    diff: 'candidates(fingerprint) ⊆ candidates(predicate-filter) AND set equality after full match.',
  },
  {
    flag: 'prediction',
    modules: 'opt/prediction.js',
    wraps: 'strategy.candidates()',
    mechanism: 'Threaded-code dispatch — predicts next applicable rule from last substitution; skips findAllMatches when hit.',
    enabled: { bare: false, fast: false, evm: true },
    diff: 'Any predicted-false rule must also fail on full match; else regression.',
  },
  {
    flag: 'discTree',
    modules: 'disc-tree.js',
    wraps: 'strategy.candidates()',
    mechanism: 'Shape-indexed trie — finer than fingerprint. Handles variable-position arguments.',
    enabled: { bare: false, fast: false, evm: true },
    diff: 'Disc-tree result ⊆ predicate-filter result after unification.',
  },
  {
    flag: 'deltaBypass',
    modules: 'delta-bypass.js',
    wraps: 'matchIndexed decomposition',
    mechanism: 'Direct Store.child() extraction for flat delta patterns; skips full recursive match.',
    enabled: { bare: false, fast: false, evm: true },
    diff: 'Bindings identical to full decomposition on shape-compatible inputs.',
  },
  {
    flag: 'loliDrain',
    modules: 'lnl/loli-drain.js',
    wraps: 'DFS continuation',
    mechanism: 'Eagerly fires persistent-trigger lolis before branching — safe because they consume only themselves.',
    enabled: { bare: false, fast: false, evm: true },
    diff: 'Same leaf set as lazy firing (reorder-independence proof).',
  },
  {
    flag: 'structuralMemo',
    modules: 'opt/structural-memo.js',
    wraps: 'explore() descent',
    mechanism: 'hash(PC, SH) control hash → subtree skip; avoids exploring isomorphic states twice.',
    enabled: { bare: false, fast: false, evm: true },
    diff: 'With memo off, explore visits all same leaves (possibly more duplicate copies).',
  },
  {
    flag: 'solver',
    modules: 'constraint.js + constraint-feed.js',
    wraps: 'DFS branch enumeration',
    mechanism: 'EqNeq union-find SAT-filters oplus alternatives; feeds persistent facts via constraint-feed; prunes UNSAT branches.',
    enabled: { bare: false, fast: false, evm: true },
    diff: 'Pruned branches must be unreachable under the computed eq/neq constraints.',
  },
];

const PROFILE_DESC: Record<Profile, string> = {
  bare: 'All 10 flags off. Pure reference semantics — slow but maximally auditable. The correctness baseline for differential testing.',
  fast: 'ffi + compiledSub + preserved (3 flags). Common-path, low-risk optimizations. Baseline for non-heavy workloads.',
  evm:  'All 10 flags on. The default when CALC_PROFILE is unset. Required for EVM symbolic execution performance.',
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

/**
 * Disk-cache mode row. Mirrors the `cache:` option handled in lib/engine/index.js (load).
 */
interface CacheModeRow {
  mode: string;          // cache: option literal
  env: string;           // equivalent env var(s)
  location: string;      // where the cache lives
  behaviour: string;
  whenToUse: string;
}

const CACHE_MODES: CacheModeRow[] = [
  {
    mode: 'true (default)',
    env: 'CALC_CACHE unset, or =1',
    location: 'os.tmpdir()/calc-cache/',
    behaviour: 'Two-tier snapshot cache: one file for the SDK (imports-only), one for the full program. Keyed on content hash of source tree + CACHE_VERSION.',
    whenToUse: 'Everyday runs. Hits the full-program snapshot on unchanged files.',
  },
  {
    mode: "'imports'",
    env: '—',
    location: 'os.tmpdir()/calc-cache/',
    behaviour: 'Caches the SDK (transitive imports) only. The program itself is re-composed every run.',
    whenToUse: 'When program source changes faster than its SDK.',
  },
  {
    mode: "'compose'",
    env: 'CALC_COMPOSE_CACHE=1',
    location: 'CALC_CACHE_DIR or ~/.cache/calc/snapshots/',
    behaviour: 'Caches post-compose rule pools (fused / specialized / tabled). Keyed on content hash + bytecode + cacheFlagFingerprint.',
    whenToUse: 'Iteration on heavy symex programs (multisig, EVM). ~10× cold-load speedup.',
  },
  {
    mode: "'verify'",
    env: 'CALC_CACHE_VERIFY=1',
    location: 'same as compose',
    behaviour: 'Audit mode: runs cold, writes snapshot, replays from snapshot, diffs rule names. Throws on divergence.',
    whenToUse: 'Before trusting a compose-cache change; CI gate.',
  },
  {
    mode: 'false',
    env: 'CALC_CACHE=0',
    location: '—',
    behaviour: 'No disk caching at all. cache: false and CALC_CACHE=0 each override every other opt-in.',
    whenToUse: 'Reproducing a clean build; debugging cache-key drift.',
  },
];

interface RuntimeCacheRow {
  name: string;
  file: string;
  key: string;
  cleared: string;
  soundness: string;
}

const RUNTIME_CACHES: RuntimeCacheRow[] = [
  {
    name: 'Backward proof cache',
    file: 'lib/engine/backward-cache.js',
    key: '(pred, +input-args)  — FFI-mode positions',
    cleared: 'lnlClearCache() at the start of every forward.run() / explore.explore() call',
    soundness: 'Clause DB is immutable within a run; FFI is pure. Cached successes valid on every DFS path; cached failures conservative. Arena undo retracts facts on backtrack, but state lookup is always redone fresh — only backchain outputs are cached.',
  },
  {
    name: 'Tabling cache',
    file: 'family/lnl/lib/persistent.js',
    key: 'goal hash',
    cleared: 'same lnlClearCache() call',
    soundness: 'Same invariant as backward cache — clause DB path-independence within a run.',
  },
];

export default function Optimization() {
  const meta = DEEP_DIVES.find(d => d.id === 'optimization')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);
  const optComponents = componentsByCluster('engine.opt');

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      subtitle="Ten profile flags that wrap lower-layer functions. Not a stack layer — cross-cutting instrumentation. Turning a flag off preserves soundness; only performance changes."
      accentClass={DEEPDIVE_ACCENT.optimization}
    >
      <DetailPanel component={selected()} onClose={() => setSelected(null)} />

      <Intro>
        The <strong>optimization surface</strong> is the only genuinely cross-cutting layer in CALC. Each flag
        in <code>PROFILES</code> (<code>lib/engine/optimizer.js</code>) toggles a wrapper that replaces a
        lower-layer function with an instrumented version. The composition root decides which wrappers to
        apply. Profiles (<em>bare</em>, <em>fast</em>, <em>evm</em>) are presets — disabling everything keeps
        the engine sound, it just gets slower.
      </Intro>

      <SectionCard
        title="Opt-module catalog (engine/opt/)"
        subtitle="Six of the ten flags have a dedicated module under engine/opt/. The other four flags live at other layers (disc-tree.js, delta-bypass.js, preserved.js, lnl/loli-drain.js, constraint.js + constraint-feed.js). The full flag matrix is below."
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
        title="Profile-flag matrix (10 flags × 3 profiles)"
        subtitle="Exact mirror of PROFILES in lib/engine/optimizer.js. A profile is a Set of flags to enable. Differential tests run all profiles and compare outputs byte-for-byte."
      >
        <div class="overflow-x-auto">
          <table class="w-full text-xs border-collapse">
            <thead>
              <tr class="text-left">
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Flag</th>
                <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Module(s)</th>
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
              <For each={FLAGS}>
                {(f) => (
                  <tr class="border-t border-gray-200 dark:border-gray-700 align-top">
                    <td class="py-2 pr-3 font-mono text-gray-800 dark:text-gray-200 font-semibold">{f.flag}</td>
                    <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 font-mono text-[10px] leading-snug max-w-[12rem]">{f.modules}</td>
                    <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 font-mono text-[11px]">{f.wraps}</td>
                    <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-sm">{f.mechanism}</td>
                    <For each={PROFILES}>
                      {(p) => (
                        <td class="py-2 px-2 text-center">
                          <span class={`inline-block w-4 h-4 rounded-full ${f.enabled[p] ? 'bg-orange-500 dark:bg-orange-400' : 'border border-gray-300 dark:border-gray-600'}`}
                                title={`${p}: ${f.enabled[p] ? 'on' : 'off'}`} />
                        </td>
                      )}
                    </For>
                    <td class="py-2 pl-3 text-gray-700 dark:text-gray-300 leading-snug max-w-sm">{f.diff}</td>
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
        title="Selecting a profile"
        subtitle="Priority order: CALC_PROFILE env var > explicit argument > default (evm). Unknown names throw immediately."
      >
        <div class="grid grid-cols-1 md:grid-cols-2 gap-3 text-xs">
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-1">Programmatic</div>
            <pre class="font-mono text-[11px] text-gray-800 dark:text-gray-200 whitespace-pre-wrap leading-snug">{`import { profile, engine } from 'calc/engine/optimizer';

// By name
const p = profile('fast');

// As object (custom mix — name defaults to 'custom')
const p2 = profile({ ffi: true, solver: true });

// Default when undefined → 'evm'
const p3 = profile();`}</pre>
          </div>
          <div class="rounded border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/30 p-3">
            <div class="text-[10px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-1">Environment</div>
            <pre class="font-mono text-[11px] text-gray-800 dark:text-gray-200 whitespace-pre-wrap leading-snug">{`CALC_PROFILE=bare npm test          # all flags off
CALC_PROFILE=fast npm test          # 3-flag common path
CALC_PROFILE=evm  npm test          # all 10 flags (= default)

CALC_PERF_PROFILE=1 bun bench.js    # separate flag:
                                    # enable runtime perf counters
                                    # (hot-path profiling, not profile selection)`}</pre>
          </div>
        </div>
        <p class="text-xs text-gray-600 dark:text-gray-400 mt-3 leading-snug">
          <code class="font-mono">CALC_PROFILE</code> always wins, even against an explicit argument — useful
          for running the whole test matrix under one profile without touching call sites. Note the unrelated
          <code class="font-mono"> CALC_PERF_PROFILE</code>: that enables cache/profile counters in
          <code class="font-mono"> match.js</code> and <code class="font-mono">backward-cache.js</code>, it does
          not change which optimizations are active.
        </p>
      </SectionCard>

      <SectionCard
        title="Cache layers"
        subtitle="Two runtime caches (in-memory, always on, cleared per run) and five disk-cache modes (persistent, controlled by the cache: option or env var)."
      >
        <div class="space-y-5">
          {/* Runtime */}
          <div>
            <h4 class="font-semibold text-gray-900 dark:text-white text-sm mb-2">Runtime caches (in-memory)</h4>
            <p class="text-xs text-gray-600 dark:text-gray-400 mb-2 leading-snug">
              Always enabled. Both caches are cleared together at the start of every
              <code class="font-mono"> forward.run()</code> / <code class="font-mono">explore.explore()</code>
              call — that's the soundness primitive. They are not profile-gated: even <em>bare</em> keeps them.
            </p>
            <div class="overflow-x-auto">
              <table class="w-full text-xs border-collapse">
                <thead>
                  <tr class="text-left">
                    <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Cache</th>
                    <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">File</th>
                    <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Key</th>
                    <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Cleared</th>
                    <th class="pb-2 pl-3 font-semibold text-gray-600 dark:text-gray-400">Soundness argument</th>
                  </tr>
                </thead>
                <tbody>
                  <For each={RUNTIME_CACHES}>
                    {(c) => (
                      <tr class="border-t border-gray-200 dark:border-gray-700 align-top">
                        <td class="py-2 pr-3 font-semibold text-gray-800 dark:text-gray-200">{c.name}</td>
                        <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 font-mono text-[10px]">{c.file}</td>
                        <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 font-mono text-[10px]">{c.key}</td>
                        <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-xs">{c.cleared}</td>
                        <td class="py-2 pl-3 text-gray-700 dark:text-gray-300 leading-snug max-w-md">{c.soundness}</td>
                      </tr>
                    )}
                  </For>
                </tbody>
              </table>
            </div>
          </div>

          {/* Disk */}
          <div>
            <h4 class="font-semibold text-gray-900 dark:text-white text-sm mb-2">Disk caches (load-time, user-configurable)</h4>
            <p class="text-xs text-gray-600 dark:text-gray-400 mb-2 leading-snug">
              Selected via the <code class="font-mono">cache:</code> option on <code class="font-mono">mde.load()</code>,
              with env-var equivalents. <code class="font-mono">cache: false</code> and
              <code class="font-mono"> CALC_CACHE=0</code> are hard opt-outs — they override every other opt-in.
              The compose cache's key registry lives at <code class="font-mono">lib/engine/cache-flags.js</code>:
              any env var or option that changes compose output must be listed there, or stale hits become a
              soundness bug.
            </p>
            <div class="overflow-x-auto">
              <table class="w-full text-xs border-collapse">
                <thead>
                  <tr class="text-left">
                    <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">cache: option</th>
                    <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Env equivalent</th>
                    <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Location</th>
                    <th class="pb-2 pr-3 font-semibold text-gray-600 dark:text-gray-400">Behaviour</th>
                    <th class="pb-2 pl-3 font-semibold text-gray-600 dark:text-gray-400">When to use</th>
                  </tr>
                </thead>
                <tbody>
                  <For each={CACHE_MODES}>
                    {(m) => (
                      <tr class="border-t border-gray-200 dark:border-gray-700 align-top">
                        <td class="py-2 pr-3 font-mono text-[11px] text-gray-800 dark:text-gray-200">{m.mode}</td>
                        <td class="py-2 pr-3 font-mono text-[10px] text-gray-700 dark:text-gray-300">{m.env}</td>
                        <td class="py-2 pr-3 font-mono text-[10px] text-gray-700 dark:text-gray-300">{m.location}</td>
                        <td class="py-2 pr-3 text-gray-700 dark:text-gray-300 leading-snug max-w-md">{m.behaviour}</td>
                        <td class="py-2 pl-3 text-gray-700 dark:text-gray-300 leading-snug max-w-sm">{m.whenToUse}</td>
                      </tr>
                    )}
                  </For>
                </tbody>
              </table>
            </div>
          </div>

          <div class="rounded border border-amber-200 dark:border-amber-700 bg-amber-50 dark:bg-amber-900/15 p-3 text-xs text-gray-700 dark:text-gray-300 leading-snug">
            <strong class="text-amber-800 dark:text-amber-200">Quick reference:</strong>{' '}
            <code class="font-mono">cache: false</code> or <code class="font-mono">CALC_CACHE=0</code> → no
            caching anywhere;{' '}
            <code class="font-mono">cache: 'compose'</code> or <code class="font-mono">CALC_COMPOSE_CACHE=1</code> →
            turn on the heavy iteration-loop cache;{' '}
            <code class="font-mono">cache: 'verify'</code> or <code class="font-mono">CALC_CACHE_VERIFY=1</code> →
            audit (cold + cached + diff).
          </div>
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
