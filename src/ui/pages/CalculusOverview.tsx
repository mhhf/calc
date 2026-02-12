import { createSignal, createMemo, For, Show } from 'solid-js';
import KaTeX from '../components/math/KaTeX';
import ErrorBoundary from '../components/common/ErrorBoundary';

// v2 API
import {
  getCalculusName,
  getFormulaConnectives,
  getRulesGrouped,
  getBNFGrammar,
  getPolarityInfo,
  type ConnectiveInfo,
  type RuleInfo,
  type BNFProduction
} from '../lib/calcV2';

/**
 * Simple BNF grammar display component
 */
function BNFGrammarView(props: { productions: BNFProduction[] }) {
  return (
    <div class="font-mono text-sm space-y-2">
      <For each={props.productions}>
        {(prod) => (
          <div class="flex gap-2">
            <span class="text-blue-600 dark:text-blue-400 font-semibold min-w-[80px]">
              {prod.lhs}
            </span>
            <span class="text-gray-500">::=</span>
            <span class="text-gray-700 dark:text-gray-300">
              {prod.alternatives.join(' | ')}
            </span>
          </div>
        )}
      </For>
    </div>
  );
}

/**
 * Rule card component
 */
function RuleCard(props: { rule: RuleInfo }) {
  const rule = () => props.rule;

  return (
    <div class="bg-gray-50 dark:bg-gray-700/50 rounded-lg p-4 border border-gray-200 dark:border-gray-600">
      <div class="flex items-center justify-between mb-2">
        <span class="font-mono font-bold text-gray-900 dark:text-white">
          {rule().pretty}
        </span>
        <div class="flex gap-1">
          <Show when={rule().invertible === true}>
            <span class="px-2 py-0.5 text-xs bg-green-100 dark:bg-green-900/30 text-green-700 dark:text-green-400 rounded">
              invertible
            </span>
          </Show>
          <Show when={rule().invertible === false}>
            <span class="px-2 py-0.5 text-xs bg-orange-100 dark:bg-orange-900/30 text-orange-700 dark:text-orange-400 rounded">
              synchronous
            </span>
          </Show>
          <Show when={rule().structural}>
            <span class="px-2 py-0.5 text-xs bg-purple-100 dark:bg-purple-900/30 text-purple-700 dark:text-purple-400 rounded">
              structural
            </span>
          </Show>
        </div>
      </div>
      <div class="text-sm text-gray-600 dark:text-gray-400">
        {rule().numPremises === 0 ? 'Axiom (no premises)' :
         rule().numPremises === 1 ? '1 premise' :
         `${rule().numPremises} premises`}
      </div>
    </div>
  );
}

export default function CalculusOverview() {
  const [showAscii, setShowAscii] = createSignal(false);

  // Get calculus data from v2 API
  const calcName = createMemo(() => getCalculusName());
  const connectives = createMemo(() => getFormulaConnectives());
  const ruleGroups = createMemo(() => getRulesGrouped());
  const bnfProductions = createMemo(() => getBNFGrammar());
  const polarityInfo = createMemo(() => getPolarityInfo());

  // Separate binary and unary connectives
  const binaryConnectives = createMemo(() =>
    connectives().filter(c => c.arity === 2)
  );
  const unaryConnectives = createMemo(() =>
    connectives().filter(c => c.arity === 1)
  );
  const nullaryConnectives = createMemo(() =>
    connectives().filter(c => c.arity === 0)
  );

  return (
    <ErrorBoundary>
      <div class="max-w-6xl mx-auto p-6 space-y-8 text-gray-900 dark:text-gray-100">
        {/* Header */}
        <div>
          <h2 class="text-2xl font-bold text-gray-900 dark:text-white mb-2">
            {calcName()} — Calculus Overview
          </h2>
          <p class="text-gray-600 dark:text-gray-400">
            Complete specification of the object logic: syntax, connectives, and inference rules.
          </p>
        </div>

        {/* Display options */}
        <div class="flex flex-wrap items-center gap-4 p-4 bg-gray-100 dark:bg-gray-800 rounded-lg">
          <label class="flex items-center gap-2 cursor-pointer">
            <input
              type="checkbox"
              checked={showAscii()}
              onChange={(e) => setShowAscii(e.currentTarget.checked)}
              class="w-4 h-4 text-blue-600 rounded focus:ring-blue-500"
            />
            <span class="text-sm text-gray-700 dark:text-gray-300">
              Show ASCII source
            </span>
          </label>
        </div>

        {/* Section 1: Syntax (BNF) */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              1. Syntax
            </h3>
            <p class="text-sm text-gray-500 dark:text-gray-400 mt-1">
              BNF grammar for formulas and sequents
            </p>
          </div>
          <div class="p-4 overflow-x-auto">
            <BNFGrammarView productions={bnfProductions()} />
          </div>
        </section>

        {/* Section 2: Connectives */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              2. Logical Connectives
            </h3>
            <p class="text-sm text-gray-500 dark:text-gray-400 mt-1">
              Binary and unary connectives with their polarity (for focused proof search)
            </p>
          </div>
          <div class="overflow-x-auto">
            <table class="w-full">
              <thead>
                <tr class="bg-gray-50 dark:bg-gray-700/30">
                  <th class="px-4 py-2 text-left text-sm font-medium text-gray-600 dark:text-gray-400">Name</th>
                  <th class="px-4 py-2 text-left text-sm font-medium text-gray-600 dark:text-gray-400">ASCII</th>
                  <th class="px-4 py-2 text-left text-sm font-medium text-gray-600 dark:text-gray-400">Symbol</th>
                  <th class="px-4 py-2 text-left text-sm font-medium text-gray-600 dark:text-gray-400">Category</th>
                  <th class="px-4 py-2 text-left text-sm font-medium text-gray-600 dark:text-gray-400">Polarity</th>
                </tr>
              </thead>
              <tbody class="divide-y divide-gray-200 dark:divide-gray-700">
                <For each={[...binaryConnectives(), ...unaryConnectives(), ...nullaryConnectives()]}>
                  {(conn) => (
                    <tr class="hover:bg-gray-50 dark:hover:bg-gray-700/30">
                      <td class="px-4 py-2 text-gray-900 dark:text-white font-medium">
                        {conn.name}
                      </td>
                      <td class="px-4 py-2 font-mono text-gray-700 dark:text-gray-300">
                        {conn.ascii}
                      </td>
                      <td class="px-4 py-2">
                        <Show when={conn.latex} fallback={<span class="text-gray-400">—</span>}>
                          <KaTeX latex={conn.latex.replace(/#\d/g, '\\square')} />
                        </Show>
                      </td>
                      <td class="px-4 py-2 text-sm text-gray-600 dark:text-gray-400">
                        {conn.category || '—'}
                      </td>
                      <td class="px-4 py-2">
                        <span
                          class="px-2 py-0.5 text-xs rounded"
                          classList={{
                            'bg-green-100 text-green-800 dark:bg-green-900/30 dark:text-green-400':
                              conn.polarity === 'positive',
                            'bg-red-100 text-red-800 dark:bg-red-900/30 dark:text-red-400':
                              conn.polarity === 'negative',
                            'bg-gray-100 text-gray-600 dark:bg-gray-700 dark:text-gray-400':
                              conn.polarity === 'unknown',
                          }}
                        >
                          {conn.polarity}
                        </span>
                      </td>
                    </tr>
                  )}
                </For>
              </tbody>
            </table>
          </div>

          {/* Polarity explanation */}
          <div class="p-4 bg-blue-50 dark:bg-blue-900/20 border-t border-gray-200 dark:border-gray-700">
            <p class="text-sm text-blue-800 dark:text-blue-300">
              <strong>Polarity</strong> determines the proof search phase:
              <span class="text-green-700 dark:text-green-400"> positive</span> connectives are decomposed eagerly (synchronous),
              <span class="text-red-700 dark:text-red-400"> negative</span> connectives are decomposed lazily (asynchronous/invertible).
            </p>
          </div>
        </section>

        {/* Section 3: Sequent Notation */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              3. Sequent Notation
            </h3>
          </div>
          <div class="p-4 prose dark:prose-invert max-w-none text-sm">
            <p>A <strong>sequent</strong> has the form:</p>
            <div class="text-center my-4">
              <KaTeX latex="\\Gamma ; \\Delta \\vdash A" display={true} />
            </div>
            <p>where:</p>
            <ul>
              <li><KaTeX latex="\\Gamma" /> — cartesian (persistent/unrestricted) context</li>
              <li><KaTeX latex="\\Delta" /> — linear context (resources available exactly once)</li>
              <li><KaTeX latex="A" /> — succedent (goal formula)</li>
              <li><KaTeX latex="\\vdash" /> (turnstile) — entailment relation</li>
            </ul>
            <p class="mt-4">
              <strong>Linear logic</strong> is resource-sensitive: each linear hypothesis must be used exactly once.
              The <KaTeX latex="!" /> (bang) modality allows formulas to be used multiple times.
            </p>
          </div>
        </section>

        {/* Section 4: Inference Rules */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              4. Inference Rules
            </h3>
            <p class="text-sm text-gray-500 dark:text-gray-400 mt-1">
              Rules are organized by connective category
            </p>
          </div>
          <div class="p-4 space-y-8">
            <For each={Object.entries(ruleGroups())}>
              {([groupName, rules]) => (
                <div>
                  <h4 class="text-lg font-semibold text-gray-800 dark:text-gray-200 mb-4 pb-2 border-b border-gray-200 dark:border-gray-700">
                    {groupName}
                    <span class="ml-2 text-sm font-normal text-gray-500">
                      ({rules.length} rule{rules.length !== 1 ? 's' : ''})
                    </span>
                  </h4>
                  <div class="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
                    <For each={rules}>
                      {(rule) => <RuleCard rule={rule} />}
                    </For>
                  </div>
                </div>
              )}
            </For>
          </div>
        </section>

        {/* Section 5: Focusing */}
        <Show when={polarityInfo().length > 0}>
          <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
            <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
              <h3 class="font-semibold text-gray-900 dark:text-white">
                5. Focused Proof Search
              </h3>
            </div>
            <div class="p-4 prose dark:prose-invert max-w-none text-sm">
              <p>
                This calculus uses <strong>focused proof search</strong> (Andreoli 1992), which organizes
                proof construction into alternating phases based on connective polarity:
              </p>
              <ul>
                <li>
                  <strong class="text-green-700 dark:text-green-400">Positive phase</strong> (synchronous):
                  Decompose all positive connectives eagerly until reaching a negative formula or atom.
                </li>
                <li>
                  <strong class="text-red-700 dark:text-red-400">Negative phase</strong> (asynchronous):
                  Decompose negative connectives — these rules are invertible and can be applied in any order.
                </li>
              </ul>
              <div class="overflow-x-auto mt-4">
                <table class="text-sm">
                  <thead>
                    <tr>
                      <th class="px-3 py-2 text-left">Connective</th>
                      <th class="px-3 py-2 text-left">Polarity</th>
                      <th class="px-3 py-2 text-left">Phase</th>
                    </tr>
                  </thead>
                  <tbody>
                    <For each={polarityInfo()}>
                      {(info) => (
                        <tr>
                          <td class="px-3 py-2 font-mono">{info.name}</td>
                          <td class="px-3 py-2">
                            <span
                              class="px-2 py-0.5 text-xs rounded"
                              classList={{
                                'bg-green-100 text-green-800': info.polarity === 'positive',
                                'bg-red-100 text-red-800': info.polarity === 'negative',
                              }}
                            >
                              {info.polarity}
                            </span>
                          </td>
                          <td class="px-3 py-2">
                            {info.polarity === 'positive' ? 'Synchronous (eager)' : 'Asynchronous (lazy)'}
                          </td>
                        </tr>
                      )}
                    </For>
                  </tbody>
                </table>
              </div>
            </div>
          </section>
        </Show>
      </div>
    </ErrorBoundary>
  );
}
