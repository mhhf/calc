import { createSignal, createMemo, For, Show } from 'solid-js';
import KaTeX from '../components/math/KaTeX';
import SequentRule from '../components/math/SequentRule';
import BNFGrammar, { extractBNFFromCalc } from '../components/math/BNFGrammar';
import ErrorBoundary from '../components/common/ErrorBoundary';

// @ts-ignore - CommonJS module
import * as CalcModule from '../../../lib/calc.js';

const Calc = (CalcModule as any).default || CalcModule;

export default function CalculusOverview() {
  const [simplified, setSimplified] = createSignal(true);
  const [showAscii, setShowAscii] = createSignal(false);
  const [activeSection, setActiveSection] = createSignal<string | null>(null);

  // Get calculus data
  const calcData = createMemo(() => Calc.calc || {});
  const calcName = createMemo(() => calcData().calc_name || 'Calculus');

  // Extract BNF grammar
  const bnfProductions = createMemo(() => {
    const structure = calcData().calc_structure;
    if (!structure) return [];
    return extractBNFFromCalc(structure);
  });

  // Extract connectives from Formula_Bin_Op
  const connectives = createMemo(() => {
    const structure = calcData().calc_structure;
    const meta = calcData().calc_structure_rules_meta;
    if (!structure?.Formula_Bin_Op) return [];

    const polarities = meta?.polarity || {};

    return Object.entries(structure.Formula_Bin_Op).map(([name, data]: [string, any]) => ({
      name: name.replace('Formula_', ''),
      fullName: name,
      ascii: data.ascii || '',
      latex: data.latex || '',
      polarity: polarities[name] || 'unknown',
    }));
  });

  // Extract unary formula constructors (like Bang)
  const unaryConnectives = createMemo(() => {
    const structure = calcData().calc_structure;
    const meta = calcData().calc_structure_rules_meta;
    if (!structure?.Formula) return [];

    const polarities = meta?.polarity || {};

    return Object.entries(structure.Formula)
      .filter(([name, data]: [string, any]) => {
        // Only unary formula constructors (not Atprop, Freevar, Bin)
        return !name.includes('Atprop') &&
               !name.includes('Freevar') &&
               !name.includes('Bin') &&
               Array.isArray(data.type) &&
               data.type.length === 1 &&
               data.type[0] === 'Formula';
      })
      .map(([name, data]: [string, any]) => ({
        name: name.replace('Formula_', ''),
        fullName: name,
        ascii: data.ascii?.replace(/_/g, '').trim() || '',
        latex: data.latex?.replace(/_/g, '').trim() || '',
        polarity: polarities[name] || 'unknown',
      }));
  });

  // Extract inference rules grouped by category
  const ruleGroups = createMemo(() => {
    const rules = calcData().rules || {};
    const meta = calcData().calc_structure_rules_meta?.Contexts || {};

    const groups: { name: string; label: string; rules: { name: string; ruleStrings: string[] }[] }[] = [];

    for (const [ctxName, ctxRules] of Object.entries(rules)) {
      const ctxMeta = meta[ctxName] || {};
      const group = {
        name: ctxName,
        label: ctxMeta.label || ctxName,
        rules: Object.entries(ctxRules as Record<string, string[]>).map(([ruleName, ruleStrings]) => ({
          name: ruleName,
          ruleStrings: ruleStrings,
        })),
      };
      groups.push(group);
    }

    // Sort: Axioms first, then Cut, then Structural, then Logical
    const order = ['RuleZer', 'RuleCut', 'RuleStruct', 'RuleU', 'RuleBin'];
    groups.sort((a, b) => {
      const aIdx = order.indexOf(a.name);
      const bIdx = order.indexOf(b.name);
      if (aIdx === -1 && bIdx === -1) return a.name.localeCompare(b.name);
      if (aIdx === -1) return 1;
      if (bIdx === -1) return -1;
      return aIdx - bIdx;
    });

    return groups;
  });

  // Polarity explanation
  const polarityInfo = createMemo(() => {
    const meta = calcData().calc_structure_rules_meta;
    if (!meta?.polarity) return [];
    return Object.entries(meta.polarity).map(([name, pol]) => ({
      name: name.replace('Formula_', ''),
      polarity: pol as string,
    }));
  });

  return (
    <ErrorBoundary>
      <div class="max-w-6xl mx-auto p-6 space-y-8">
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
              checked={simplified()}
              onChange={(e) => setSimplified(e.currentTarget.checked)}
              class="w-4 h-4 text-blue-600 rounded focus:ring-blue-500"
            />
            <span class="text-sm text-gray-700 dark:text-gray-300">
              Simplified notation (Γ, A, B)
            </span>
          </label>
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
              BNF grammar for formulas, structures, and sequents
            </p>
          </div>
          <div class="p-4 overflow-x-auto">
            <BNFGrammar productions={bnfProductions()} useLatex={true} />
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
                  <th class="px-4 py-2 text-left text-sm font-medium text-gray-600 dark:text-gray-400">Polarity</th>
                </tr>
              </thead>
              <tbody class="divide-y divide-gray-200 dark:divide-gray-700">
                <For each={[...connectives(), ...unaryConnectives()]}>
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
                          <KaTeX latex={conn.latex} />
                        </Show>
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
              <span class="text-red-700 dark:text-red-400"> negative</span> connectives are decomposed lazily (asynchronous).
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
              <KaTeX latex="\\Gamma \\vdash \\Delta" display={true} />
            </div>
            <p>where:</p>
            <ul>
              <li><KaTeX latex="\\Gamma" /> (antecedent) — resources available / assumptions</li>
              <li><KaTeX latex="\\Delta" /> (succedent) — goal to prove / conclusion</li>
              <li><KaTeX latex="\\vdash" /> (turnstile) — entailment relation</li>
            </ul>
            <Show when={simplified()}>
              <p class="mt-4">
                <strong>Simplified notation:</strong> We use <KaTeX latex="\\Gamma, \\Delta, \\Sigma" /> for contexts,
                and <KaTeX latex="A, B, C" /> for formulas.
              </p>
            </Show>
            <Show when={!simplified()}>
              <p class="mt-4">
                <strong>Full notation:</strong> Metavariables like <code>?X</code>, <code>F?A</code> show the exact
                matching patterns used by the proof engine.
              </p>
            </Show>
          </div>
        </section>

        {/* Section 4: Inference Rules */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              4. Inference Rules
            </h3>
            <p class="text-sm text-gray-500 dark:text-gray-400 mt-1">
              Rules are written in fraction notation: premises above, conclusion below
            </p>
          </div>
          <div class="p-4 space-y-8">
            <For each={ruleGroups()}>
              {(group) => (
                <div>
                  <h4 class="text-lg font-semibold text-gray-800 dark:text-gray-200 mb-4 pb-2 border-b border-gray-200 dark:border-gray-700">
                    {group.label}
                    <span class="ml-2 text-sm font-normal text-gray-500">
                      ({group.rules.length} rule{group.rules.length !== 1 ? 's' : ''})
                    </span>
                  </h4>
                  <div class="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
                    <For each={group.rules}>
                      {(rule) => (
                        <SequentRule
                          name={rule.name}
                          ruleStrings={rule.ruleStrings}
                          simplified={simplified()}
                          showAscii={showAscii()}
                        />
                      )}
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
              <p>
                The <code>[A]</code> notation indicates a <strong>focused formula</strong> — the current
                focus of decomposition during the positive phase.
              </p>
            </div>
          </section>
        </Show>
      </div>
    </ErrorBoundary>
  );
}
