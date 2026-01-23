import { createMemo, For, Show, createSignal } from 'solid-js';
import KaTeX from '../components/math/KaTeX';
import ErrorBoundary from '../components/common/ErrorBoundary';

// @ts-ignore - CommonJS module
import * as CalcModule from '../../../lib/calc.js';

const Calc = (CalcModule as any).default || CalcModule;

/**
 * Code block component for JSON/code examples
 */
function CodeBlock(props: { code: string; language?: string }) {
  return (
    <pre class="bg-gray-900 text-gray-100 rounded-lg p-4 overflow-x-auto text-sm font-mono">
      <code>{props.code}</code>
    </pre>
  );
}

export default function MetaOverview() {
  const [expandedSection, setExpandedSection] = createSignal<string | null>(null);

  const calcData = createMemo(() => Calc.calc || {});
  const calcName = createMemo(() => calcData().calc_name || 'Calculus');

  // Extract sort names from calc_structure
  const sortNames = createMemo(() => {
    const structure = calcData().calc_structure;
    if (!structure) return [];
    return Object.keys(structure).filter(name => !name.includes('_Op'));
  });

  // Metavariable conventions (framework-level, not object-level)
  const metavars = [
    { pattern: '?X, ?Y, ?Z', meaning: 'Structure metavariable', example: '?X |- ?Y' },
    { pattern: 'F?A, F?B', meaning: 'Formula metavariable', example: 'F?A * F?B' },
    { pattern: 'S?A, S?B', meaning: 'Structure-in-formula metavariable', example: 'S?A, S?B' },
    { pattern: 'A?a, A?b', meaning: 'Atomic proposition variable', example: 'A?a -o A?a' },
    { pattern: '--', meaning: 'Neutral/wildcard term', example: '-- : F?A' },
  ];

  return (
    <ErrorBoundary>
      <div class="max-w-5xl mx-auto p-6 space-y-8">
        {/* Header */}
        <div>
          <h2 class="text-2xl font-bold text-gray-900 dark:text-white mb-2">
            Framework Documentation
          </h2>
          <p class="text-gray-600 dark:text-gray-400">
            How to read, write, and extend calculus specifications in the display calculus framework.
          </p>
        </div>

        {/* Section 1: What is a Display Calculus? */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              1. What is a Display Calculus?
            </h3>
          </div>
          <div class="p-4 prose dark:prose-invert max-w-none text-sm">
            <p>
              A <strong>display calculus</strong> (Belnap 1982) is a generalization of Gentzen's sequent calculus
              that uses <em>structural connectives</em> alongside logical connectives. Key features:
            </p>
            <ul>
              <li>
                <strong>Display Property</strong>: Any subformula can be "displayed" (isolated) on one side
                of the turnstile using structural rules alone.
              </li>
              <li>
                <strong>Eight Conditions</strong>: Syntactic conditions that guarantee cut elimination.
              </li>
              <li>
                <strong>Modularity</strong>: New connectives can be added without breaking metatheory.
              </li>
            </ul>
            <p>
              This framework implements display calculi as declarative JSON specifications, with automatic
              parser generation and multi-format output.
            </p>
          </div>
        </section>

        {/* Section 2: The ll.json Specification Format */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              2. The ll.json Specification Format
            </h3>
          </div>
          <div class="p-4 space-y-6">
            <div class="prose dark:prose-invert max-w-none text-sm">
              <p>A calculus is defined in a JSON file with the following structure:</p>
            </div>

            <CodeBlock code={`{
  "calc_name": "LLog",
  "calc_structure": { ... },           // Syntax (sorts & constructors)
  "calc_structure_rules_meta": { ... }, // Metadata (polarity, labels)
  "calc_structure_rules": { ... },      // Rule names/categories
  "rules": { ... }                      // Inference rules
}`} />

            {/* 2.1 calc_structure */}
            <div class="space-y-3">
              <h4 class="font-semibold text-gray-800 dark:text-gray-200">
                2.1 Defining Sorts (<code class="text-sm">calc_structure</code>)
              </h4>
              <p class="text-sm text-gray-600 dark:text-gray-400">
                Each sort is a syntactic category. Constructors define how terms of that sort are built:
              </p>
              <CodeBlock code={`"Formula": {
  "Formula_Tensor": {
    "type": ["Formula", "Formula"],  // Two Formula children
    "ascii": "_ * _",                // Display format
    "latex": "_ \\\\otimes _",
    "isabelle": "_ \\<otimes> _",
    "precedence": [320, 320, 321]    // Binding strength
  },
  "Formula_Atprop": {
    "type": "string"                 // Terminal (atomic prop)
  }
}`} />
              <div class="overflow-x-auto">
                <table class="w-full text-sm">
                  <thead>
                    <tr class="bg-gray-50 dark:bg-gray-700/30">
                      <th class="px-3 py-2 text-left font-medium text-gray-600 dark:text-gray-400">Field</th>
                      <th class="px-3 py-2 text-left font-medium text-gray-600 dark:text-gray-400">Purpose</th>
                    </tr>
                  </thead>
                  <tbody class="divide-y divide-gray-200 dark:divide-gray-700">
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">type</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">Child sorts (array) or "string" for terminals</td>
                    </tr>
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">ascii</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">ASCII rendering template (<code>_</code> = child)</td>
                    </tr>
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">latex</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">LaTeX rendering template</td>
                    </tr>
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">isabelle</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">Isabelle/HOL export format</td>
                    </tr>
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">precedence</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">Operator binding [left, right, result] (higher = tighter)</td>
                    </tr>
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">shallow</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">If true, inline this constructor in parent</td>
                    </tr>
                  </tbody>
                </table>
              </div>
            </div>

            {/* 2.2 Metavariables */}
            <div class="space-y-3">
              <h4 class="font-semibold text-gray-800 dark:text-gray-200">
                2.2 Metavariable Conventions
              </h4>
              <p class="text-sm text-gray-600 dark:text-gray-400">
                Rules use schematic variables (metavariables) that match any term of the appropriate sort:
              </p>
              <div class="overflow-x-auto">
                <table class="w-full text-sm">
                  <thead>
                    <tr class="bg-gray-50 dark:bg-gray-700/30">
                      <th class="px-3 py-2 text-left font-medium text-gray-600 dark:text-gray-400">Pattern</th>
                      <th class="px-3 py-2 text-left font-medium text-gray-600 dark:text-gray-400">Meaning</th>
                      <th class="px-3 py-2 text-left font-medium text-gray-600 dark:text-gray-400">Example</th>
                    </tr>
                  </thead>
                  <tbody class="divide-y divide-gray-200 dark:divide-gray-700">
                    <For each={metavars}>
                      {(mv) => (
                        <tr>
                          <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">{mv.pattern}</td>
                          <td class="px-3 py-2 text-gray-600 dark:text-gray-400">{mv.meaning}</td>
                          <td class="px-3 py-2 font-mono text-gray-500 dark:text-gray-500">{mv.example}</td>
                        </tr>
                      )}
                    </For>
                  </tbody>
                </table>
              </div>
            </div>

            {/* 2.3 Defining Rules */}
            <div class="space-y-3">
              <h4 class="font-semibold text-gray-800 dark:text-gray-200">
                2.3 Defining Inference Rules
              </h4>
              <p class="text-sm text-gray-600 dark:text-gray-400">
                Rules are arrays: <code>[conclusion, premise1, premise2, ...]</code>
              </p>
              <CodeBlock code={`"rules": {
  "RuleBin": {
    "Tensor_L": [
      "?X, -- : F?A * F?B |- ?Y",    // Conclusion
      "?X, -- : F?A, -- : F?B |- ?Y" // Premise
    ],
    "Tensor_R": [
      "?X, ?Y |- -- : [ F?A * F?B ]", // Conclusion
      "?X |- -- : [ F?A ]",           // Premise 1
      "?Y |- -- : [ F?B ]"            // Premise 2
    ]
  }
}`} />
              <p class="text-sm text-gray-600 dark:text-gray-400">
                The <code>[A]</code> notation marks a <strong>focused formula</strong> — the principal formula
                being decomposed during proof search.
              </p>
            </div>

            {/* 2.4 Metadata */}
            <div class="space-y-3">
              <h4 class="font-semibold text-gray-800 dark:text-gray-200">
                2.4 Metadata (<code class="text-sm">calc_structure_rules_meta</code>)
              </h4>
              <CodeBlock code={`"calc_structure_rules_meta": {
  "polarity": {
    "Formula_Tensor": "positive",
    "Formula_Loli": "negative"
  },
  "Contexts": {
    "RuleZer": { "label": "Axioms", "simp": true },
    "RuleBin": { "label": "Logical rules (binary)" },
    "RuleStruct": { "label": "Structural rules" }
  }
}`} />
            </div>
          </div>
        </section>

        {/* Section 3: Adding a New Connective */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              3. Adding a New Connective
            </h3>
          </div>
          <div class="p-4 space-y-4">
            <p class="text-sm text-gray-600 dark:text-gray-400">
              To add a new logical connective (e.g., additive disjunction <KaTeX latex="\oplus" />):
            </p>

            <div class="space-y-4">
              <div class="flex gap-3">
                <span class="flex-shrink-0 w-6 h-6 rounded-full bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-400 flex items-center justify-center text-sm font-medium">1</span>
                <div>
                  <p class="font-medium text-gray-900 dark:text-white">Add the operator</p>
                  <p class="text-sm text-gray-600 dark:text-gray-400">In <code>calc_structure.Formula_Bin_Op</code>:</p>
                  <CodeBlock code={`"Formula_Plus": {
  "ascii": "+",
  "latex": "\\\\oplus"
}`} />
                </div>
              </div>

              <div class="flex gap-3">
                <span class="flex-shrink-0 w-6 h-6 rounded-full bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-400 flex items-center justify-center text-sm font-medium">2</span>
                <div>
                  <p class="font-medium text-gray-900 dark:text-white">Set polarity</p>
                  <p class="text-sm text-gray-600 dark:text-gray-400">In <code>calc_structure_rules_meta.polarity</code>:</p>
                  <CodeBlock code={`"Formula_Plus": "positive"`} />
                </div>
              </div>

              <div class="flex gap-3">
                <span class="flex-shrink-0 w-6 h-6 rounded-full bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-400 flex items-center justify-center text-sm font-medium">3</span>
                <div>
                  <p class="font-medium text-gray-900 dark:text-white">Define inference rules</p>
                  <p class="text-sm text-gray-600 dark:text-gray-400">In <code>rules.RuleBin</code>:</p>
                  <CodeBlock code={`"Plus_L": [
  "?X, -- : F?A + F?B |- ?Y",
  "?X, -- : F?A |- ?Y",
  "?X, -- : F?B |- ?Y"
],
"Plus_R1": [
  "?X |- -- : [ F?A + F?B ]",
  "?X |- -- : [ F?A ]"
],
"Plus_R2": [
  "?X |- -- : [ F?A + F?B ]",
  "?X |- -- : [ F?B ]"
]`} />
                </div>
              </div>

              <div class="flex gap-3">
                <span class="flex-shrink-0 w-6 h-6 rounded-full bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-400 flex items-center justify-center text-sm font-medium">4</span>
                <div>
                  <p class="font-medium text-gray-900 dark:text-white">Regenerate the parser</p>
                  <p class="text-sm text-gray-600 dark:text-gray-400">Run: <code>npm run build:parser</code></p>
                </div>
              </div>
            </div>
          </div>
        </section>

        {/* Section 4: The Parser Pipeline */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              4. The Parser Pipeline
            </h3>
          </div>
          <div class="p-4 space-y-4">
            <div class="flex items-center justify-center gap-2 text-sm font-mono flex-wrap">
              <span class="px-3 py-1 bg-blue-100 dark:bg-blue-900/30 text-blue-800 dark:text-blue-300 rounded">ll.json</span>
              <span class="text-gray-400">→</span>
              <span class="px-3 py-1 bg-purple-100 dark:bg-purple-900/30 text-purple-800 dark:text-purple-300 rounded">calc-genparser</span>
              <span class="text-gray-400">→</span>
              <span class="px-3 py-1 bg-green-100 dark:bg-green-900/30 text-green-800 dark:text-green-300 rounded">Jison grammar</span>
              <span class="text-gray-400">→</span>
              <span class="px-3 py-1 bg-orange-100 dark:bg-orange-900/30 text-orange-800 dark:text-orange-300 rounded">parser.js</span>
              <span class="text-gray-400">→</span>
              <span class="px-3 py-1 bg-red-100 dark:bg-red-900/30 text-red-800 dark:text-red-300 rounded">AST</span>
            </div>

            <div class="prose dark:prose-invert max-w-none text-sm">
              <ul>
                <li><strong>ll.json</strong> defines the grammar declaratively</li>
                <li><strong>calc-genparser</strong> generates a Jison grammar file</li>
                <li><strong>Jison</strong> compiles this to a JavaScript parser</li>
                <li><strong>parser.js</strong> parses input strings into AST nodes</li>
                <li><strong>Node.toString()</strong> renders the AST in different formats (ascii, latex, isabelle)</li>
              </ul>
              <p>
                The <code>precedence</code> field controls parsing ambiguity resolution:
                higher values bind tighter. The format is <code>[left, right, result]</code>
                where left/right are the binding strength on each side.
              </p>
            </div>
          </div>
        </section>

        {/* Section 5: Structural vs Logical Rules */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              5. Rule Categories
            </h3>
          </div>
          <div class="p-4 space-y-4">
            <div class="grid md:grid-cols-2 gap-4">
              <div class="p-4 bg-gray-50 dark:bg-gray-700/30 rounded-lg">
                <h4 class="font-semibold text-gray-900 dark:text-white mb-2">
                  Structural Rules
                </h4>
                <p class="text-sm text-gray-600 dark:text-gray-400">
                  Manipulate structure without touching formulas. Enable the display property
                  by allowing any substructure to be isolated. Examples: associativity,
                  commutativity, unit laws.
                </p>
                <p class="text-sm text-gray-500 dark:text-gray-500 mt-2">
                  Category: <code>RuleStruct</code>
                </p>
              </div>

              <div class="p-4 bg-gray-50 dark:bg-gray-700/30 rounded-lg">
                <h4 class="font-semibold text-gray-900 dark:text-white mb-2">
                  Logical Rules
                </h4>
                <p class="text-sm text-gray-600 dark:text-gray-400">
                  Introduce or eliminate logical connectives. Have a principal formula
                  in the conclusion that is being decomposed.
                </p>
                <p class="text-sm text-gray-500 dark:text-gray-500 mt-2">
                  Categories: <code>RuleU</code> (unary), <code>RuleBin</code> (binary)
                </p>
              </div>

              <div class="p-4 bg-gray-50 dark:bg-gray-700/30 rounded-lg">
                <h4 class="font-semibold text-gray-900 dark:text-white mb-2">
                  Identity Rules
                </h4>
                <p class="text-sm text-gray-600 dark:text-gray-400">
                  Axioms that close proof branches. Match atomic propositions or handle
                  unit elements.
                </p>
                <p class="text-sm text-gray-500 dark:text-gray-500 mt-2">
                  Category: <code>RuleZer</code>
                </p>
              </div>

              <div class="p-4 bg-gray-50 dark:bg-gray-700/30 rounded-lg">
                <h4 class="font-semibold text-gray-900 dark:text-white mb-2">
                  Cut Rule
                </h4>
                <p class="text-sm text-gray-600 dark:text-gray-400">
                  Allows composing proofs. Cut elimination is a key metatheoretic property
                  ensuring proof normalization.
                </p>
                <p class="text-sm text-gray-500 dark:text-gray-500 mt-2">
                  Category: <code>RuleCut</code>
                </p>
              </div>
            </div>
          </div>
        </section>

        {/* Section 6: Current Calculus Sorts */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              6. Sorts in {calcName()}
            </h3>
          </div>
          <div class="p-4">
            <p class="text-sm text-gray-600 dark:text-gray-400 mb-4">
              The currently loaded calculus defines these syntactic categories:
            </p>
            <div class="flex flex-wrap gap-2">
              <For each={sortNames()}>
                {(sort) => (
                  <span class="px-3 py-1 bg-gray-100 dark:bg-gray-700 text-gray-800 dark:text-gray-200 rounded font-mono text-sm">
                    {sort}
                  </span>
                )}
              </For>
            </div>
            <p class="text-sm text-gray-500 dark:text-gray-500 mt-4">
              See the <strong>Calculus Overview</strong> tab for the complete syntax and inference rules.
            </p>
          </div>
        </section>

        {/* References */}
        <section class="bg-blue-50 dark:bg-blue-900/20 rounded-lg p-4">
          <h4 class="font-semibold text-blue-900 dark:text-blue-200 mb-2">References</h4>
          <ul class="text-sm text-blue-800 dark:text-blue-300 space-y-1">
            <li>Belnap, N.D. (1982). "Display logic". Journal of Philosophical Logic.</li>
            <li>Girard, J.Y. (1987). "Linear logic". Theoretical Computer Science.</li>
            <li>Andreoli, J.M. (1992). "Logic programming with focusing proofs in linear logic".</li>
          </ul>
        </section>
      </div>
    </ErrorBoundary>
  );
}
