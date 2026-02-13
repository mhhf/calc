import { createMemo, For, Show, createSignal } from 'solid-js';
import KaTeX from '../components/math/KaTeX';
import ErrorBoundary from '../components/common/ErrorBoundary';

// v2 API
import {
  getCalculusName,
  getSortNames,
  getMetavarConventions,
  getFormulaConnectives
} from '../lib/calculus';

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

  // Get calculus data from v2 API
  const calcName = createMemo(() => getCalculusName());
  const sortNames = createMemo(() => getSortNames());
  const metavars = createMemo(() => getMetavarConventions());
  const connectives = createMemo(() => getFormulaConnectives());

  return (
    <ErrorBoundary>
      <div class="max-w-5xl mx-auto p-6 space-y-8 text-gray-900 dark:text-gray-100">
        {/* Header */}
        <div>
          <h2 class="text-2xl font-bold text-gray-900 dark:text-white mb-2">
            Framework Documentation
          </h2>
          <p class="text-gray-600 dark:text-gray-400">
            How to read, write, and extend calculus specifications in the v2 DSL framework.
          </p>
        </div>

        {/* Section 1: What is a Display Calculus? */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              1. What is Linear Logic?
            </h3>
          </div>
          <div class="p-4 prose dark:prose-invert max-w-none text-sm">
            <p>
              <strong>Linear logic</strong> (Girard 1987) is a resource-sensitive logic where
              hypotheses must be used exactly once. Key features:
            </p>
            <ul>
              <li>
                <strong>Resource Sensitivity</strong>: Unlike classical logic, you can't duplicate
                or discard hypotheses freely. Each formula is a "resource" that must be consumed.
              </li>
              <li>
                <strong>Exponentials</strong>: The <KaTeX latex="!" /> modality allows controlled
                reuse - <KaTeX latex="!A" /> can be used any number of times.
              </li>
              <li>
                <strong>Focusing</strong>: Andreoli's focusing discipline (1992) organizes proof
                search into phases, making it efficient and complete.
              </li>
            </ul>
            <p>
              This framework implements linear logic as declarative specifications (.calc/.rules files),
              with automatic parser generation and focused proof search.
            </p>
          </div>
        </section>

        {/* Section 2: The .calc/.rules Specification Format */}
        <section class="bg-white dark:bg-gray-800 rounded-lg shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
          <div class="px-4 py-3 bg-gray-50 dark:bg-gray-700/50 border-b border-gray-200 dark:border-gray-700">
            <h3 class="font-semibold text-gray-900 dark:text-white">
              2. The .calc/.rules Specification Format
            </h3>
          </div>
          <div class="p-4 space-y-6">
            <div class="prose dark:prose-invert max-w-none text-sm">
              <p>A calculus is defined in two files:</p>
              <ul>
                <li><code>.calc</code> — Syntax definitions (types, constructors)</li>
                <li><code>.rules</code> — Inference rules</li>
              </ul>
            </div>

            {/* 2.1 .calc file */}
            <div class="space-y-3">
              <h4 class="font-semibold text-gray-800 dark:text-gray-200">
                2.1 Defining Types (<code class="text-sm">.calc</code>)
              </h4>
              <p class="text-sm text-gray-600 dark:text-gray-400">
                Types define syntactic categories. Constructors define how terms are built:
              </p>
              <CodeBlock code={`// Base types
type formula
type structure
type sequent

// Constructors with annotations
constructor tensor : formula -> formula -> formula
  @ascii "_ * _"
  @latex "#1 \\\\otimes #2"
  @prec 60 left
  @category multiplicative

constructor loli : formula -> formula -> formula
  @ascii "_ -o _"
  @latex "#1 \\\\multimap #2"
  @prec 50 right
  @category multiplicative

constructor bang : formula -> formula
  @ascii "! _"
  @latex "!#1"
  @prec 80`} />
              <div class="overflow-x-auto">
                <table class="w-full text-sm">
                  <thead>
                    <tr class="bg-gray-50 dark:bg-gray-700/30">
                      <th class="px-3 py-2 text-left font-medium text-gray-600 dark:text-gray-400">Annotation</th>
                      <th class="px-3 py-2 text-left font-medium text-gray-600 dark:text-gray-400">Purpose</th>
                    </tr>
                  </thead>
                  <tbody class="divide-y divide-gray-200 dark:divide-gray-700">
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">@ascii</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">ASCII rendering (<code>_</code> = child)</td>
                    </tr>
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">@latex</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">LaTeX rendering (<code>#1</code>, <code>#2</code> = children)</td>
                    </tr>
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">@prec</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">Precedence and associativity</td>
                    </tr>
                    <tr>
                      <td class="px-3 py-2 font-mono text-gray-900 dark:text-white">@category</td>
                      <td class="px-3 py-2 text-gray-600 dark:text-gray-400">Connective category (multiplicative, additive, exponential)</td>
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
                    <For each={metavars()}>
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
                2.3 Defining Inference Rules (<code class="text-sm">.rules</code>)
              </h4>
              <p class="text-sm text-gray-600 dark:text-gray-400">
                Rules are written with premises above and conclusion below:
              </p>
              <CodeBlock code={`// Identity axiom
rule id
  -----------------
  deriv (seq empty (hyp any A) (hyp any A))

// Tensor right (context splitting)
rule tensor_r
  deriv (seq G D (hyp any A))
  deriv (seq G D' (hyp any B))
  -----------------
  deriv (seq G (comma D D') (hyp any (tensor A B)))

// Loli right (implication introduction)
rule loli_r
  deriv (seq G (comma D (hyp any A)) (hyp any B))
  -----------------
  deriv (seq G D (hyp any (loli A B)))`} />
              <p class="text-sm text-gray-600 dark:text-gray-400">
                The <code>deriv</code> wrapper indicates a derivable judgment.
                Context variables (D, D', G) are split among premises for multiplicative rules.
              </p>
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
                  <p class="font-medium text-gray-900 dark:text-white">Add the constructor</p>
                  <p class="text-sm text-gray-600 dark:text-gray-400">In the <code>.calc</code> file:</p>
                  <CodeBlock code={`constructor plus : formula -> formula -> formula
  @ascii "_ + _"
  @latex "#1 \\\\oplus #2"
  @prec 65 left
  @category additive`} />
                </div>
              </div>

              <div class="flex gap-3">
                <span class="flex-shrink-0 w-6 h-6 rounded-full bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-400 flex items-center justify-center text-sm font-medium">2</span>
                <div>
                  <p class="font-medium text-gray-900 dark:text-white">Set polarity</p>
                  <p class="text-sm text-gray-600 dark:text-gray-400">In the <code>.rules</code> file:</p>
                  <CodeBlock code={`polarity plus positive`} />
                </div>
              </div>

              <div class="flex gap-3">
                <span class="flex-shrink-0 w-6 h-6 rounded-full bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-400 flex items-center justify-center text-sm font-medium">3</span>
                <div>
                  <p class="font-medium text-gray-900 dark:text-white">Define inference rules</p>
                  <p class="text-sm text-gray-600 dark:text-gray-400">In the <code>.rules</code> file:</p>
                  <CodeBlock code={`// Plus left (additive - context preserved)
rule plus_l
  deriv (seq G (comma D (hyp any A)) C)
  deriv (seq G (comma D (hyp any B)) C)
  -----------------
  deriv (seq G (comma D (hyp any (plus A B))) C)

// Plus right 1
rule plus_r1
  deriv (seq G D (hyp any A))
  -----------------
  deriv (seq G D (hyp any (plus A B)))

// Plus right 2
rule plus_r2
  deriv (seq G D (hyp any B))
  -----------------
  deriv (seq G D (hyp any (plus A B)))`} />
                </div>
              </div>

              <div class="flex gap-3">
                <span class="flex-shrink-0 w-6 h-6 rounded-full bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-400 flex items-center justify-center text-sm font-medium">4</span>
                <div>
                  <p class="font-medium text-gray-900 dark:text-white">Regenerate the bundle</p>
                  <p class="text-sm text-gray-600 dark:text-gray-400">Run: <code>npm run build:v2-bundle</code></p>
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
              <span class="px-3 py-1 bg-blue-100 dark:bg-blue-900/30 text-blue-800 dark:text-blue-300 rounded">.calc</span>
              <span class="text-gray-400">+</span>
              <span class="px-3 py-1 bg-blue-100 dark:bg-blue-900/30 text-blue-800 dark:text-blue-300 rounded">.rules</span>
              <span class="text-gray-400">→</span>
              <span class="px-3 py-1 bg-purple-100 dark:bg-purple-900/30 text-purple-800 dark:text-purple-300 rounded">Tree-sitter</span>
              <span class="text-gray-400">→</span>
              <span class="px-3 py-1 bg-green-100 dark:bg-green-900/30 text-green-800 dark:text-green-300 rounded">ill.json</span>
              <span class="text-gray-400">→</span>
              <span class="px-3 py-1 bg-orange-100 dark:bg-orange-900/30 text-orange-800 dark:text-orange-300 rounded">Runtime Parser</span>
              <span class="text-gray-400">→</span>
              <span class="px-3 py-1 bg-red-100 dark:bg-red-900/30 text-red-800 dark:text-red-300 rounded">AST</span>
            </div>

            <div class="prose dark:prose-invert max-w-none text-sm">
              <ul>
                <li><strong>.calc + .rules</strong> define the calculus declaratively</li>
                <li><strong>Tree-sitter</strong> parses these into an AST representation</li>
                <li><strong>ill.json</strong> bundles the calculus for browser use</li>
                <li><strong>Runtime Parser</strong> is built from @ascii/@prec annotations</li>
                <li><strong>AST</strong> nodes are rendered in different formats (ascii, latex)</li>
              </ul>
              <p>
                The <code>@prec</code> annotation controls parsing ambiguity resolution:
                higher values bind tighter. Associativity (<code>left</code>/<code>right</code>)
                determines how same-precedence operators are grouped.
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
                  Logical Rules
                </h4>
                <p class="text-sm text-gray-600 dark:text-gray-400">
                  Introduce or eliminate logical connectives. Have a principal formula
                  in the conclusion that is being decomposed.
                </p>
                <p class="text-sm text-gray-500 dark:text-gray-500 mt-2">
                  Examples: <code>tensor_r</code>, <code>loli_l</code>, <code>with_r</code>
                </p>
              </div>

              <div class="p-4 bg-gray-50 dark:bg-gray-700/30 rounded-lg">
                <h4 class="font-semibold text-gray-900 dark:text-white mb-2">
                  Structural Rules
                </h4>
                <p class="text-sm text-gray-600 dark:text-gray-400">
                  Manipulate the structure without touching formulas. In focused proof
                  search, these are implicit in context management.
                </p>
                <p class="text-sm text-gray-500 dark:text-gray-500 mt-2">
                  Examples: <code>copy</code> (for cartesian context)
                </p>
              </div>

              <div class="p-4 bg-gray-50 dark:bg-gray-700/30 rounded-lg">
                <h4 class="font-semibold text-gray-900 dark:text-white mb-2">
                  Identity Axioms
                </h4>
                <p class="text-sm text-gray-600 dark:text-gray-400">
                  Close proof branches when the goal matches a hypothesis.
                </p>
                <p class="text-sm text-gray-500 dark:text-gray-500 mt-2">
                  Example: <code>id</code> (A ⊢ A)
                </p>
              </div>

              <div class="p-4 bg-gray-50 dark:bg-gray-700/30 rounded-lg">
                <h4 class="font-semibold text-gray-900 dark:text-white mb-2">
                  Exponential Rules
                </h4>
                <p class="text-sm text-gray-600 dark:text-gray-400">
                  Handle the ! modality for controlled reuse. Includes promotion,
                  dereliction, and absorption.
                </p>
                <p class="text-sm text-gray-500 dark:text-gray-500 mt-2">
                  Examples: <code>promotion</code>, <code>dereliction</code>, <code>absorption</code>
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
            <li>Girard, J.Y. (1987). "Linear logic". Theoretical Computer Science.</li>
            <li>Andreoli, J.M. (1992). "Logic programming with focusing proofs in linear logic".</li>
            <li>Belnap, N.D. (1982). "Display logic". Journal of Philosophical Logic.</li>
          </ul>
        </section>
      </div>
    </ErrorBoundary>
  );
}
