# Frontend Refactor: CycleJS → SolidJS

## Overview

Rewrite the frontend from CycleJS/static HTML generators to a clean SolidJS single-page application with three tabs: Sandbox, Calculus Overview, and Display Calculus Overview.

## Tech Stack

| Layer | Current | New |
|-------|---------|-----|
| Framework | CycleJS + xstream | SolidJS |
| Build | Webpack | Vite + vite-plugin-solid |
| Language | JavaScript | TypeScript |
| Styling | Plain CSS | Tailwind CSS v4 |
| Math | KaTeX 0.8.2 | KaTeX (latest) |
| Graphs | Viz.js (Graphviz) | solid-g6 (@antv/g6) |
| Router | None | @solidjs/router |

## Architecture Principles

1. **lib/ is the core** - All logic stays in `lib/`. UI imports directly from lib.
2. **No bridge/wrapper pattern** - TypeScript types live alongside lib modules, not in UI.
3. **UI is purely presentational** - `src/ui/` contains ONLY SolidJS components, pages, and UI-specific state.
4. **CLI remains independent** - `libexec/` continues to work exactly as before.

## Directory Structure

### Core Library (lib/) - Enhanced with TypeScript

```
lib/
├── types/                    # NEW: TypeScript definitions for all lib modules
│   ├── index.d.ts            # Re-exports all types
│   ├── calc.d.ts             # Calc class, db structure, rule types
│   ├── node.d.ts             # Node AST class and methods
│   ├── sequent.d.ts          # Sequent class
│   ├── pt.d.ts               # Proof tree class
│   └── parser.d.ts           # Parser types
│
├── calc.js                   # (existing) Calculus database
├── node.js                   # (existing) AST representation
├── parser.js                 # (existing) Jison grammar generation
├── sequent.js                # (existing) Logical sequents
├── proofstate.js             # (existing) Proof search
├── pt.js                     # (existing) Proof trees
├── helper.js                 # (existing) Utilities
├── mgu.js                    # (existing) Unification
├── substitute.js             # (existing) Substitution
├── compare.js                # (existing) Comparison
├── ressource.js              # (existing) Resource extraction
├── runner.js                 # (existing) Orchestration
├── llt_compiler.js           # (existing, Node-only)
└── ruleset.js                # (existing, Node-only)
```

### UI Layer (src/ui/) - Purely Presentational

```
src/ui/
├── index.html
├── index.tsx                 # Bootstrap: init Calc, mount App
├── App.tsx                   # Router + shell
├── vite.config.ts
├── tsconfig.json
├── tailwind.config.ts
│
├── components/
│   ├── layout/
│   │   ├── TabNav.tsx        # Tab navigation using @solidjs/router
│   │   └── Shell.tsx         # App container
│   │
│   ├── math/
│   │   ├── KaTeX.tsx         # Renders LaTeX string to HTML
│   │   ├── FormulaInput.tsx  # Input field + parse error display
│   │   ├── InferenceRule.tsx # Single inference rule display
│   │   └── RuleGrid.tsx      # Grid/list of rules
│   │
│   ├── graph/
│   │   ├── ProofTree.tsx     # Proof tree via solid-g6
│   │   └── ASTView.tsx       # AST visualization
│   │
│   └── common/
│       ├── ErrorBoundary.tsx
│       └── Loading.tsx
│
├── pages/
│   ├── Sandbox.tsx           # Interactive formula sandbox
│   ├── CalculusOverview.tsx  # Rules overview (replaces calculus.html)
│   └── MetaOverview.tsx      # Meta-calculus (replaces calculus-meta.html)
│
├── state/
│   └── ui.ts                 # UI-only state: active filters, toggles, form values
│
└── styles/
    └── app.css               # Tailwind directives + custom styles
```

## Module Boundaries

```
┌─────────────────────────────────────────────────────────────────┐
│                         ll.json (data)                          │
└──────────────────────────────┬──────────────────────────────────┘
                               │
              ┌────────────────┼────────────────┐
              │                │                │
              ▼                ▼                ▼
       ┌──────────┐     ┌──────────┐     ┌──────────┐
       │ libexec/ │     │   lib/   │     │ src/ui/  │
       │  (CLI)   │     │  (core)  │     │  (UI)    │
       └────┬─────┘     └────┬─────┘     └────┬─────┘
            │                │                │
            │   imports      │   imports      │
            └───────────────►│◄──────────────┘
                             │
                    ┌────────┴────────┐
                    │   lib/types/    │
                    │ (TS definitions)│
                    └─────────────────┘
```

**Key rule:** Arrows only point INTO lib/. Nothing in lib/ imports from libexec/ or src/ui/.

## Type Definitions (lib/types/)

### calc.d.ts
```typescript
export interface Rule {
  id: number
  name: string
  ctx: string
  rule: string
  invertable?: boolean
  _unused_by_proofstate?: boolean
}

export interface CalcDB {
  rules: Record<number, Rule>
  toIds: Record<string, number>
}

export interface Calc {
  db: CalcDB
  initialized: boolean
  init(calc: CalcDefinition): void
  eachStructureRule(calc: CalcDefinition, fn: (rule: Rule) => void): void
}

export const Calc: Calc
```

### node.d.ts
```typescript
export interface ToStringOptions {
  style: 'ascii' | 'latex' | 'latex_se' | 'isabelle' | 'isabelle_se'
}

export interface Node {
  id: number
  vals: Node[]
  copy(): Node
  toString(options?: ToStringOptions): string
  isAtomic(): boolean
  isNegative(): boolean
  isPositive(): boolean
}

export interface NodeStatic {
  new (id: number, vals: Node[]): Node
  toTree(opts: { node: Node; rules: Record<number, Rule>; attrs: string[] }): TreeNode
  toString(node: Node, options?: ToStringOptions): string
}

export const Node: NodeStatic
```

### parser.d.ts
```typescript
import type { Node } from './node'
import type { Calc } from './calc'

export interface Parser {
  parse(input: string): Node
  yy: { Node: typeof Node }
}

export interface ParserModule {
  parser: Parser
  grammar: unknown
  calc: CalcDefinition
  Calc: Calc
}

export function genParser(calc: CalcDefinition): ParserModule
```

## UI Implementation

### Entry Point (index.tsx)

```tsx
import { render } from 'solid-js/web'
import { Router } from '@solidjs/router'
// Direct imports from lib - no wrappers
import { Calc } from '../../lib/calc.js'
import calc from '../../out/calc.json'
import App from './App'
import './styles/app.css'

// Initialize core library (same as CLI does)
Calc.init(calc)

render(() => (
  <Router>
    <App />
  </Router>
), document.getElementById('root')!)
```

### App Shell (App.tsx)

```tsx
import { Route } from '@solidjs/router'
import { lazy, Suspense } from 'solid-js'
import TabNav from './components/layout/TabNav'
import Shell from './components/layout/Shell'
import Loading from './components/common/Loading'

const Sandbox = lazy(() => import('./pages/Sandbox'))
const CalculusOverview = lazy(() => import('./pages/CalculusOverview'))
const MetaOverview = lazy(() => import('./pages/MetaOverview'))

export default function App() {
  return (
    <Shell>
      <TabNav />
      <Suspense fallback={<Loading />}>
        <Route path="/" component={Sandbox} />
        <Route path="/calculus" component={CalculusOverview} />
        <Route path="/meta" component={MetaOverview} />
      </Suspense>
    </Shell>
  )
}
```

### Sandbox Page (pages/Sandbox.tsx)

```tsx
import { createSignal, createMemo, Show } from 'solid-js'
// Direct lib imports
import parser from '../../../out/parser.js'
import { Node } from '../../../lib/node.js'
import { Calc } from '../../../lib/calc.js'
import helper from '../../../lib/helper.js'
// UI components
import KaTeX from '../components/math/KaTeX'
import FormulaInput from '../components/math/FormulaInput'
import ProofTree from '../components/graph/ProofTree'

export default function Sandbox() {
  const [input, setInput] = createSignal('')
  const [error, setError] = createSignal<string | null>(null)

  const parsed = createMemo(() => {
    const formula = input().trim()
    if (!formula) return null
    try {
      const node = parser.parse(formula)
      setError(null)
      return node
    } catch (e) {
      setError(e.message)
      return null
    }
  })

  const latex = createMemo(() => {
    const node = parsed()
    return node ? node.toString({ style: 'latex_se' }) : ''
  })

  const treeData = createMemo(() => {
    const node = parsed()
    if (!node) return null
    return Node.toTree({
      node,
      rules: Calc.db.rules,
      attrs: ['constr', 'ascii', 'formula']
    })
  })

  return (
    <div class="p-4 space-y-4">
      <FormulaInput value={input()} onInput={setInput} error={error()} />

      <Show when={parsed()}>
        <div class="bg-white rounded-lg p-4 shadow">
          <KaTeX latex={latex()} display />
        </div>
      </Show>

      <Show when={treeData()}>
        <ProofTree data={treeData()!} />
      </Show>
    </div>
  )
}
```

### Calculus Overview Page (pages/CalculusOverview.tsx)

```tsx
import { createSignal, For, Show, createMemo } from 'solid-js'
import { Calc } from '../../../lib/calc.js'
import parser from '../../../out/parser.js'
import InferenceRule from '../components/math/InferenceRule'

export default function CalculusOverview() {
  const [showAll, setShowAll] = createSignal(false)
  const [filter, setFilter] = createSignal('')

  const rules = createMemo(() => {
    const all = Object.values(Calc.db.rules)
    const filtered = showAll()
      ? all
      : all.filter(r => !r._unused_by_proofstate)

    const search = filter().toLowerCase()
    return search
      ? filtered.filter(r => r.name.toLowerCase().includes(search))
      : filtered
  })

  // Group by context
  const grouped = createMemo(() => {
    const groups: Record<string, typeof rules.value> = {}
    for (const rule of rules()) {
      const ctx = rule.ctx || 'Other'
      groups[ctx] = groups[ctx] || []
      groups[ctx].push(rule)
    }
    return groups
  })

  return (
    <div class="p-4">
      <div class="flex gap-4 mb-6">
        <input
          type="text"
          placeholder="Filter rules..."
          class="border rounded px-3 py-2"
          value={filter()}
          onInput={e => setFilter(e.target.value)}
        />
        <label class="flex items-center gap-2">
          <input
            type="checkbox"
            checked={showAll()}
            onChange={e => setShowAll(e.target.checked)}
          />
          Show structural rules
        </label>
      </div>

      <For each={Object.entries(grouped())}>
        {([ctx, ctxRules]) => (
          <section class="mb-8">
            <h2 class="text-xl font-bold mb-4">{ctx}</h2>
            <div class="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
              <For each={ctxRules}>
                {rule => <InferenceRule rule={rule} parser={parser} />}
              </For>
            </div>
          </section>
        )}
      </For>
    </div>
  )
}
```

### KaTeX Component (components/math/KaTeX.tsx)

```tsx
import katex from 'katex'
import { createMemo } from 'solid-js'

interface Props {
  latex: string
  display?: boolean
}

export default function KaTeX(props: Props) {
  const html = createMemo(() => {
    try {
      return katex.renderToString(props.latex, {
        displayMode: props.display ?? false,
        throwOnError: false,
      })
    } catch {
      return `<span class="text-red-500">${props.latex}</span>`
    }
  })

  return <span innerHTML={html()} />
}
```

### UI State (state/ui.ts)

Only UI-specific reactive state - no core logic:

```tsx
import { createSignal } from 'solid-js'

// Filter state for Calculus Overview
export const [ruleFilter, setRuleFilter] = createSignal('')
export const [showStructuralRules, setShowStructuralRules] = createSignal(false)

// Dark mode toggle
export const [darkMode, setDarkMode] = createSignal(false)
```

## Build Configuration

### Vite Config (src/ui/vite.config.ts)

```ts
import { defineConfig } from 'vite'
import solid from 'vite-plugin-solid'
import path from 'path'

export default defineConfig({
  plugins: [solid()],
  root: '.',
  build: {
    outDir: '../../out/ui',
    emptyOutDir: true,
  },
  resolve: {
    alias: {
      '@': path.resolve(__dirname, '.'),
    },
  },
})
```

### TypeScript Config (src/ui/tsconfig.json)

```json
{
  "compilerOptions": {
    "target": "ESNext",
    "module": "ESNext",
    "moduleResolution": "bundler",
    "jsx": "preserve",
    "jsxImportSource": "solid-js",
    "strict": true,
    "noEmit": true,
    "isolatedModules": true,
    "paths": {
      "@/*": ["./*"]
    }
  },
  "include": ["./**/*.ts", "./**/*.tsx", "../../lib/types/**/*.d.ts"]
}
```

### Tailwind Config (src/ui/tailwind.config.ts)

```ts
import type { Config } from 'tailwindcss'

export default {
  content: ['./**/*.{ts,tsx,html}'],
  darkMode: 'class',
  theme: {
    extend: {
      colors: {
        positive: '#38a169',
        negative: '#e53e3e',
      },
    },
  },
  plugins: [],
} satisfies Config
```

## Migration Phases

### Phase 1: TypeScript Foundation
1. Create `lib/types/` with .d.ts files for all lib modules
2. Verify types match actual runtime behavior
3. No changes to existing lib/*.js files

### Phase 2: UI Scaffold
1. Create `src/ui/` directory structure
2. Initialize Vite + SolidJS + TypeScript + Tailwind
3. Create basic App shell with router
4. Verify lib modules import correctly in browser

### Phase 3: Components
1. Build KaTeX component
2. Build InferenceRule component
3. Build FormulaInput with error handling
4. Build RuleGrid for calculus display

### Phase 4: Pages
1. Implement Sandbox (port main.js logic)
2. Implement CalculusOverview (port calc-export logic)
3. Implement MetaOverview

### Phase 5: Graph Visualization
1. Install and configure solid-g6
2. Build ASTView component
3. Build ProofTree component

### Phase 6: Polish & Cleanup
1. Dark mode support
2. Responsive design
3. Error boundaries
4. Remove CycleJS, Webpack, viz.js
5. Update Makefile / npm scripts

## npm Scripts

```json
{
  "scripts": {
    "dev": "vite --config src/ui/vite.config.ts",
    "build:ui": "vite build --config src/ui/vite.config.ts",
    "preview": "vite preview --config src/ui/vite.config.ts"
  }
}
```

## Dependencies

### Add
```bash
npm install solid-js @solidjs/router katex @antv/g6 @dschz/solid-g6
npm install -D vite vite-plugin-solid typescript
npm install -D tailwindcss @tailwindcss/vite postcss autoprefixer
```

### Remove
```bash
npm uninstall @cycle/run @cycle/dom xstream viz.js webpack webpack-cli
```

## Key Design Decisions

1. **No wrapper/bridge layer** - UI imports lib/ directly with TypeScript types
2. **Types in lib/types/** - Core type definitions belong with the core library
3. **UI state is minimal** - Only filters, toggles, form values in src/ui/state/
4. **Same init pattern** - UI calls `Calc.init()` just like CLI does
5. **Lazy loading** - Each page loads on demand via `lazy()` + `Suspense`

## References

- [SolidJS Docs](https://docs.solidjs.com/)
- [SolidJS Router](https://docs.solidjs.com/solid-router)
- [SolidJS State Management](https://docs.solidjs.com/guides/state-management)
- [Tailwind CSS + SolidJS](https://docs.solidjs.com/guides/styling-components/tailwind)
- [solid-g6 GitHub](https://github.com/dsnchz/solid-g6)
- [KaTeX API](https://katex.org/docs/api)
- [Vite Plugin Solid](https://github.com/solidjs/vite-plugin-solid)
