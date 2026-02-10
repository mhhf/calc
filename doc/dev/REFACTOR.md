# REFACTOR.md

This document tracks code analysis, technical debt, refactoring plans, and modernization strategies for the CALC proof system.

---

## Table of Contents

1. [Current State Analysis](#current-state-analysis)
2. [Technical Debt](#technical-debt)
3. [Dependency Analysis](#dependency-analysis)
4. [Modernization Plan](#modernization-plan)
5. [Performance Optimization](#performance-optimization)
6. [Rust/Zig Rewrite Strategy](#rustzig-rewrite-strategy)
7. [Migration Checklists](#migration-checklists)
8. [Refactoring TODOs](#refactoring-todos)

---

## Pre-Refactoring Research Question

### Is Display Calculus the Right Choice?

**Status:** Needs deep research before committing to refactoring

**The Question:**
The current implementation uses a **display calculus** style for linear logic (based on calculus-toolbox). Before investing significant effort in refactoring, we need to understand:

1. **What is display calculus?**
   - Belnap's display logic (1982): structural connectives separate from logical connectives
   - "Display property": any formula occurrence can be "displayed" (made principal)
   - Enables modular proof of cut elimination
   - Used in calculus-toolbox (original inspiration for this repo)

2. **What are the alternatives?**
   - Standard sequent calculus (Gentzen-style, one-sided or two-sided)
   - Hypersequent calculus
   - Deep inference / calculus of structures
   - Proof nets (for linear logic specifically)
   - Natural deduction

3. **Potential issues with display calculus:**
   - **Complexity**: More structural rules, more complex proofs
   - **Efficiency**: Display postulates can blow up proof search space
   - **Implementation overhead**: More machinery than standard sequents
   - **Overkill?**: Display calculus shines for modal/substructural logics with complex structural rules - is it needed for our use case?

4. **Questions to answer:**
   - Is display calculus introducing inefficiencies in proof search?
   - Would standard focused sequent calculus be simpler and faster?
   - What do we gain from display calculus that we'd lose otherwise?
   - How does Celf/Ceptre handle this? (They use standard sequents)

**Research Plan:**
- [ ] Study Belnap's original display logic paper
- [ ] Understand what `ll.json` structure rules actually encode
- [ ] Compare proof search complexity: display vs standard sequent
- [ ] Look at how calculus-toolbox uses display calculus
- [ ] Evaluate if we should migrate to simpler sequent calculus

**Key Papers:**
- Belnap, "Display Logic" (1982)
- Goré, "Substructural Logics on Display" (1998)
- Ciabattoni et al., "Hypersequent and Display Calculi – a Unified Perspective" (2014)

**Decision Point:**
This research should be completed BEFORE major refactoring. If display calculus is overkill, we might want to simplify the architecture significantly rather than polish what we have.

---

## Architectural Vision

### Core vs. Calculus Separation

**Goal:** The optimized JS version should cleanly separate:

1. **Core Engine (Gentzen-style sequent calculus machinery)**
   - Sequent data structure (contexts, succedent)
   - Proof tree representation
   - Unification / MGU
   - Substitution
   - Cut elimination (generic)
   - Proof search framework (backtracking, etc.)

2. **Calculus Plugin (e.g., Linear Logic with Focusing)**
   - Connectives and their rules (tensor, lolli, with, etc.)
   - Structural rules (or absence thereof)
   - Polarity assignments
   - Focusing discipline
   - Format-specific rendering (LaTeX, Isabelle, etc.)

**Plugin loading options:**
- **Compile-time:** Generate optimized code for a specific calculus (current `ll.json` approach, but cleaner)
- **Runtime:** Load calculus definition dynamically, interpret rules

**Benefits:**
- Test the core independently of any specific logic
- Experiment with different calculi without changing core code
- Easier to reason about correctness (core is small and stable)
- Enables future Rust/Zig rewrite of just the core
- Educational: see what's "Gentzen" vs what's "Linear Logic"

**Current state:** The codebase mixes core and calculus concerns. `ll.json` defines both grammar (core-ish) and LL-specific rules (calculus). Refactoring should separate these.

**Proposed structure:**
```
lib/
  core/
    sequent.js      # Generic sequent structure
    proof-tree.js   # Generic proof tree
    unify.js        # Unification (MGU)
    substitute.js   # Substitution
    search.js       # Generic proof search framework
  calculi/
    linear-logic/
      rules.json    # LL connectives and rules
      focusing.js   # Focusing discipline
      format.js     # LL-specific formatting
```

---

## Current State Analysis

### Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                        CLI Entry                            │
│                     (calc shell script)                     │
│                           ↓                                 │
│                    libexec/calc-*                           │
│                    (21 CLI commands)                        │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│                      Core Library                           │
├─────────────────────────────────────────────────────────────┤
│  ll.json          │ Calculus definition (grammar, rules)   │
│  parser.js        │ Dynamic Jison grammar generation       │
│  node.js          │ AST representation                     │
│  sequent.js       │ Sequent data structure                 │
│  proofstate.js    │ Proof search engine                    │
│  calc.js          │ Calculus abstraction, dependency order │
│  pt.js            │ Proof tree structure                   │
│  mgu.js           │ Most general unification               │
│  substitute.js    │ Variable substitution                  │
│  ruleset.js       │ Rule management                        │
│  llt_compiler.js  │ LLT rule language compiler             │
│  helper.js        │ Tree-to-DOT, formatting utilities      │
│  intern.js        │ Content-addressed interning             │
│  ressource.js     │ Resource handling                      │
│  runner.js        │ Rule execution                         │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│                       Output Layer                          │
├─────────────────────────────────────────────────────────────┤
│  ASCII, LaTeX, Isabelle, Isabelle_SE formats               │
│  DOT graph generation (Viz.js)                             │
│  Clipboard integration (copy-paste)                        │
└─────────────────────────────────────────────────────────────┘
```

### File-by-File Analysis

#### `lib/proofstate.js` (504 lines) - CRITICAL
**Purpose:** Proof search engine with auto-prover, focusing, forward/backward chaining.

**Key Functions:**
- `Proofstate.auto(pt, o)` - Main recursive proof search
- `Proofstate.getInvertableRule(pt, o)` - Find invertible formula
- `Proofstate.apply(pt, rule_name, id, rule)` - Apply a rule
- `Proofstate.focus(pt, id)` / `Proofstate.blur(pt, pos)` - Focus management
- `Proofstate.tryIdPos/tryIdNeg(pt)` - Identity rule attempts

**Issues:**
- Heavy use of mutation (modifies `pt` in place)
- Complex nested control flow
- Many TODOs in comments
- Magic strings for rule names
- No type annotations

**Refactoring Priority:** HIGH

#### `lib/sequent.js` (418 lines) - CRITICAL
**Purpose:** Sequent data structure with linear and persistent contexts.

**Data Structure:**
```javascript
{
  persistent_ctx: {},     // Set: id -> resource
  linear_ctx: {},         // Multiset: id -> {num, val}
  succedent: Node,        // Goal formula
  focus: Node | null,     // Currently focused formula
  focusPosition: "R"|"L"  // Focus side
}
```

**Key Functions:**
- `Sequent.fromTree(seq)` - Convert AST to sequent
- `Sequent.copy(seq)` - Deep copy
- `Sequent.substitute(theta)` - Apply substitution
- `Sequent.add_to_linear_ctx(seq, ast, num)` - Add to multiset
- `Sequent.remove_from_antecedent(seq, delta)` - Remove from context

**Issues:**
- ~~Uses SHA3/keccak for hashing (heavyweight)~~ → FIXED: Now uses FNV-1a via intern.js
- ~~`id` generation via hash - potential collisions~~ → FIXED: Content-addressed hashing with BigInt
- Mixes concerns (data + formatting)
- Global mutable `varIndex`

**Refactoring Priority:** HIGH

#### `lib/node.js` (234 lines) - HIGH
**Purpose:** AST node representation with format-polymorphic rendering.

**Class Structure:**
```javascript
class Node {
  constructor(id, vals)  // id references ll.json rule, vals are children
  copy()                 // Clone
  doFocus() / doUnfocus()
  isAtomic() / isPositive() / isNegative() / isLax() / isFocus()
  toString(o)            // Format-aware rendering
}
```

**Issues:**
- `id` is numeric index into `Calc.db.rules` - fragile
- Polarity checking traverses structure repeatedly
- `toString` has complex format logic mixed with data

**Refactoring Priority:** MEDIUM

#### `lib/parser.js` (190 lines) - MEDIUM
**Purpose:** Dynamic Jison grammar generation from `ll.json`.

**Approach:**
- Reads `calc_structure` from JSON
- Generates BNF rules programmatically
- Sets up precedence from JSON spec
- Returns Jison parser instance

**Issues:**
- Generates grammar at runtime (slow startup)
- No caching of generated parser
- Jison is outdated/unmaintained
- Complex template string manipulation

**Refactoring Priority:** MEDIUM (parser migration)

#### `lib/calc.js` (232 lines) - MEDIUM
**Purpose:** Calculus abstraction, dependency ordering, rule database.

**Key Structures:**
- `Calc.db.rules` - Rule lookup by numeric ID
- `Calc.db.toIds` - Reverse lookup (name -> ID)
- `Calc.initDB(calc)` - Initialize from JSON

**Issues:**
- Global mutable state (`Calc.db`)
- Complex initialization logic
- Circular dependencies with other modules

**Refactoring Priority:** MEDIUM

#### `ll.json` (606 lines) - CRITICAL CONFIG
**Purpose:** Master calculus definition.

**Structure:**
```json
{
  "calc_name": "LLog",
  "calc_structure": { /* grammar */ },
  "calc_structure_rules_meta": { /* polarity, contexts */ },
  "calc_structure_rules": { /* rule names and labels */ },
  "rules": { /* actual sequent rules */ }
}
```

**Issues:**
- No JSON schema validation
- Precedence array semantics unclear
- Mixing grammar and logic specification
- Some rules commented/experimental

**Refactoring Priority:** HIGH (needs documentation)

---

## Technical Debt

### Code Quality Issues

1. **No Type System**
   - Pure JavaScript with no TypeScript, Flow, or JSDoc
   - Many implicit contracts
   - Easy to pass wrong arguments

2. **Global Mutable State**
   - `Calc.db` is global
   - `Sequent.varIndex` is global counter
   - Parser generated once, used globally

3. **Inconsistent Error Handling**
   - Many functions return `false` on failure
   - Some throw exceptions
   - Console.log for errors

4. **TODO Comments**
   - 30+ TODO comments in codebase
   - Many describe known limitations

5. **Commented Code**
   - Several blocks of commented-out code
   - Unclear if experimental or dead

6. **Magic Strings/Numbers**
   - Rule names as strings throughout
   - Numeric IDs for AST nodes
   - Array index conventions

### Missing Infrastructure

1. **No CI/CD** - No GitHub Actions or similar
2. **No Linting** - No ESLint configuration
3. **No Formatting** - No Prettier
4. **Minimal Tests** - Test files exist but `npm test` is broken
5. **No Documentation** - Only minimal README
6. **No Benchmarks** - No performance testing

---

## Dependency Analysis

### Current Dependencies

| Package | Version | Purpose | Status | Alternative |
|---------|---------|---------|--------|-------------|
| `jison` | N/A | Parser generator | **Outdated** | Chevrotain, Nearley, Peggy |
| `mocha` | ^3.5.0 | Test framework | **Outdated** | Vitest, Jest, Node test |
| `chai` | ^4.1.1 | Assertion library | Stable | Built-in assert, Vitest |
| `katex` | ^0.8.2 | Math rendering | **Outdated** | Update to latest |
| `viz.js` | ^1.8.0 | Graph visualization | **Outdated** | @viz-js/viz, D3 |
| `neodoc` | ^1.4.0 | CLI documentation | Stable | Commander, yargs |
| `readline-sync` | ^1.4.7 | CLI interaction | Stable | Inquirer, prompts |
| `shelljs` | ^0.7.8 | Shell operations | **Outdated** | Node built-ins, execa |
| `copy-paste` | ^1.3.0 | Clipboard | **Outdated** | clipboardy |
| `sha3` | ^1.2.0 | Hashing | Stable | crypto built-in |
| `keccakjs` | ^0.2.1 | Hashing | **Outdated** | crypto, sha3 |

### Recommended Replacements

#### Parser Generator: Jison → **Chevrotain** or **Nearley**

**Chevrotain Pros:**
- Fastest JavaScript parser
- No code generation step (parser defined in JS)
- Excellent error messages
- Active maintenance
- TypeScript support

**Nearley Pros:**
- Handles ambiguous grammars (Earley algorithm)
- Simple BNF-like syntax
- Good for experimentation

**Recommendation:** Chevrotain for performance, Nearley for flexibility

#### Test Framework: Mocha/Chai → **Vitest**

**Pros:**
- Modern ESM support
- Jest-compatible API
- Fast (Vite-based)
- Built-in TypeScript
- Watch mode with HMR

**Migration Path:**
1. Install vitest
2. Rename test files to `.test.js`
3. Replace `require('chai').expect` with vitest's `expect`
4. Update npm scripts

#### Frontend: Cycle.js → **Preact** or **SolidJS** or **HTMX**

**For minimal JS complexity:** HTMX
- Server-rendered HTML with AJAX attributes
- No build step
- Simplest option

**For reactive UI:** Preact or SolidJS
- Preact: React API in 3KB
- SolidJS: Best performance, fine-grained reactivity

**Recommendation:** Start with HTMX for simplicity, consider SolidJS for complex UI later

---

## Modernization Plan

### Phase 1: Infrastructure (Week 1-2)

1. **Add TypeScript**
   ```bash
   npm install -D typescript @types/node
   ```
   - Start with `allowJs: true`
   - Add `.d.ts` files for existing code
   - Gradually convert to `.ts`

2. **Setup Tooling**
   ```bash
   npm install -D eslint prettier vitest
   ```
   - ESLint with TypeScript plugin
   - Prettier for formatting
   - Vitest for testing

3. **Fix npm scripts**
   ```json
   {
     "scripts": {
       "test": "vitest",
       "lint": "eslint lib/",
       "build": "tsc",
       "dev": "vitest --watch"
     }
   }
   ```

4. **Add CI**
   - GitHub Actions for test/lint
   - Dependabot for updates

### Phase 2: Core Refactoring (Week 3-6)

1. **Separate Core from Calculus**
   - Identify which code is "Gentzen machinery" vs "Linear Logic specific"
   - Extract core into `lib/core/` directory
   - Move LL-specific code to `lib/calculi/linear-logic/`
   - Define clean interface between core and calculus plugins

2. **Extract Type Definitions**
   - Define interfaces for Node, Sequent, ProofState
   - Create type for ll.json schema
   - Add JSDoc or convert to TypeScript

3. **Remove Global State**
   - Pass `Calc.db` explicitly
   - Make `varIndex` instance-based
   - Use dependency injection

4. **Improve Error Handling**
   - Define Result type: `{success: true, value} | {success: false, error}`
   - Replace `console.log` with proper logging
   - Add validation at boundaries

5. **Add Tests**
   - Unit tests for core (independent of any calculus)
   - Unit tests for LL calculus
   - Integration tests for proof search
   - Property-based tests for substitution

### Phase 3: Parser Migration (Week 7-8)

1. **Document Current Grammar**
   - Extract BNF from ll.json
   - Write comprehensive grammar spec

2. **Implement in Chevrotain**
   - Define tokens (lexer)
   - Define parser rules
   - Build AST visitor

3. **Benchmark Comparison**
   - Parse time: Jison vs Chevrotain
   - Memory usage
   - Error message quality

### Phase 4: Performance Optimization (Week 9-10)

See [Performance Optimization](#performance-optimization) section.

---

## Performance Optimization

### Profiling Current Bottlenecks

1. **Parser Generation**
   - Jison generates parser at runtime
   - Fix: Pre-generate or use Chevrotain

2. ~~**Hash Computation**~~ **FIXED**
   - ~~SHA3/Keccak for every sequent ID~~ → Now uses FNV-1a (fast, non-crypto)
   - Content-addressed interning via `lib/intern.js` and `lib/hash.js`
   - O(1) equality via hash comparison

3. ~~**Deep Copying**~~ **IMPROVED**
   - ~~`Sequent.copy()` called frequently~~ → Structural sharing via interning
   - Further optimizations available: see `dev/optimization_strategies.md`

4. **String Operations**
   - `toString()` called repeatedly
   - Fix: Lazy evaluation, caching

### JavaScript Performance Tips

1. **Avoid Hidden Class Changes**
   ```javascript
   // Bad: shape changes
   const obj = {};
   obj.a = 1;
   obj.b = 2;

   // Good: consistent shape
   const obj = {a: 1, b: 2};
   ```

2. **Use TypedArrays for Numeric Data**
   ```javascript
   // For quantity tracking
   const quantities = new Float64Array(1000);
   ```

3. **Minimize GC Pressure**
   - Object pooling for frequently created objects
   - Avoid closures in hot paths
   - Reuse arrays instead of creating new ones

4. **Use Map/Set over Object**
   ```javascript
   // Better for dynamic keys
   const ctx = new Map();
   ctx.set(id, {num, val});
   ```

### Data Structure Improvements

1. **Persistent Data Structures**
   - Use Immutable.js or Immer for sequents
   - Enables structural sharing
   - Simpler backtracking

2. **Efficient Multiset**
   ```javascript
   class Multiset {
     constructor() {
       this.items = new Map(); // key -> count
     }
     add(item, count = 1) { ... }
     remove(item, count = 1) { ... }
     merge(other) { ... }  // Returns new multiset
   }
   ```

3. **Interned Strings**
   - String pool for rule names
   - Numeric IDs for fast comparison

---

## Rust/Zig Rewrite Strategy

### Why Rust/Zig?

1. **Performance**: 10-100x faster than JavaScript
2. **Memory Safety**: No GC pauses, predictable performance
3. **WASM Target**: Can compile to WebAssembly for browser
4. **FFI**: Can be called from JavaScript/Python/etc.

### Core Components to Rewrite

1. **Data Structures** (Priority: HIGH)
   - Node (AST)
   - Sequent
   - Proof Tree
   - Multiset

2. **Algorithms** (Priority: HIGH)
   - Unification (MGU)
   - Substitution
   - Proof search

3. **Parser** (Priority: MEDIUM)
   - Can use existing Rust parser generators
   - pest, nom, lalrpop

### Rust Architecture Sketch

```rust
// Core types
pub struct Node {
    id: RuleId,
    children: Vec<Node>,
}

pub struct Sequent {
    persistent: Context,
    linear: Multiset<Resource>,
    succedent: Node,
    focus: Option<Focus>,
}

pub struct ProofTree {
    conclusion: Sequent,
    rule: Option<RuleId>,
    premises: Vec<ProofTree>,
}

// Traits
pub trait Substitutable {
    fn substitute(&self, theta: &Substitution) -> Self;
}

pub trait Unifiable {
    fn unify(&self, other: &Self) -> Option<Substitution>;
}

// WASM exports
#[wasm_bindgen]
pub fn parse(input: &str) -> JsValue { ... }

#[wasm_bindgen]
pub fn prove(goal: JsValue) -> JsValue { ... }
```

### Migration Strategy

1. **Start with Core Algorithms**
   - Implement unification in Rust
   - Compile to WASM
   - Call from JavaScript via wasm-bindgen

2. **Benchmark Hybrid**
   - Compare JS-only vs JS+Rust-WASM
   - Identify if WASM overhead is acceptable

3. **Gradually Move More to Rust**
   - Data structures
   - Proof search
   - Parser

4. **Keep JS for UI/CLI**
   - Rust core as library
   - JS for user interaction

---

## Migration Checklists

### TypeScript Migration

- [ ] Install TypeScript and configure tsconfig.json
- [ ] Add .d.ts declarations for ll.json
- [ ] Convert lib/node.js to TypeScript
- [ ] Convert lib/sequent.js to TypeScript
- [ ] Convert lib/proofstate.js to TypeScript
- [ ] Convert lib/parser.js to TypeScript
- [ ] Update build process

### Parser Migration (Chevrotain)

- [ ] Document current Jison grammar
- [ ] Install Chevrotain
- [ ] Define token types (lexer)
- [ ] Implement parser rules
- [ ] Create AST builder visitor
- [ ] Write parser tests
- [ ] Benchmark comparison
- [ ] Remove Jison dependency

### Test Migration (Vitest)

- [ ] Install Vitest (currently using Node's built-in test runner)
- [x] ~~Migrate existing Mocha tests~~ → Using Node test runner
- [x] ~~Add tests for proofstate.js~~ → v2 tests in tests/v2/
- [x] ~~Add tests for sequent.js~~ → tests/v2/sequent.test.js
- [x] ~~Add tests for node.js~~ → tests/v2/ast.test.js
- [x] ~~Add tests for parser~~ → tests/v2/calculus.test.js
- [x] ~~Add integration tests~~ → tests/e2e-solidjs.js (15 tests)
- [ ] Setup coverage reporting

### Frontend Migration (HTMX/SolidJS)

- [x] ~~Evaluate HTMX for simple UI~~ → Chose SolidJS for reactivity
- [x] ~~Prototype with HTMX + server~~ → N/A
- [x] ~~If needed, evaluate SolidJS~~ → SolidJS chosen and implemented
- [x] ~~Remove Cycle.js dependency~~ → Legacy UI deprecated, new SolidJS UI active
- [x] ~~Update webpack/bundling~~ → Now using Vite
- [x] ~~Update KaTeX to latest~~ → Using katex@0.16 via npm

---

## Refactoring TODOs

### Immediate (This Week)

- [x] ~~Fix `npm test` to actually run tests~~ → Tests now run with `npm test`
- [ ] Add basic ESLint configuration
- [ ] Document ll.json schema
- [x] ~~Remove dead/commented code~~ → Removed v1 UI code
- [ ] Fix obvious bugs marked with TODO

### Short-term (This Month)

- [x] ~~Add TypeScript with allowJs~~ → UI is TypeScript, lib stays JS
- [ ] Migrate to Vitest (still using Node test runner)
- [ ] Add basic CI with GitHub Actions
- [x] ~~Refactor global state in Calc.db~~ → v2 uses functional approach
- [ ] Add proper error types

### Medium-term (This Quarter)

- [ ] Complete TypeScript migration (v2 lib modules)
- [ ] Replace Jison with Chevrotain/tree-sitter
- [x] ~~Optimize hash computation~~ → FNV-1a via intern.js/hash.js
- [x] ~~Add comprehensive test suite~~ → 146 v2 tests, 15 e2e tests
- [x] ~~Implement benchmarks~~ → `npm run bench:compare:all`

### Long-term (This Year)

- [ ] Prototype Rust core
- [ ] WASM integration
- [x] ~~New frontend (HTMX or SolidJS)~~ → SolidJS UI complete
- [ ] Documentation site

---

## Notes & Discoveries

### 2026-02-03: v1→v2 Migration Complete

**Major milestone achieved:** The v2 rewrite is now the primary codebase.

**What was done:**

1. **UI fully migrated to v2:**
   - All pages (Sandbox, ManualProof, CalculusOverview, CalculusHealth, MetaOverview) use v2
   - `src/ui/lib/calcV2.ts` - browser wrapper for v2
   - `src/ui/lib/proofLogicV2.ts` - interactive prover using v2
   - Deleted `proofLogic.ts` (67KB of v1 code)
   - Removed v1 initialization from `index.tsx`
   - Bundle size reduced from 57KB to 43KB for main chunk

2. **CLI tools switched to v2:**
   - `calc parse` now uses v2 (was `calc-parse-v2`)
   - `calc proof` now uses v2 (was `calc-proof-v2`)
   - v1 tools renamed to `calc parse-v1`, `calc proof-v1` for benchmarking

3. **v2 architecture:**
   ```
   lib/v2/
   ├── calculus/index.js   # Load .calc/.rules files
   ├── kernel/             # Core data structures
   │   ├── ast.js          # AST operations
   │   ├── ast-hash.js     # Content-addressed hashing
   │   ├── sequent.js      # Sequent type
   │   ├── substitute.js   # Substitution
   │   └── unify.js        # Unification
   ├── prover/             # Proof search
   │   ├── focused/        # Focused prover
   │   │   ├── prover.js   # Main prover
   │   │   ├── state.js    # Proof state
   │   │   └── context.js  # Context splitting
   │   └── pt.js           # Proof trees
   ├── meta/focusing.js    # Polarity inference
   ├── browser.js          # Browser-compatible API
   └── index.js            # Main entry point
   ```

4. **What's kept as v1 (for benchmarks/comparison):**
   - `lib/*.js` files (marked @deprecated)
   - `tests/proofstate.js`, `tests/node.js`, etc.
   - `benchmarks/proof/proofs.bench.js`
   - `calc-genparser` (generates v1 parser, still used by some tests)

**Performance comparison (v1 vs v2):**
- v2 focused prover: 5-8x faster than v1 (see `npm run bench:compare:all`)
- v2 uses content-addressed hashing with FNV-1a (fast, non-crypto)
- v2 has proper structural sharing via hash-consing

### 2026-01-21: Initial Code Analysis

**Key Observations:**

1. The code is surprisingly well-structured for 9-year-old experimental code
2. Core abstractions (Node, Sequent, ProofState) are reasonable
3. Main issues are tooling age and lack of types
4. Parser dynamic generation is clever but slow

**Codebase Statistics:**
- ~2,500 lines of core library code
- 21 CLI commands
- Single ll.json config file (~600 lines)
- Minimal test coverage

**Quick Wins:**
- Fix npm test script
- Add TypeScript gradually
- Update dependencies with security issues
