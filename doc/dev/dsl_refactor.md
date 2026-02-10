---
title: Extended Celf DSL Refactor
created: 2026-02-10
modified: 2026-02-10
summary: Implementation plan for replacing ll.json with Extended Celf DSL using tree-sitter parser and family abstraction
tags: [dsl, celf, parser, tree-sitter, refactor]
status: stable
---

# DSL Refactor: Extended Celf Implementation Plan

This document outlines the implementation plan for replacing ll.json with an Extended Celf DSL.

## Progress (2026-02-02)

**Phase 1 Status:** COMPLETE
**Phase 2 Status:** COMPLETE

**Phase 1 Completed:**
- [x] Decided on tree-sitter (over Chevrotain/Ohm) — handles 1000+ nesting without stack overflow
- [x] Grammar promoted from `prototypes/` to `lib/tree-sitter-mde/grammar.js`
- [x] Nix flake with gcc, tree-sitter 0.25.10, emscripten: `flake.nix`
- [x] Verified deep nesting works (1000 levels, tree-sitter handles it)
- [x] Parse real optimism-mde files (`bin.mde`, `evm.mde`, `helper.mde`)
- [x] Added `&` (with) connective and uppercase declaration names
- [x] WASM build for browser use: `tree-sitter-mde.wasm`
- [x] Node.js bindings: `lib/celf/ts-parser.js` (async API, WASM-based)
- [x] Test suite: `tests/tree-sitter.js` (19 tests passing)

**Phase 2 Completed:**
- [x] Extended grammar with @annotation support
- [x] Annotation value types: string, identifier, boolean, precedence+associativity
- [x] AST types: `Annotation`, `StringValue`, `PrecValue`, `BoolValue`, `IdentValue`
- [x] TypeDecl and ClauseDecl now include `annotations: []` field
- [x] Test suite extended: `tests/tree-sitter.js` (30 tests passing)
- [x] Sample files: `calculus/linear-logic.calc`, `calculus/linear-logic.rules`

**Phase 3 Completed:**
- [x] ll.json generator: `lib/celf/generator.js`
- [x] **Calculus-agnostic**: No hardcoded connectives (tensor/loli/with)
- [x] Connective identification via type signatures (returnType + arity)
- [x] Dynamic pattern rendering via @ascii parsing
- [x] Extract connectives from .calc (binary operators, precedence, rendering)
- [x] Extract rules from .rules (premises, annotations)
- [x] Generate calc_structure (Formula, Structure, Sequent, etc.)
- [x] Generate rules section with correct string patterns
- [x] Test suite: `tests/ll-generation.js` (21 tests passing)
- [x] Verified Calc.init() works with generated ll.json
- [x] Verified parser (genParser) works with generated ll.json

**Phase 3.5 Completed (Family Abstraction):**
- [x] Family file format: `families/display_calculus.family`
- [x] `@extends` directive in .calc for auto-resolving family
- [x] `@role` annotations for infrastructure roles (judgment, sequent, context_concat, formula_lift, unit, variable, wildcard)
- [x] Role-based pattern generation in generator.js
- [x] Removed 37 lines of hardcoded fallbacks (deriv, seq, comma, struct, empty)
- [x] Test suite: `tests/family-generation.js` (6 tests passing)

**v2 Prover Completed (2026-02-02):**
- [x] Focused proof search (Andreoli-style) in `lib/v2/prover/focused/`
- [x] Content-addressed multisets for O(1) formula lookup
- [x] 5-8x faster than v1 (see `doc/benchmark-v2.md`)
- [x] All core ILL rules: tensor, loli, with, bang, one
- [x] Polarity/invertibility inference from rule structure
- [x] 138 tests passing

**Next (Phase 4): Full Migration to .calc/.rules**

Goal: Deprecate ll.json entirely. Load ONLY from .calc/.rules.

See detailed plan below.

---

## Current State

### Architecture
```
ll.json                    # Monolithic: types + rules + metadata + rendering
    │
    ├── lib/parser.js      # Generates Jison grammar from ll.json
    ├── lib/calc.js        # Processes ll.json, builds rule DB with integer IDs
    ├── lib/node.js        # AST with (id, vals[]) structure
    ├── lib/polarity.js    # Infers polarity from rule structure
    └── lib/proofstate.js  # Focused proof search
```

### Pain Points
1. **ll.json is verbose** - 600+ lines mixing grammar, rules, rendering, metadata
2. **No type safety** - Rules are strings, typos silently fail
3. **Jison is unmaintained** - Poor error messages, no TypeScript
4. **Hard to extend** - Adding connectives requires JSON surgery
5. **No reuse** - Can't import stdlib or share definitions

---

## CLF/Celf/Ceptre Hierarchy

Understanding the relationship between logical frameworks:

```
LF (Edinburgh Logical Framework)
 │   Dependent types: Πx:A. B
 │
 └─► LLF (Linear Logical Framework)
      │   + Linear types: A ⊸ B, A & B, ⊤
      │   + Backward chaining only
      │
      └─► CLF (Concurrent Logical Framework)
           │   + Lax monad: {A}
           │   + Synchronous connectives inside monad: ⊗, 1, !, ∃
           │   + Forward chaining (to quiescence)
           │
           ├─► Celf (Implementation)
           │     Full CLF in Standard ML
           │     #query, #exec, #trace directives
           │
           ├─► LolliMon (Simplified)
           │     Lolli + Monad
           │     No dependent types
           │
           └─► Ceptre (Game-focused)
                 + Stages (structured quiescence)
                 + Interactive mode
                 - No dependent types
                 - Simplified syntax
```

**CALC v2 Target:** Ceptre-level features, with path to full CLF.

See `dev/research/clf-celf-ceptre.md` for detailed analysis.

---

## Target State

### Three-File Architecture
```
linear-logic.calc          # Types, connectives with @annotations
linear-logic.rules         # Inference rules (Celf + @pretty)
lib/*.mde                  # Pure Celf stdlib (optimism-mde compatible)
```

### Syntax Summary

**.calc files** (Extended Celf):
```celf
formula : type.

tensor : formula -> formula -> formula
  @ascii "_ * _"
  @latex "#1 \\otimes #2"
  @prec 60 left
  @polarity positive.
```

**.rules files** (Celf + annotations):
```celf
deriv : sequent -> type.

tensor_l : deriv (seq (comma G (struct (tensor A B))) C)
        <- deriv (seq (comma (comma G (struct A)) (struct B)) C)
  @pretty "*L"
  @invertible true.
```

**.mde files** (Pure Celf - optimism-mde compatible):
```celf
bin : type.
e : bin.
i : bin -> bin.

plus : bin -> bin -> bin -> type.
plus/z1 : plus e e e.
plus/s1 : plus (o M) (o N) (o R) <- plus M N R.
```

---

## Design Questions to Resolve

### 1. First-Order vs Higher-Order Abstract Syntax
**Question:** Support HOAS like `forall : (formula -> formula) -> formula`?

**Options:**
- **A) First-order only** - Explicit variable names, simpler to implement
- **B) Full HOAS** - True to LF, requires scope/binding machinery

**Recommendation:** Start with first-order. The current ll.json uses explicit `Atterm` for bound variables. HOAS can be added later.

### 2. Annotation Syntax
**Question:** Exact syntax for `@annotations`?

**Decided:**
- `@key value` - Simple value (identifier, string, number)
- `@key "string"` - String literal
- `@key n assoc` - Precedence with associativity

### 3. ll.json Generation vs Direct Use
**Question:** Generate ll.json for backwards compatibility or refactor consumers?

**Recommendation:**
- Phase 1: Generate ll.json from .calc/.rules
- Phase 2: Refactor consumers to use new AST directly
- This allows incremental migration without breaking the UI

### 4. FFI Hook Point
**Question:** Where does FFI dispatch integrate with proof search?

**Answer:** In `lib/prover.js` during rule application. When a rule is marked `@ffi`, check if arguments are ground, dispatch to JS function, unify result.

---

## Implementation Phases

### Phase 0: Baseline Tests (Before Refactoring)
**Goal:** Capture current behavior to verify refactor doesn't break anything.

**Tasks:**
- [ ] Test current parser output for all ll.json constructs
- [ ] Test proof search for known theorems (from tests/proofstate.js)
- [ ] Test rendering (ASCII, LaTeX) for all connectives
- [ ] Test polarity inference
- [ ] Snapshot ll.json-derived Calc.db for comparison

**Files:**
```
tests/parser-snapshot.js    # Parser output tests
tests/calc-db-snapshot.js   # Calc.db structure tests
tests/rendering-snapshot.js # toString() output tests
```

### Phase 1: Tree-sitter Parser for Pure Celf
**Goal:** Parse optimism-mde style .mde files.
**Status:** COMPLETE

**Grammar:** `lib/tree-sitter-mde/grammar.js`

Supports:
- Type declarations: `name: type.`
- Arrow types: `foo: a -> b -> c.`
- Linear implication: `foo: a -o b.`
- Forward rules: `rule: a -o { b }.`
- Tensor: `foo: a * b * c.`
- With (additive conjunction): `foo: a & b.`
- Bang: `foo: !a.`
- Application: `foo: f x y.`
- Backward chaining: `rule: head <- premise1 <- premise2.`
- Comments: `% comment`

**Tests:** All passing
- [x] Parse deeply nested expressions (1000+ levels)
- [x] Parse optimism-mde/lib/bin.mde
- [x] Parse optimism-mde/lib/evm.mde
- [x] Parse optimism-mde/lib/helper.mde
- [x] AST conversion to Ohm-compatible format

**Files:**
```
lib/tree-sitter-mde/
├── grammar.js              # Tree-sitter grammar (source)
├── tree-sitter.json        # Tree-sitter config
├── tree-sitter-mde.wasm    # WASM parser (generated, gitignored)
├── mde.so                  # Native parser (generated, gitignored)
├── src/                    # Generated C code (gitignored)
└── test/
    ├── test.mde            # Basic test cases
    └── deep-test.mde       # Deep nesting test

lib/celf/
├── parser.js               # Ohm-based parser (original)
├── ts-parser.js            # Tree-sitter parser (new, async API)
└── grammar.ohm             # Ohm grammar (original)
```

**npm scripts:**
```bash
npm run build:ts       # Generate + build native parser
npm run build:ts:wasm  # Build WASM parser
npm run test:ts        # Run tree-sitter tests
```

### Phase 2: Extended Celf (@annotations)
**Goal:** Parse .calc files with annotations.
**Status:** COMPLETE

**Grammar Extension (tree-sitter):**
```javascript
// In lib/tree-sitter-mde/grammar.js
annotation_block: $ => repeat1($.annotation),

annotation: $ => seq(
  '@',
  field('key', $.identifier),
  field('value', optional($.annotation_value))
),

annotation_value: $ => choice(
  $.string_literal,
  $.prec_value,      // number with optional associativity
  $.identifier,
  $.bool_literal,
),

prec_value: $ => seq($.number, optional($.associativity)),
associativity: $ => choice('left', 'right', 'none'),
string_literal: $ => seq('"', /[^"]*/, '"'),
bool_literal: $ => choice('true', 'false'),
```

**AST Node Types:**
```javascript
AST.Annotation(key, value)        // { type: 'Annotation', key, value }
AST.StringValue(value)            // { type: 'StringValue', value }
AST.PrecValue(precedence, assoc)  // { type: 'PrecValue', precedence, associativity }
AST.BoolValue(value)              // { type: 'BoolValue', value: true/false }
AST.IdentValue(name)              // { type: 'IdentValue', name }
```

**Annotation Schema:**
| Key | Values | Used In |
|-----|--------|---------|
| `@ascii` | string | .calc |
| `@latex` | string | .calc |
| `@isabelle` | string | .calc |
| `@prec` | number [assoc] | .calc |
| `@polarity` | positive/negative | .calc |
| `@category` | multiplicative/additive/exponential | .calc |
| `@dual` | ident | .calc |
| `@shallow` | true/false | .calc |
| `@pretty` | string | .rules |
| `@invertible` | true/false | .rules |
| `@direction` | forward/backward | .rules |
| `@ffi` | ident | .calc |
| `@mode` | mode-spec | .calc |

**Tests:** ✓ All passing (30 tests in tests/tree-sitter.js)
- [x] Parse annotation blocks
- [x] Extract annotations into structured metadata
- [x] Handle missing annotations gracefully (annotations: [])
- [x] Parse .calc-style connective definitions
- [x] Parse .rules-style rule definitions
- [x] Backwards compatible with pure Celf (.mde files)

**Sample Files:**
- `calculus/linear-logic.calc` - Connective definitions with annotations
- `calculus/linear-logic.rules` - Inference rules with annotations

### Phase 3: ll.json Generation
**Goal:** Generate ll.json from .calc + .rules for backwards compatibility.
**Status:** COMPLETE

**Key Property:** The generator is **calculus-agnostic**. It derives all connective information from:
- Type signatures (e.g., `formula -> formula -> formula` indicates binary formula connective)
- `@ascii` patterns (e.g., `"_ * _"` specifies how to render the connective)

No hardcoded logic for specific connectives (tensor, loli, with, etc.). Any calculus definable in the Extended Celf format can be processed.

**Transformation:**
```
.calc types/connectives  →  calc_structure (via type signature analysis)
.calc @annotations       →  ascii/latex/precedence fields (via @ascii patterns)
.rules definitions       →  rules section (via connective registry lookup)
Inferred from structure  →  calc_structure_rules_meta
```

**API:**
```javascript
const generator = require('./lib/celf/generator');

// Generate ll.json programmatically
const llJson = await generator.generate(
  './calculus/linear-logic.calc',
  './calculus/linear-logic.rules',
  { calcName: 'LinearLogic' }
);

// Or generate and write to file
await generator.generateToFile(calcPath, rulesPath, outputPath);

// Helpers
generator.extractConnectives(calcAst)  // Get connective metadata with returnType
generator.extractRules(rulesAst)       // Get rule metadata
generator.termToPattern(term, conn)    // Convert Celf term using connective registry
generator.parseAsciiPattern(ascii)     // Parse "_ * _" into {arity, parts}
generator.applyPattern(pattern, args)  // Apply pattern to arguments
generator.getReturnType(typeExpr)      // Get return type from arrow chain
```

**Tests:** ✓ All passing (21 tests in tests/ll-generation.js)
- [x] Generate ll.json from linear-logic.calc + linear-logic.rules
- [x] Extract binary operators from type signatures (not hardcoded)
- [x] Generate rule categories (RuleZer, RuleU, RuleBin)
- [x] Generate sequent patterns (e.g., "?X, -- : F?A * F?B |- -- : F?C")
- [x] Verify Calc.init() works with generated ll.json
- [x] Verify genParser() works with generated ll.json
- [x] Custom connectives use their @ascii patterns dynamically
- [x] Formula vs structure connectives distinguished by return type

**Files:**
```
lib/celf/generator.js       # .calc → ll.json generator (calculus-agnostic)
tests/ll-generation.js      # Generation tests (21 tests)
```

### Phase 4: Complete Migration to .calc/.rules (REVISED 2026-02-02)

**Goal:** Deprecate ll.json entirely. Load ONLY from .calc/.rules format.

**Rationale:** We don't want backward compatibility with ll.json. The v2 system
already loads from .calc/.rules via `lib/v2/calculus/index.js`.

#### Phase 4A: Complete v2 ILL Prover ✓

**Gap Analysis (ll.json vs v2):**

| Feature | ll.json | v2 | Status |
|---------|---------|-----|--------|
| Tensor ⊗ | ✓ | ✓ | ✓ Done |
| Loli ⊸ | ✓ | ✓ | ✓ Done |
| With & | ✓ | ✓ | ✓ Done |
| Bang ! | ✓ | ✓ | ✓ Done + tested |
| One I | ✓ | ✓ | ✓ Done |
| Top ⊤ | - | - | NOT IMPLEMENTED (low priority) |
| Monad {A} | experimental | - | NOT IMPLEMENTED (see TODO.md) |
| Lax | experimental | - | NOT IMPLEMENTED (see TODO.md) |
| Forall | experimental | - | NOT IMPLEMENTED |
| Absorption | ✓ | spec'd | Rule defined but not integrated in prover |
| Copy | ✓ | spec'd | Rule defined but not integrated in prover |

**Tasks completed (2026-02-02):**
- [x] Add bang tests to focused-prover.test.js
- [x] Fixed requiresEmptyDelta constraint for promotion rule
- [x] Fixed delta tracking for nested rule applications

**Limitations:**
- `!A ⊢ !A` requires absorption+copy integration (tracked in tests as expected failure)
- Full cartesian context support deferred to future work

#### Phase 4B: Migrate Consumers ✓

**Current v1 consumers that need migration:**
- `lib/calc.js` → ✓ marked deprecated
- `lib/parser.js` → ✓ marked deprecated
- `lib/proofstate.js` → ✓ marked deprecated
- `libexec/*` CLI tools → ✓ v2 versions created (calc-proof-v2, calc-parse-v2)
- `src/ui/` SolidJS UI → pending (requires node.js compatibility layer)

**New v2 API (lib/v2/index.js):**
```javascript
const v2 = require('./lib/v2');

// High-level API
const result = await v2.proveString('P, P -o Q |- Q');
const formula = await v2.parseFormula('A -o B');
const sequent = await v2.parseSequent('A, B |- C');
const ascii = await v2.render(formula, 'ascii');
```

**New CLI tools:**
- `calc-proof-v2` - 5-8x faster proof search
- `calc-parse-v2` - Parse formulas and sequents

#### Phase 4C: Remove ll.json (PENDING)

Blocked by UI migration. Cannot remove ll.json until:
- [ ] Migrate UI to v2 prover
- [ ] Delete ll.json from repository
- [ ] Remove lib/llt_compiler.js (Jison generator)
- [ ] Remove v1 tests that depend on ll.json
- [ ] Update all imports to use v2 exclusively

### Phase 5: FFI Support

**Goal:** Support `@ffi` and `@mode` for computational predicates.

**Syntax:**
```celf
plus : bin -> bin -> bin -> type
  @ffi "arithmetic.plus"
  @mode + + -
  @verify true.
```

**Implementation:**
1. Register FFI functions at startup
2. During proof search, check if goal matches FFI predicate
3. Verify mode (inputs are ground)
4. Call JS function
5. Unify result

**Files:**
```
lib/ffi/registry.js         # FFI function registry
lib/ffi/arithmetic.js       # Built-in arithmetic
lib/celf/mode-check.js      # Mode checking
```

**Tests:**
- [ ] Parse @ffi and @mode annotations
- [ ] Mode checking rejects non-ground inputs
- [ ] FFI dispatch computes correct results
- [ ] Verify option catches errors

### Phase 6: Stdlib and Full Migration

**Goal:** Create reusable stdlib, complete migration.

**Stdlib:**
```
lib/celf/stdlib/
├── base.mde          # nat, bin, bool
├── arithmetic.mde    # plus, mul, etc.
└── linear-logic.calc # ILL connectives
```

**Migration:**
- [ ] Port lib/bin.mde from optimism-mde
- [ ] Create full Celf-compatible stdlib
- [ ] Verify all tests pass with v2 exclusively
- [ ] Archive or remove all v1 code

---

## Future Work (Deferred to TODO.md)

The following advanced features are documented in `dev/TODO.md` with LOW priority:

- **Lax Monad + Forward Chaining** - CLF foundation (HIGH in TODO.md, but after v2 migration)
- **Ceptre Stages** - Structured quiescence for multi-phase computation
- **Dependent Types (Π, ∃)** - Full CLF/LF compatibility
- **Top (⊤)** - Additive truth connective

See `dev/research/clf-celf-ceptre.md` for research background.

---

## Current File Structure

```
/home/mhhf/src/calc/
├── lib/
│   ├── tree-sitter-mde/       # Tree-sitter grammar (Phases 1+2 - COMPLETE)
│   │   ├── grammar.js         # Source grammar (with @annotations)
│   │   ├── tree-sitter.json   # Config
│   │   ├── tree-sitter-mde.wasm  # WASM (gitignored)
│   │   ├── mde.so             # Native (gitignored)
│   │   ├── src/               # Generated C (gitignored)
│   │   └── test/              # Test files
│   │
│   ├── celf/                  # Celf parsers and tools
│   │   ├── grammar.ohm        # Ohm grammar (original)
│   │   ├── parser.js          # Ohm parser (sync, stack overflow on deep)
│   │   ├── ts-parser.js       # Tree-sitter parser (async, handles deep, annotations)
│   │   └── generator.js       # ll.json generator from .calc/.rules (Phase 3)
│   │
│   ├── calc.js                # Calculus database
│   ├── parser.js              # Jison generation from ll.json
│   ├── node.js                # AST nodes
│   └── ...
│
├── calculus/                  # Extended Celf definitions (Phase 2)
│   ├── linear-logic.calc      # Connectives with @annotations
│   └── linear-logic.rules     # Inference rules with @annotations
│
├── tests/
│   ├── tree-sitter.js         # Tree-sitter parser tests (30 tests)
│   ├── ll-generation.js       # ll.json generation tests (12 tests) (Phase 3)
│   ├── celf-parser.js         # Ohm parser tests
│   └── ...
│
├── flake.nix                  # Nix devshell (tree-sitter, gcc, emscripten)
├── .envrc                     # direnv integration
└── ll.json                    # Current calculus definition
```

## Target File Structure (After Full Refactor)

```
/home/mhhf/src/calc/
├── calculus/                  # Calculus definitions (note: 'calc' is taken by CLI)
│   ├── linear-logic.calc      # Connectives with @annotations ✓
│   ├── linear-logic.rules     # Inference rules ✓
│   └── stdlib/
│       ├── base.mde           # nat, bin, bool
│       └── arithmetic.mde     # plus, mul, etc.
│
├── lib/
│   ├── tree-sitter-mde/       # Unified grammar (pure Celf + @annotations) ✓
│   │
│   ├── celf/
│   │   ├── ts-parser.js       # Tree-sitter parser (with annotations) ✓
│   │   └── generator.js       # .calc → ll.json (Phase 3)
│   │
│   ├── ffi/                   # FFI support (Phase 5)
│   │   ├── registry.js
│   │   └── arithmetic.js
│   │
│   ├── calculus.js            # Unified API (Phase 4)
│   └── ...
│
├── ll.json                    # GENERATED from .calc/.rules (Phase 3)
│
└── tests/
    ├── tree-sitter.js         # Parser tests ✓
    ├── ll-generation.js       # Phase 3
    └── ffi.js                 # Phase 5
```

---

## Risks and Mitigations

### Risk 1: Parser complexity
**Mitigation:** Start with pure Celf subset. Ohm handles left-recursion and precedence well.

### Risk 2: Breaking proof search
**Mitigation:** Extensive baseline tests before refactoring. Dual loading path during migration.

### Risk 3: Scope creep
**Mitigation:** Each phase is independently valuable. Can stop after any phase.

---

## Dependencies

**Nix devshell (flake.nix):**
- tree-sitter CLI 0.25.10
- gcc (for native parser compilation)
- emscripten (for WASM builds)
- Node.js 22

**npm packages:**
- `web-tree-sitter@0.25.10` - WASM runtime for Node.js and browser
- `ohm-js` - Alternative parser (original, has stack overflow on deep nesting)

---

## Success Criteria

1. **Phase 1 Complete:** ✓ Can parse optimism-mde files (bin.mde, evm.mde, helper.mde)
2. **Phase 2 Complete:** ✓ Can parse .calc files with @annotations
3. **Phase 3 Complete:** ✓ Can generate ll.json from .calc/.rules
4. **Phase 4:** Proof search works without ll.json
5. **Phase 5:** `plus(2,3,X)` computes X=5 via FFI

---

## Open Questions for User

1. **HOAS Priority:** Is higher-order abstract syntax (for quantifier binding) needed soon, or can we defer?

2. **Backwards Compatibility:** Keep ll.json as generated artifact indefinitely, or remove after migration?

3. **Stdlib Location:** Should stdlib live in this repo or separate (optimism-mde style)?

---

## Parser Decision: Tree-sitter

**Decision Date:** 2026-02-01

**Chosen:** Tree-sitter over Ohm/Chevrotain

**Rationale:**
- **No stack overflow**: GLR algorithm uses explicit parse stack, not call stack
- **Tested**: 1000-level nesting in 0.002s without issues
- **Zig bindings**: Official `tree-sitter-zig` bindings for future porting
- **Unified**: Same parser technology for meta (`.calc`/`.rules`) and object (`.ll`) languages
- **Editor support**: Bonus syntax highlighting, code folding, incremental parsing

**Prototype:** `prototypes/tree-sitter-mde/`

**Development environment:** `flake.nix` provides all build tools. Use `direnv allow` to auto-load.

**Two-Layer Architecture:**
```
┌─────────────────────────────────────────────────────────┐
│  Bootstrap Parser (tree-sitter grammar for .calc/.rules)│
│  - Parses calculus definitions                          │
│  - Hardcoded, checked into repo                         │
└─────────────────────────────────────────────────────────┘
                        │
                        ▼ generates
┌─────────────────────────────────────────────────────────┐
│  Object Parser (tree-sitter grammar for .ll files)      │
│  - Generated from calculus definitions                  │
│  - Different .calc/.rules → different object grammars   │
└─────────────────────────────────────────────────────────┘
```

---

## Phase 3.5: Family Abstraction & Multi-Type DC (2026-02-02)

### Files Created

```
families/
├── display_calculus.family   # Base family with labeled connective
└── lnl.family                # LNL extension with F ⊣ G adjunction

calculus/
├── linear-logic-minimal.calc # Simple ILL using display_calculus
└── lnl-linear-logic.calc     # ILL using LNL family (multi-type)
```

### Multi-Type DC Design

**Mode System:**
Types can be annotated with `@mode` to indicate structural properties:
- `@mode linear` - No contraction, no weakening (default)
- `@mode cartesian` - Contraction + weakening allowed

**Bridge Connectives:**
The F ⊣ G adjunction connects modes:
```celf
functor_g: formula -> formula
  @role bridge
  @adjoint functor_f
  @from_mode linear
  @to_mode cartesian.

functor_f: formula -> formula
  @role bridge
  @adjoint functor_g
  @from_mode cartesian
  @to_mode linear.
```

**LNL Sequent:**
```celf
lnl_seq: cart_structure -> structure -> formula -> lnl_sequent
  @ascii "_ ; _ |- -- : _"
  @shape lnl.
```

### Labeled vs Anonymous Proof Terms

Two ways to put formulas in context:
```celf
% Anonymous (wildcard proof term)
struct: formula -> structure
  @ascii "-- : _"
  @role formula_lift.

% Labeled (tracks proof term variable)
labeled: term -> formula -> structure
  @ascii "_ : _"
  @role labeled_formula.
```

---

## Family Abstraction Analysis (2026-02-02)

### Q1: Can we tell from display-calculus.family that something IS a display calculus?

**Answer: NO, not fully.**

The family file provides *structural infrastructure* but does NOT encode:
- Display postulates (structural permutation rules)
- Belnap's C1-C8 conditions for cut elimination
- Structure visibility (which connective "displays" which)

To verify something is a display calculus, we'd need to:
1. Check the .rules file has proper display postulates
2. Verify C1-C8 conditions hold (complex meta-property)

**What the family DOES indicate:**
- Presence of @role annotations suggests display-style architecture
- `@role sequent` with `@shape one_sided` indicates one-sided sequent form
- But a purely syntactic one-sided sequent calculus isn't necessarily a display calculus

### Q2: Is display_calculus.family general enough for multi-type display calculi?

**Answer: NO, current family has limitations:**

| Feature | Current | Multi-Type DC Needs |
|---------|---------|---------------------|
| Structure types | 1 (`structure`) | Multiple (linear_ctx, persistent_ctx) |
| Formula types | 1 (`formula`) | Multiple (linear_formula, intuitionistic_formula) |
| Bridge connectives | None | F ⊣ G adjunction (`!` decomposes into two) |
| Mode annotations | None | Types parameterized by mode preorder |

**For LNL (Linear/Non-Linear) Logic:**
Current family would need extension:
```celf
% Additional types for LNL
intuitionistic_formula: type @layer formula @mode persistent.
linear_formula: type @layer formula @mode linear.

% Bridge adjunction
F_functor: intuitionistic_formula -> linear_formula  % Left adjoint
G_functor: linear_formula -> intuitionistic_formula  % Right adjoint (!)
```

### Q3: Proof term support (named vs anonymous)?

**Answer: Currently ANONYMOUS only.**

```celf
% Current: struct takes only formula
struct: formula -> structure
  @role formula_lift.

% For named proof terms, would need:
labeled: term -> formula -> structure
  @role labeled_formula.
```

The `var: string -> term` and `any: term` exist, but `struct` only lifts formulas, not labeled formulas.

**To support named proof terms:**
1. Add `labeled: term -> formula -> structure` connective
2. Modify proof search to track variable assignments
3. Proof trees would output actual proof terms, not just `--`

### Roadmap for Multi-Type Support

1. **Phase A**: Add `@mode` annotation to types
2. **Phase B**: Allow multiple types per layer (`@layer formula @mode linear`)
3. **Phase C**: Add bridge connective support in generator
4. **Phase D**: Verify LNL as test case

See: dev/research/multi-type-display-calculus.md for detailed research
