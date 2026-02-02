# TODO

Outstanding tasks for the CALC project.

---

## HIGH Priority Research

### Extended Celf DSL
**Priority:** HIGH
**Status:** PHASE 1 IN PROGRESS — Tree-sitter prototype working

**Current State (2026-02-01):**
- Tree-sitter chosen over Chevrotain/Ohm (handles 1000+ nesting, has Zig bindings)
- Prototype grammar at `prototypes/tree-sitter-mde/grammar.js`
- Nix flake created with gcc, tree-sitter, emscripten
- Deep nesting test passed (1000 levels in 0.002s)

**Next Steps:**
1. Parse real optimism-mde files (`/home/mhhf/src/optimism-mde/lib/bin.mde`, `evm.mde`)
2. Refine grammar for full Celf compatibility
3. Test WASM build for browser

Use **Extended Celf syntax** as the specification language, adding `@annotations` for metadata.

**Decision: Three-file architecture**

| File | Syntax | Purpose |
|------|--------|---------|
| `.calc` | Extended Celf + `@annotations` | Connectives + metadata (polarity, latex, dual) |
| `.rules` | Celf + `@pretty` | Inference rules (proof search hints) |
| `.mde` | **Pure Celf** (unchanged) | Stdlib + programs (optimism-mde compatible) |

**Key insight**: Only `.calc` needs extensions. Stdlib and programs are pure Celf.

**Example `.calc` syntax:**
```celf
tensor : formula -> formula -> formula
  @ascii "_ * _"
  @latex "#1 \\otimes #2"
  @prec 60 left
  @polarity positive
  @category multiplicative
  @dual par
  @interp "Simultaneous availability: both A and B".
```

**Example `.rules` syntax (Celf with @pretty):**
```celf
tensor_l : deriv (seq (comma G (struct (tensor A B))) C)
        <- deriv (seq (comma (comma G (struct A)) (struct B)) C)
  @pretty "*L"
  @invertible true.
```

**Critical extensions:**

1. **Literal syntax** — Types can define literal patterns:
   ```celf
   bin : type
     @literal decimal "[0-9]+"       % 42 → i(o(i(o(i(e)))))
     @literal hex "0x[0-9a-f]+"      % 0xff → ...
     @desugar decimal bin_from_decimal.
   ```

2. **FFI predicates** — Escape proof search for computation:
   ```celf
   plus : bin -> bin -> bin -> type
     @ffi arithmetic.plus            % JS function
     @mode + + -                     % input input output
     @verify true                    % check result
     @fallback axioms.               % if mode doesn't match
   ```

**Implementation tasks:**
- [x] Prototype tree-sitter parser for .mde files (`prototypes/tree-sitter-mde/`)
- [x] Verify deep nesting works (1000+ levels, 0.002s)
- [ ] Implement full Celf grammar in tree-sitter
- [ ] Add `@literal` and `@desugar` for syntax sugar
- [ ] Add `@ffi` and `@mode` for FFI predicates
- [ ] Implement FFI dispatch in proof search
- [ ] Port optimism-mde/lib to verify pure Celf works
- [ ] Generate ll.json from .calc for backwards compatibility

**FFI considerations:**
- Mode checking: `+` = ground input, `-` = computed output
- Verification: optionally check FFI results
- Fallback: use axioms when FFI mode doesn't match
- See: dev/research/ffi-logics.md (detailed design)

**Deferred research questions (for later):**
- [ ] Dependent types for rule typing (LF-style)
- [ ] Cut elimination via adequacy
- [ ] Twelf/Celf export for metatheory verification

**See:** dev/research/typed-dsl-logical-framework.md (comprehensive design)

**Parser Framework Research**

Need a modern, maintainable parser framework for:
1. Parsing ASCII syntax of the calculus (formulas, sequents, rules)
2. Parsing the .mde DSL to compile to internal calculus representation
3. Potentially generating parsers from ll.json grammar specs

**Requirements:**
- Modern JavaScript/TypeScript with good DX (error messages, debugging)
- Methodology portable to Zig (similar parsing approach)
- Easy to iterate on grammar during research phase
- Good error recovery and reporting for user-facing parsing

**Frameworks to evaluate:**

1. **Chevrotain** (JS)
   - Parser combinator style, no code generation
   - Pure JS, good error messages, fast
   - Grammar defined in code (not separate file)
   - Downside: grammar-in-code harder to port directly

**Decision: tree-sitter for both meta and object language**

Tree-sitter is the clear winner after prototyping both tree-sitter and Chevrotain:

| Criteria | Tree-sitter | Chevrotain | Ohm |
|----------|-------------|------------|-----|
| Deep nesting (1000+) | ✅ 0.002s | ❌ Stack overflow | ❌ Stack overflow |
| Algorithm | GLR (explicit stack) | LL(k) (call stack) | PEG (call stack) |
| Zig porting | Official bindings | Manual rewrite | Manual rewrite |
| Build step | Required (C) | None | None |
| Editor support | Native | None | None |

**Why tree-sitter:**
- **No stack overflow**: GLR uses explicit parse stack, handles 1000+ nesting levels
- **Zig bindings**: Official `tree-sitter-zig` bindings exist
- **Unified architecture**: Same parser tech for meta (`.calc`/`.rules`) and object (`.ll`) languages
- **Editor integration**: Bonus syntax highlighting, code folding, etc.

**Prototype location:** `prototypes/tree-sitter-mde/`

**Development environment:** `flake.nix` provides gcc, tree-sitter CLI, emscripten for WASM builds. Use `direnv allow` to auto-load.

**See:** dev/research/typed-dsl-logical-framework.md for full comparison

---

### Higher Order Linear Types:
Priority: HIGH

I'm curious about linear types that can wrap linear types.
Right now we only have the posibility of doing:

```
bla: type.
omg: bla.
omg2: bla.

foo: bla -> ltype.
```

but i'd like something like:

```
bar: ltype -> ltype
```

We would need to research that in depth if its possible and how easy and 'far away' it is from the constructive LL we already implemented.


### Pacioli Grading Semiring
**Priority:** HIGH

Can the Pacioli group P be a well-behaved grading semiring for graded linear logic?

- [ ] Define multiplication: [a//b] · [c//d] = ???
- [ ] Verify semiring laws
- [ ] Define □_{[x//y]} A in the logic
- [ ] What does grade polymorphism mean for T-accounts?

---

### Fibration Semantics for Ownership
**Priority:** HIGH

What is the precise fibration structure for ownership?

- [ ] Base category: Principals with speaks-for morphisms?
- [ ] Fibers: SMC of resources? Linear categories?
- [ ] Transfer as reindexing: what properties?
- [ ] Connection to dependent linear types?

---

### Debt as Session Protocol
**Priority:** HIGH

Define debt relationships as session types:

- [ ] debt_type = &{ pay: ..., renegotiate: ..., default: ... }
- [ ] Settlement as channel closure
- [ ] Default handling via exception types?
- [ ] Multi-party debt (syndicated loans)?

---

### MPST-Based Authorization Design
**Priority:** HIGH

Apply MPST methodology to CALC:

- [ ] Define atomic swap as global type
- [ ] Implement projection algorithm
- [ ] Prove deadlock freedom for swap
- [ ] Generate local rules automatically

---

## MEDIUM Priority

### Advanced Optimizations
**Priority:** MEDIUM
**Status:** Content-addressing complete, profiling infrastructure in place

Deferred optimizations documented in **dev/optimization_strategies.md**.

Use `CALC_PROFILE=1` to identify bottlenecks before implementing:
- Constructor Index (O(1) identity lookup)
- Proof Memoization (polynomial complexity)
- Near-Linear Unification (Martelli-Montanari)
- Explicit Substitutions (lazy evaluation)
- Persistent Data Structures
- Arena Allocation (for Zig port)

---

### Conditional execution
**Priority:** MEDIUM

research BDI framework and logic - behaviour desire intention and how it might fit into our system, create a research document for bdi

### Conditional execution
**Priority:** MEDIUM

if a condition is reached (time is up, price is hit, etc) we need to triger a transition. how to model it?

see financial-primitives

### Price Oracles
**Priority:** MEDIUM

- internal price oracles
- external price oracles

see financial-primitives

### Explicit time
**Priority:** MEDIUM
Some things - like future or option contracts need explicit time - since they are expiering. We need to research how to model that well with calc

see financial-primitives.md

### Generalize Multi-Type Display Calculus
**Priority:** MEDIUM

CALC implements Benton's LNL via persistent_ctx + linear_ctx. For multimodalities, graded types, and agents, we need a generic multi-type framework.

**Current State:**
- LNL hardcoded (persistent_ctx, linear_ctx, Bang_L special handling)
- Works correctly for ILL — this is our case study

**Goal:**
- Generalize to support arbitrary types and bridge rules
- Keep LNL as instantiation proving the framework works
- Enable: ownership modalities, consensus algorithms, graded types

**Consensus modalities to support (not just simple ownership):**
- Single authority: `[Alice] A`
- Multi-signature: `[Alice ∧ Bob] A`
- k-of-n threshold: `[2-of-{A,B,C}] A`
- Weighted voting: `[Alice:0.3, Bob:0.7] A`
- Proof of Work: `[PoW(nonce, difficulty)] A`
- Proof of Stake: `[Stake(Alice, amount)] A`

**Options evaluated (see research doc):**
1. **Multi-type DC** (Greco & Palmigiano) — PRIMARY CHOICE
2. **Labelled sequents** — backup if MTDC insufficient
3. **Pfenning's adjoint logic** — good fit, modes as partial order

**Advanced systems evaluated:**
- Deep Inference: LOW relevance (structural flexibility, not our need)
- Cyclic Proofs: MEDIUM-HIGH for future (if we need recursive contracts/fixpoints)
- Proof Nets: LOW (bad for multimodal logics)

See: dev/research/multi-type-display-calculus.md (revised)

---

### Core/Calculus Separation (Revised)
**Priority:** MEDIUM

Two completely separate provers, minimal interaction for now.

**GenericProver** (lib/core/prover.js):
- Just tries all rules (including structural rules)
- NO explicit split enumeration (structural rules handle it implicitly)
- Supports ordered logic, linear logic, etc. - no assumptions
- Loop detection needed (A,B => B,A => A,B)
- Can verify proof trees from specialized provers

**ILLProver** (lib/provers/ill/):
- Current focused prover, unchanged
- Produces proof trees that GenericProver can verify
- No oracle/FFI for now - just two separate implementations

- [ ] Implement GenericProver (dumb rule enumeration)
- [ ] Add loop detection / visited state tracking
- [ ] Keep ILLProver as-is
- [ ] Add `verify(proofTree)` method to GenericProver

---

### Code Investigation
**Priority:** MEDIUM

Understand what's logic-specific vs generic in current code.

- [ ] **substitute.js:10 - Formula_Forall check**
  - Purpose: Avoid substituting bound variables in ∀
  - Is this strictly necessary? Where is it used?
  - Can it be made generic (any "binder" rule)?

- [ ] **calc.js:214 - Structure_Term_Formula check**
  - Purpose: Marks nodes as "term type" for rendering
  - Can be generalized: look for rules with Formula child type?

- [ ] **compare.js:23-27 - Commented references**
  - Were Structure_Term_Formula / Structure_Focused_Term_Formula comparisons
  - Investigate git history - why were they added/removed?
  - Probably debug/experimental code

- [ ] **sequent.js - hardcoded structure names**
  - Why config is better: allows different calculi with different structure names
  - But maybe YAGNI - keep hardcoded until we have second calculus

---

### Partial Settlement with Arithmetic FFI
**Priority:** MEDIUM

From linear-negation-debt research:
- [ ] Partial settlement with arithmetic FFI

---

## Backlog

### Display Calculus Completeness
**Priority:** DEPRIORITIZED (decided to stay with ILL fragment)

- [ ] ~~Add Par (⅋) - multiplicative disjunction (dual of ⊗)~~
- [ ] ~~Add Plus (+) - additive disjunction (dual of &)~~
- [ ] ~~Add Why-not (?) - dual exponential (dual of !)~~
- [ ] ~~Add units: ⊥ (bottom), 0 (zero), ⊤ (top), 1 (one)~~

Decision: Stay with intuitionistic linear logic (ILL) fragment. Full classical linear logic duals not needed for current goals.

### Architecture (Core/Calculus Separation)
**Priority:** MEDIUM

- [ ] Identify code that is "Gentzen machinery" vs "Linear Logic specific"
- [ ] Design clean interface between core engine and calculus plugins
- [ ] Extract core into `lib/core/` directory
- [ ] Support compile-time and runtime calculus loading

### Code Quality
**Priority:** LOW

- [ ] Add ESLint configuration
- [ ] Add TypeScript (gradual)
- [ ] Set up CI with GitHub Actions

### Parser
**Priority:** LOW

- [ ] Document current Jison grammar
- [ ] Evaluate Chevrotain migration
- [ ] Benchmark parser performance

### Cyclic Proofs for Fixpoints
**Priority:** LOW

- [ ] Cyclic proofs for fixpoints — deeper study needed

### Coalgebras over Comonads
**Priority:** LOW

- [ ] Coalgebras over comonads — deeper study needed

### Extensions
**Priority:** LOW (future)

- [ ] Design semiring-parameterized quantities
- [ ] Design ownership modalities
- [ ] Prototype real-number arithmetic

### Documentation
**Priority:** LOW

- [ ] Write significance hypothesis document (dev/HYPOTHESIS.md)
- [ ] Design minimal litmus test example (token transfer encoding)

---

## Deprioritized

### Study Proof Nets
**Priority:** VERY LOW

Proof nets are hard for multimodalities. Keep as long-term research interest only.

- [ ] Understand proof nets vs proof trees
- [ ] Study the "bureaucracy" problem they solve
- [ ] Understand correctness criteria

### Display proofs as PDF/HTML
**Priority:** VERY LOW

Already have HTML UI with multiple views. PDF export can wait.

### Isabelle Export
**Priority:** ULTRA LOW

- [ ] Consider Isabelle export for formal verification of cut elimination
- [ ] Research Isabelle/Isar proof format
- [ ] Would provide machine-checked guarantee but not needed for current goals
