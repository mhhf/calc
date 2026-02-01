# TODO

Outstanding tasks for the CALC project.

---

## HIGH Priority Research

### Content-Addressed Formulas, Terms, and Sequents
**Priority:** HIGH

Design a content-addressing scheme where identical logical objects have identical addresses, enabling efficient equality, caching, and deduplication.

**Goals:**
- Same formula/term/sequent → same address (structural identity)
- Efficient to compute (ideally O(1) for equality after initial hash)
- Support for alpha-equivalence (identical up to bound variable renaming)
- Enable proof sharing, memoization, and deduplication

**Approaches to research:**

1. **Hash Consing** — Classic technique from functional programming / SAT solvers
   - Structurally equal terms share the same memory cell
   - Equality becomes pointer equality (O(1))
   - Used in: BDDs, SAT/SMT solvers, some theorem provers
   - Key paper: Filliatre & Conchon, "Type-Safe Modular Hash-Consing"

2. **Merkle-style Hashing** — Content-addressable trees
   - Each node's hash = hash(constructor, child_hashes)
   - Roots identify entire subtrees
   - Used in: Git, IPFS, Unison language
   - Benefit: Incremental updates, proof of structure

3. **De Bruijn Indices** — For alpha-equivalence
   - Replace variable names with binding depth
   - `λx.λy.x` becomes `λ.λ.1` (index 1 = one binder up)
   - Ensures alpha-equivalent terms are syntactically identical
   - Then apply hash consing on de Bruijn form

4. **Locally Nameless Representation** — Hybrid approach
   - Bound variables: de Bruijn indices
   - Free variables: names
   - Good for substitution and alpha-equivalence

**Implementation considerations:**
- [ ] Where to address: AST nodes? Sequents? Proof trees?
- [ ] Incremental addressing for edits
- [ ] Weak references for garbage collection of unused structures
- [ ] Thread-safety for concurrent proof search

**CRITICAL: Performance requirement**
- Tree construction and comparison happens constantly during proof search
- Must be **O(1)** for equality checking after initial construction
- **Cryptographic hashing is too slow** — computing hash at every node is expensive
- Consider alternatives:
  - **Interning with integer IDs**: Each unique structure gets a unique integer. Equality = integer comparison (O(1))
  - **Hash consing with weak hash tables**: Hash once on construction, then pointer equality
  - **Structural sharing**: Reuse subtrees, compare by reference
  - **Lazy hashing**: Only compute hash when needed (serialization, dedup), not for equality
- The key insight: we need **identity**, not necessarily **content hash**
  - For equality: pointer/ID comparison suffices
  - For serialization/dedup: can compute hash lazily

**Zig export compatibility**
- Future goal: Export provers to Zig for large proof search performance
- JavaScript is too slow for exhaustive search on complex proofs
- Design decisions now must consider Zig portability:
  - Data structures should map cleanly to Zig (arena allocators, slices)
  - Avoid JS-specific patterns (closures as data, prototype chains)
  - Integer IDs for interning work well in Zig (simple array indexing)
  - Consider: define core data structures in a language-agnostic way
  - Potential path: JS prototype → Zig rewrite of hot paths → FFI or full port

**Potential benefits for CALC:**
- Fast sequent comparison in proof search (memoization)
- Proof sharing across similar goals
- Caching of completed subproofs
- Efficient serialization (refer by hash)

**References:**
- Filliatre & Conchon, "Type-Safe Modular Hash-Consing" (ML Workshop 2006)
- Unison language: content-addressed code
- IPFS: content-addressed file systems
- Nominal techniques: Pitts, "Nominal Sets"

---

### Extended Celf DSL
**Priority:** HIGH
**Status:** DESIGN COMPLETE — Ready for implementation

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
- [ ] Implement Celf parser with Ohm (types, constructors, rules)
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

**Decision: Ohm for prototyping, tree-sitter for production**

2. **Ohm** (JS) ← PRIMARY for prototyping
   - PEG-based, separate grammar file
   - Excellent visualization/debugging tools
   - Clean separation: grammar vs semantics
   - Good for prototyping and iteration

3. **tree-sitter** (C with bindings) ← FUTURE for editor support
   - Industrial-strength incremental parsing
   - Used by editors (VSCode, Neovim)
   - Zig bindings exist for future port

**Migration path:**
```
Jison (current) → Ohm (prototype) → tree-sitter (production/editors)
                                  → Zig hand-written RD (performance)
```

**See:** dev/research/typed-dsl-logical-framework.md for full comparison

---

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
