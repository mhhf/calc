---
title: "Higher-Order Extensions Overview — Polymorphism, Dependent Types, Fixed Points, Multimodality"
created: 2026-03-02
modified: 2026-03-03
summary: "Master plan for extending CALC beyond first-order ILL: what to implement, what to defer, how features interrelate across four orthogonal axes"
tags: [dependent-types, polymorphism, fixed-points, muMALL, QTT, adjoint-logic, MTDC, lax-monad, clf, graded-types, higher-order, linear-logic, proof-theory, architecture, roadmap]
type: design
status: researching
priority: 9
cluster: Theory
depends_on: []
required_by: [TODO_0006, TODO_0009, TODO_0010, TODO_0011, TODO_0012, TODO_0013, TODO_0014, TODO_0063]
starred: true
---

# Higher-Order Extensions Overview

Master plan for extending CALC beyond first-order ILL. This document synthesizes TODOs 0006, 0008, 0009, 0010, 0011, 0012, 0013, 0014, 0033, 0034, 0063, and research documents RES_0008, 0024, 0031, 0042, 0050, 0051, 0052, 0056 plus external literature on CLF, muMALL, QTT, adjoint logic, and MTDC.

**Core question:** What does CALC need, what can it get, and in what order?

---

## 1. The Four Orthogonal Axes

Extensions to ILL fall along four **mostly independent** axes. Different use cases draw from different axes. You can mix and match — you don't need to go all the way on every axis.

### Axis 1 — Term-Level Type Discipline

What the type system can express about terms.

| Level | What | Cost | Example |
|---|---|---|---|
| 0 | Untyped terms, tag matching | **Done** | CALC now |
| 1 | Sort system + arity checking | ~500 LOC | Prevent `plus(token, eth)` |
| 2 | Polymorphism ∀X.A | ~300 LOC | `∀X. list(X) ⊸ list(X)` |
| 3 | Indexed families (GADT-like) | ~800 LOC | `vec(N) : nat → type` |
| 4 | Dependent types Π x:A.B | ~2200 LOC | `Π n:nat. vec(n)` |
| 5 | Full QTT (Π + semiring grades) | ~3000+ LOC | Idris 2 territory |

Each level strictly contains all levels below. ∀X.A is a degenerate Π where the domain is a universe. But polymorphism is **dramatically** simpler to implement.

### Axis 2 — Structural/Modal Expressiveness

How many modes of truth the logic distinguishes.

| Level | What | Cost | Example |
|---|---|---|---|
| 0 | Single ! (linear + cartesian) | **Done** | CALC now |
| 1 | Indexed modalities (syntax wrappers) | ~600 LOC | `[Alice] token`, `[]_5 eth` |
| 2 | Subexponentials !_a | ~800 LOC | Nigam-Miller indexed ! |
| 3 | Adjoint logic (modes + shifts) | ~1500 LOC | ↑, ↓ between modes |
| 4 | Full MTDC (multi-type + bridge rules) | ~1000 LOC | Greco-Palmigiano framework |

MTDC, adjoint logic, and subexponentials are different frameworks for similar phenomena. MTDC is the most general proof-theoretic container; adjoint logic is the most elegant; subexponentials are the simplest to implement.

### Axis 3 — Fixed-Point Expressiveness

Recursion, (co)induction, and reasoning about infinite behavior.

| Level | What | Cost | Example |
|---|---|---|---|
| 0 | No fixed points (clause recursion only) | **Done** | CALC now |
| 1 | Tabling/memoization | ~80 LOC | Loop = success/failure by polarity |
| 2 | Cyclic proofs + GTC | ~200 LOC | Back-edges in proof trees |
| 3 | muMALL (μ/ν connectives) | ~400 LOC | `Nat = μX. 1 ⊕ X` |

With arithmetic (CALC has it via FFI): cyclic proofs ≡ explicit induction (Berardi-Tatsuta 2017). muMALL strictly subsumes exponentials: `!A = νX. A & X`.

### Axis 4 — Forward/Backward Integration

How the two proof search modes interact.

| Level | What | Cost | Example |
|---|---|---|---|
| 0 | Separate systems | **Done** | CALC now |
| 1 | Predicate stratification | ~100 LOC | Ad-hoc rule ordering |
| 2 | Lax monad {A} | ~500 LOC | Backward → forward mode switch |
| 3 | Nested modes (SLS-style) | ~1000 LOC | Forward within backward within forward |

The lax monad {A} is the sweet spot — it bridges the two halves of CALC and subsumes simple stages.

---

## 2. Subsumption and Orthogonality

### What Makes What Unnecessary

```
muMALL (μ/ν) ⊃ exponentials (!/?)          Baelde 2012
Π types      ⊃ ∀X.A (polymorphism)         trivially
QTT {0,1,ω}  ⊃ ILL {1,ω}                  CALC's lin/pers = QTT fragment
MTDC          ⊃ adjoint logic               instance
adjoint logic ⊃ subexponentials             instance
lax monad {A} ⊃ simple stages              backward sequences phases
cyclic proofs ≡ explicit induction (+arith)  Berardi-Tatsuta 2017
```

### What Is Orthogonal (Need Both Independently)

```
muMALL        ⊥  lax monad       (fixed points ≠ mode switching)
muMALL        ⊥  dependent types (recursion ≠ indexing)
MTDC          ⊥  muMALL          (modes ≠ fixed points)
polymorphism  ⊥  fixed points    (parametric ≠ recursive types)
lax monad     ⊥  dependent types (CLF has both independently)
```

### Partial Overlaps

- **muMALL partially overlaps stages**: `νX. (body ⊗ X)` models cyclic phases, but complex data-passing sequencing is more natural with {A}
- **QTT partially overlaps MTDC**: grades capture linear/affine/unrestricted but not principal-indexed ownership
- **Adjoint logic partially captures {!, {A}}**: bang = F(U(A)), monad = ↑(↓A), but no fixed points or polymorphism

### The Expressiveness Graph

See [RES_0073](../research/0073_higher-order-expressiveness-survey.md) for the full Mermaid diagram.

Key reading: an arrow A → B means "A subsumes B." No path = orthogonal. The four axes are mostly independent — the graph is wide, not tall.

---

## 3. What Each TODO Needs

| TODO | Description | Axis | Minimum Extension | Recommended | Phase |
|---|---|---|---|---|---|
| TODO_0063 | arrlit compact arrays | Eng. | None | None (∀ later) | 1 |
| TODO_0006 | Lax monad {A} | 4 | {A} connective + mode switch | Option B (500 LOC) | 2 |
| TODO_0010 | Ceptre stages | 4 | Subsumed by TODO_0006 | Defer to monad | 2 |
| TODO_0011 | CLF dependent types | 1 | Stages 1-3 (sorts → indexed) | Defer Stage 4 (Π) | 3-4 |
| TODO_0012 | Proper MTDC | 2 | Type-uniform sequents | Bridge rules | 3 |
| TODO_0013 | Generalized MTDC | 2 | Extends TODO_0012 | After TODO_0012 | 3+ |
| TODO_0014 | Multimodal impl. | 2 | [P]A syntax wrappers | Indexed modalities | 2 |
| TODO_0033 | Modality parser | Eng. | Supports TODO_0014 | With TODO_0014 | 2 |
| TODO_0034 | Multimodal examples | Test | Requires TODO_0014 | After TODO_0014 | 2+ |
| TODO_0008 | Metaproofs | 3+meta | P-invariants + ranking | Tabling → cyclic | 1-3 |
| TODO_0009 | Induction/coinduction | 3 | Tabling | Tabling → cyclic → muMALL | 1-3 |

---

## 4. Feasibility Assessment

### TODO_0064.Class_A — Easy (weeks, well-understood, bounded)

**A1. Simple Polymorphism ∀X.A** (~300 LOC)
- Add universal type quantification. Erasure-based (no runtime cost).
- Extend parser: `forall X. ...` at type level (reuse existing ∀ for terms)
- Extend unify.js: type variables unify like metavariables
- Extend Store: quantifier tag for type-level ∀ (may reuse existing)
- Focusing: ∀ is negative (asynchronous) — invertible on right
- Well-understood theory: Girard 1987, Wadler 1993, Barber 1996 (DILL)
- **Payoff:** Generic rules, reusable libraries, type-safe containers
- **Not blocking:** TODO_0063 works without it (bin is universal)

**A2. Tabling** (~80 LOC)
- State memoization in `explore()`: `Map<stateHash, subtree>`
- Loop on inductive predicate = failure; on coinductive = success
- Builds on existing content-addressed hashing (O(1) state equality)
- **Payoff:** Performance (100× reported by QCHR), coinductive reasoning foundation
- Already identified in TODO_0009.Phase_1

**A3. Predicate Stratification** (~100 LOC)
- Mark rule subsets, execute in topological order
- Simple dependency analysis on predicate names
- **Payoff:** Basic staging without new proof theory
- Subsumed by lax monad (TODO_0006) — stopgap only

**A4. arrlit** (~500+ LOC, 8 stages)
- Already fully designed in TODO_0063
- Pure engineering: Store infrastructure, FFI, parser, EVM rules
- No type theory changes required

### TODO_0064.Class_B — Medium (months, established theory, careful design)

**B1. Lax Monad {A}** (~500 LOC) — TODO_0006.Option_B
- New connective in `ill.calc` and `ill.rules`
- Mode-switch rule in L3 `focused.js`: goal `{S}` → forward engine
- Bridge: sequent representation ↔ multiset state conversion
- Forward engine returns proof tree node verifiable by L1 kernel
- **Key challenge:** Linear context transfer between prover and engine
- **Payoff:** Mixed-mode programs, principled staging, formal forward/backward bridge
- Subsumes TODO_0010 (stages), partially subsumes TODO_0009 (phases)
- Theory: CLF (Watkins 2004), LolliMon (Lopez 2005), SLS (Simmons 2012)

**B2. Cyclic Proofs** (~200 LOC) — TODO_0009.Phase_3
- Add `back-edge(target)` node type to proof trees
- GTC checker: validate infinite paths have infinite progress
- Manual proof UI: "close cycle" action
- **Payoff:** Induction without invariant guessing, automation-friendly
- Builds on existing cycle detection in symexec
- Theory: Doumane 2017, E-Cyclist (Stratulat 2021)

**B3. Sort System + Arity Checking** (~500 LOC) — TODO_0011.Stages_1-2
- Multi-level sort system (extend PRED_BOUNDARY to N levels)
- Predicate signature declarations: expected argument count + sorts
- Type-check at rule compilation time (compile.js)
- **Payoff:** Catches malformed rules before execution

**B4. Indexed Modalities** (~600 LOC) — TODO_0014 + TODO_0033
- Parser: `[P] A`, `⟨P⟩ A`, `[]_r A` syntax
- Store: new tags for ownership/authorization/grade wrappers
- Content-addressed hashing incorporates index
- Forward engine: matching respects modality wrappers
- **Payoff:** Principal-indexed ownership, authorization logic, graded resources

### TODO_0064.Class_C — Hard (months-to-year, significant design)

**C1. muMALL (μ/ν connectives)** (~400 LOC) — TODO_0009.Phase_4
- Extend formula grammar with `μX.B(X)` and `νX.B(X)`
- Parser: new syntax for fixed-point formulas
- Store: new tags for μ/ν (dynamic tag range)
- Rule interpreter: μ-left (induction), ν-right (coinduction)
- Focusing: μ is positive, ν is negative (extend focusing.js)
- **Hard part:** The invariant problem makes automated proof search undecidable
- **Payoff:** Inductive data types, coinductive processes, temporal reasoning, exponentials-as-sugar
- Theory: Baelde 2012, Doumane 2017

**C2. Proper MTDC** (~1000 LOC) — TODO_0012
- Type-uniform sequents (not just formulas but structural terms)
- Generic bridge rules between types
- Belnap's conditions for generic cut elimination
- **Hard part:** Designing the bridge rule language, maintaining cut-elim
- **Payoff:** Principled multimodal, modular extension
- Theory: Greco-Palmigiano 2023, Benton 1994

**C3. Adjoint Logic** (~1500 LOC) — TODO_0006.Option_C
- Mode system with adjunctions between modes
- Shift operators ↑ (upshift) and ↓ (downshift)
- Unifies !, {A}, and future modalities under one mechanism
- **Hard part:** Mode theory infrastructure, interaction with forward engine
- **Payoff:** Most general framework for Axis 2, future-proofs design
- Theory: Pruiksma et al. 2018, Licata-Shulman 2016

**C4. Indexed Families** (~800 LOC) — TODO_0011.Stage_3
- Predicates with index constraints (GADT-like)
- `step : state → state → pred` with sort constraints
- Type refinement without full Π
- Requires sort system (B3) as prerequisite

### TODO_0064.Class_D — Very Hard (year+, research-level)

**D1. Full Dependent Types Π** (~2200 LOC) — TODO_0011.Stage_4
- Kind system, hereditary substitution, bidirectional type checking
- Higher-order pattern unification (Miller's fragment — decidable, linear time)
- Type reconstruction (implicit argument inference)
- **When needed:** If CALC becomes a general logical framework (like Twelf)
- **Not needed now:** Ceptre proves practical linear logic programming works without Π
- Theory: LF (Harper et al. 1993), CLF (Watkins et al. 2004)

**D2. Full QTT** (~3000+ LOC on top of Π)
- Semiring grades on every context variable
- Grade checking in every type rule
- Requires Π types first
- **When needed:** If formal resource certificates with dependent-type guarantees are required
- Theory: Atkey 2018, McBride 2016, Idris 2

### TODO_0064.Class_E — Not Feasible / Not Worth It

**E1. HVM-style proof nets** — Completely different execution model (graph reduction vs multiset rewriting). Would require ground-up rewrite. Not an extension of CALC.

**E2. Universe polymorphism** — Infinite type hierarchy (Type₀ : Type₁ : Type₂ : ...). Way too much complexity for CALC's domain. Only relevant for proof assistants.

**E3. Full Higher-Kinded Types (System Fω)** — Type-level computation, kind polymorphism. CALC doesn't need type-level abstraction at this level. ∀X.A suffices.

**E4. Full CLF reimplementation** — Building Celf in JavaScript. Celf exists; CALC's value is the forward engine + exhaustive exploration, not being another CLF.

---

## 5. Recommended Phased Roadmap

### Phase 1 — Immediate Value (1-2 months, ~980 LOC)

| Item | LOC | Value | Axis |
|---|---|---|---|
| arrlit (TODO_0063) | ~500 | Very High (performance) | Eng. |
| Tabling (TODO_0009.P1) | ~80 | High (perf + coinduction) | 3 |
| ∀X.A polymorphism | ~300 | Medium (generic rules) | 1 |
| Pred. stratification | ~100 | Low (stopgap for stages) | 4 |

**Rationale:** All items are well-understood, bounded, independent. arrlit is the highest-impact engineering task. Tabling gives immediate speedup and lays the foundation for Phase 2. Polymorphism opens generic programming. Stratification is a cheap staging stopgap.

**Dependencies:** None — all items are independent of each other and of later phases.

### Phase 2 — Core Extensions (3-6 months, ~1800 LOC)

| Item | LOC | Value | Axis |
|---|---|---|---|
| Lax monad {A} (TODO_0006.B) | ~500 | Very High (unifies system) | 4 |
| Cyclic proofs (TODO_0009.P3) | ~200 | High (induction) | 3 |
| Sort system + arity (TODO_0011.S1-2) | ~500 | Medium (error catching) | 1 |
| Indexed modalities (TODO_0014) | ~600 | Medium (ownership) | 2 |

**Rationale:** The lax monad is the most architecturally significant extension — it bridges CALC's two halves and subsumes staging. Cyclic proofs build on Phase 1's tabling. Sort system catches errors. Indexed modalities enable the financial logic vision.

**Dependencies:** Cyclic proofs benefit from tabling (Phase 1). Lax monad is independent. Sort system is independent. Indexed modalities require parser work (TODO_0033).

### Phase 3 — Power Features (6-12 months, ~2200 LOC)

| Item | LOC | Value | Axis |
|---|---|---|---|
| muMALL μ/ν (TODO_0009.P4) | ~400 | Very High (full fixed points) | 3 |
| MTDC or adjoint logic | ~1000-1500 | High (proper multimodal) | 2 |
| Indexed families (TODO_0011.S3) | ~800 | Medium (type safety) | 1 |

**Rationale:** muMALL is the biggest single capability upgrade — it gives inductive/coinductive reasoning, data types, temporal properties, and makes exponentials derivable. MTDC/adjoint logic properly grounds the multimodal system. Indexed families approach dependent types without full Π.

**Dependencies:** muMALL benefits from cyclic proofs (Phase 2). MTDC/adjoint benefits from indexed modalities (Phase 2). Indexed families require sort system (Phase 2).

**Choice point:** MTDC vs adjoint logic. Recommendation: adjoint logic if the goal is principled mode theory; MTDC if the goal is generic cut elimination. Adjoint logic has better interaction with the lax monad (monad = ↑↓).

### Phase 4 — Research Horizon (12+ months)

| Item | LOC | Value | Axis |
|---|---|---|---|
| Dependent types Π (TODO_0011.S4) | ~2200 | High (if framework) | 1 |
| QTT grading | ~3000+ | Medium | 1+2 |
| Metaproof framework | ~1000+ | High (verification) | All |

**Rationale:** Only pursue if CALC evolves toward being a general logical framework (like Twelf) or needs formal resource certificates. The metaproof framework combines all axes: muMALL for induction, {A} for mode switching, possibly Π for metatheoretic statements.

**Decision criterion for Π:** Implement when CALC needs to answer "is this user-defined logic sound?" Until then, the prover kernel (L1) + runtime verification suffices.

---

## 6. What CALC Would Look Like After Each Phase

### After Phase 1: "ILL with generic arrays and fast exploration"

```ill
% Polymorphic list operations
forall X. reverse : list(X) -o list(X) -o list(X).

% Compact bytecode (1 line, not 764)
bytecode 0x6080604052...

% Tabling: memoized exploration (100x faster for cyclic programs)
% Predicate stratification: basic rule ordering
```

### After Phase 2: "Mixed-mode ILL with ownership and induction"

```ill
% Backward computes gas, forward executes
main : init -o { optimal_gas(G) * execute(G) }.

% Lax monad sequences phases
phase1 : init -o { ... setup rules ... }.
phase2 : setup_done(X) -o { ... execute rules ... }.

% Ownership modalities
[Alice] token(eth, 100) * (Alice says transfer(Bob, 50))
  -o { [Alice] token(eth, 50) * [Bob] token(eth, 50) }.

% Cyclic proof closes back-edge for induction
% "every execution eventually reaches STOP"
```

### After Phase 3: "muMALL with proper multimodal"

```ill
% Inductive natural numbers
type nat = mu X. 1 + X.

% Coinductive streams (infinite token payments)
type stream(A) = nu X. A * X.

% Temporal safety: "invariant holds at all future states"
safety(P) = nu X. P & AX(X).

% Adjoint-logic shift for mode switching
enter_forward : ↓(compute_result) -o { forward_rules }.
```

### After Phase 4: "Dependently-typed linear logical framework"

```ill
% Type families indexed by terms
type vec : nat -> type -> type.
vnil : vec 0 A.
vcons : forall n:nat. A -> vec n A -> vec (s n) A.

% Judgments as types (metatheoretic statements)
type preserves : rule -> property -> type.
% ... a term of type "preserves r p" is a proof that rule r preserves property p
```

---

## 7. Key Design Decisions

### 7.1 MTDC vs Adjoint Logic vs Subexponentials

Three frameworks for Axis 2. Recommendation: **adjoint logic**.

**Critical clarification:** Adjoint logic and MTDC are at **different levels of abstraction**, NOT competing alternatives:
- **Adjoint logic** = a specific logic with concrete connectives (↑, ↓, shifts). You implement this.
- **MTDC** = a meta-framework for designing calculi with guaranteed properties (cut elimination). You use this on paper to verify your design.

Analogy: adjoint logic = "implement quicksort", MTDC = "use master theorem to verify complexity."

When this document says "CALC almost has MTDC," it means: CALC's two-zone context (linear D; cartesian G) with different structural rules per zone IS a 2-type display calculus. MTDC theory tells us this design gives cut elimination. But MTDC isn't something you "implement" as an alternative to adjoint logic.

**The actual implementation decision** is adjoint logic vs subexponentials:
- Subexponentials are simplest (just index !) but limited to exponential-style modalities.
- **Adjoint logic** hits the sweet spot: provides concrete mode theory (adjunctions), has clean interaction with the lax monad (monad = ↑↓), has a well-studied proof theory (Pruiksma et al.), and naturally extends to multimodal.

If adjoint logic is chosen, it subsumes: !, {A}, and modal operators — all as instances of shift operators between modes. This means TODO_0006 (lax monad), TODO_0012 (MTDC), TODO_0013 (generalized MTDC), and TODO_0014 (multimodal) all become instances of one unified mechanism.

**Caveat:** Adjoint logic is ~1500 LOC and complex. The phased approach (Phase 2: lax monad first, Phase 3: generalize to adjoint) avoids over-engineering.

### 7.2 muMALL vs Cyclic Proofs

Two approaches to fixed-point reasoning. Recommendation: **both, layered**.

- Cyclic proofs are more automation-friendly (no invariant guessing)
- muMALL is more expressive (inductive data types, coinductive processes)
- With arithmetic, they have the same power for proving properties (Berardi-Tatsuta)
- But muMALL adds new FORMULAS (μ/ν types) while cyclic proofs only add new PROOF STRUCTURE

**Strategy:** Tabling (Phase 1) → cyclic proofs (Phase 2) → muMALL (Phase 3). Each builds on the previous. Tabling enables coinductive loop detection. Cyclic proofs formalize it. muMALL adds the type-level expressiveness.

### 7.3 Polymorphism vs Dependent Types

Recommendation: **polymorphism now, Π later (maybe never)**.

∀X.A is ~300 LOC with well-understood theory. Full Π is ~2200 LOC with deep implications for the entire system. The cost/benefit ratio strongly favors polymorphism:

| Feature | ∀X.A | Π x:A.B |
|---|---|---|
| Generic rules | Yes | Yes |
| Type-safe containers | Yes | Yes (+ length indexing) |
| Adequate encodings | No | Yes |
| Mechanized metatheory | No | Yes |
| Implementation cost | ~300 LOC | ~2200 LOC |
| Impact on existing code | Minimal | Pervasive |

Π is only justified when CALC needs adequacy theorems or mechanized metatheory — i.e., when it becomes a logical framework for verifying other logics, not just running programs.

### 7.4 Where Does Each Use Case Land?

```
                    Axis 1        Axis 2        Axis 3        Axis 4
                    (Types)       (Modalities)  (Fixed Pts)   (Modes)
                    ─────────     ──────────    ──────────    ──────
EVM symexec         ∀ (nice)      —             Tabling       —
Financial logic     ∀ (nice)      [P]A, []_r    —             —
Protocol verify     Indexed       [P]A          Cyclic/muMALL {A}
Metaproofs          Sort sys      —             muMALL        {A}
Game engines        ∀             —             νX            {A} (phases)
Blockchain PoS      ∀             [P]A, []_r    Cyclic        {A}
```

---

## 8. Novel Aspects (What No Other System Has)

CALC's unique position: **forward engine + exhaustive exploration + content-addressed state**. No other system combines these. This makes certain extensions uniquely interesting:

1. **muMALL + forward engine:** Inductive/coinductive types inside forward-chaining rules. No prior system does this. Execution trees become proofs in muMALL. Cycle detection in symexec = back-edges in cyclic proofs.

2. **Lax monad + exhaustive exploration:** CLF's monad uses committed choice. CALC's `explore()` uses exhaustive don't-know nondeterminism. The monadic type `{S}` would mean "all quiescent states reachable from S" — a novel notion.

3. **Content-addressed muMALL:** Fixed-point unfoldings can be memoized via hash equality. `μX.B(X)` unfolded one step = `B(μX.B(X))` — hash-consed, O(1) equality check.

4. **Graded forward chaining:** If graded modalities are added, each forward step tracks resource quantities through the grades. This has connections to Nomos (DeYoung et al., resource-aware session types) but in a forward-chaining setting.

---

## 9. Connection to External TODOs

### Subsumed by This Document

| TODO | Status | Disposition |
|---|---|---|
| TODO_0010 (Stages) | researching | Subsumed by Phase 2 (lax monad) |
| TODO_0033 (Parser) | planning | Subsumed by Phase 2 (indexed modalities) |

### Informed by This Document

| TODO | Relationship |
|---|---|
| TODO_0006 | Phase 2 — lax monad is Option B |
| TODO_0008 | Phases 1-3 — tabling → cyclic → muMALL |
| TODO_0009 | Phases 1-3 — bottom-up: tabling → cyclic → muMALL |
| TODO_0011 | Phase 2 (sorts), Phase 3 (indexed), Phase 4 (Π) |
| TODO_0012 | Phase 3 — MTDC or adjoint logic |
| TODO_0013 | Phase 3+ — extends TODO_0012 |
| TODO_0014 | Phase 2 — indexed modalities |
| TODO_0034 | Phase 2+ — examples after TODO_0014 |
| TODO_0063 | Phase 1 — arrlit is pure engineering |

---

## 10. CALC's Position in the Literature

### 10.1 The LolliMon Lineage

CALC sits in a clear lineage of linear logic programming systems:

```
Lolli (1994)           backward chaining only, higher-order terms
    ↓
LolliMon (2005)        backward outside {}, forward inside {}  ← CALC IS HERE
    ↓
SLS (Simmons 2012)     ordered linear lax logic, formalized focusing
    ↓
Ceptre (Martens 2015)  forward only, stages replace monad boundary
```

CALC's forward engine (forward.js) + backward prover (prove.js) with `-o { ... }` forward rules is exactly LolliMon's architecture. The `{ ... }` syntax IS LolliMon's monadic bracket. CALC goes beyond LolliMon in one dimension: exhaustive exploration (symexec.js) vs committed choice.

Ceptre dropped the backward-chaining outer layer entirely and replaced the monad boundary with explicit stages + quiescence detection (`qui` predicate).

### 10.2 CALC's Type Status: LF Syntax, No Checking

CALC's .ill files use LF-style declarations (`bin: type.`, `plus: bin -> bin -> bin -> type.`) but the loader reads them only for parser generation and tag assignment. No type checking occurs. CALC is "Prolog with LF syntax" — type annotations are metadata, not enforcement.

This means CALC is NOT untyped in the "no types at all" sense — it has type annotations. But it IS untyped in the "no enforcement" sense. Moving up Axis 1 (sort system → polymorphism → indexed families → Π) means progressively enforcing what's currently ornamental.

### 10.3 Definitional Equality: Why It Doesn't Matter Yet

CLF's monadic type `{S}` has specific commuting conversions (reordering independent let-bindings). CLF restricts what goes inside `{...}` to maintain decidable definitional equality. CALC already violates this — loli and oplus appear inside the monad.

This works because CALC doesn't decide proof-term equality. The forward engine operates on multiset states, not proof terms. The concern about definitional equality is proof-theoretic, not operational. It becomes relevant only if CALC implements a type checker (Phase 4).

### 10.4 Stages: Three Implementation Options

For Ceptre-like stage functionality, three options in order of theoretical cleanliness:

**Option 1: Predicate stratification (~100 LOC, Phase 1)**
Partition rules by dependency, run layers bottom-up. No new proof theory. Covers 90% of use cases with near-zero cost. Stage boundaries are implicit (determined by predicate dependencies).

**Option 2: Lax monad {A} (~500 LOC, Phase 2)**
Explicit monad connective with mode-switch rule. Gets you LolliMon's architecture as a first-class feature. Stage transitions are backward-chaining goals that trigger forward phases. Subsumes Option 1.

**Option 3: Adjoint logic modes (~800-1200 LOC, Phase 2-3)**
Each stage is a mode. Shift operators ↓/↑ control transitions. Gets you stages + composability + typed transitions. `{A}` = `↑(↓A)` falls out as a special case. Subsumes Options 1 and 2.

Recommendation: **Start with Option 2 (lax monad) but design it as a 2-mode adjoint system** so it extends to Option 3 incrementally.

### 10.4.1 Adjoint Logic, Lax Monad, and Quiescence — Why `qui` Is Unnecessary

Ceptre needs the extra-logical `qui` predicate because it dropped backward chaining entirely. In any system with backward chaining (CLF, LolliMon, CALC), quiescence detection is **implicit** — the forward engine returns when no rule matches, and backward chaining naturally sequences the phases.

**The key insight:** Ceptre's `qui` reinvents what backward chaining already provides. The lax monad `{A}` IS the stage boundary — backward chaining orchestrates, the monad exits on quiescence. Adjoint logic generalizes this: `{A} = ↑(↓A)`, where ↑ (exit mode) fires when the mode reaches quiescence via the same implicit mechanism.

| System | Needs `qui`? | Why / why not |
|--------|-------------|---------------|
| **Ceptre** | Yes | Forward-only — no natural "phase done" mechanism |
| **CLF/LolliMon** | No | Backward chaining orchestrates, monad exits on quiescence |
| **Adjoint logic** | No | ↑ shift exits mode on quiescence, generalizes monad |
| **CALC now** | No | `forward.run()` returns on quiescence, `prove.js` orchestrates |

**Concrete example — stages without `qui`:**

```ill
% Backward chaining orchestrates phases (no qui needed):
run_game :-
  phase1_result(Board),          % enters monad → forward chains → quiescence → returns
  phase2_result(Board, Score).   % enters monad again with Board from phase 1

% Phase 1 forward rules (inside monad)
setup : init -o { piece a1 * piece b2 * empty c3 }.
move  : piece X * empty Y -o { piece Y * empty X }.

% Phase 2 forward rules (inside monad)
count : piece X * score N -o { score (s N) }.
```

Quiescence = `forward.run()` returned because `findMatch()` found nothing. The backward chainer naturally continues to the next phase. No `qui`, no extra-logical injection, clean proof theory.

**What adjoint logic adds over the bare lax monad:**
- **Type safety on transitions.** Only modes with declared adjunctions can shift between each other.
- **Per-mode structural rules.** Each mode has its own discipline (linear, affine, cartesian).
- **Composability.** `↑_A(↓_B(↑_C(...)))` valid only if A ≥ B ≥ C. Ceptre stages are flat.
- **N modes, not just 2.** The lax monad has backward/forward. Adjoint logic has arbitrary modes.

**How CALC would implement this:**

```javascript
function runMode(state, mode, rules) {
  const modeRules = rules.filter(r => r.mode === mode);
  while (true) {
    const match = findMatch(state, modeRules);
    if (!match) break;  // quiescence in THIS mode → shift fires
    applyMatch(state, match);
  }
  return state;
}

// Backward chaining orchestrates (or adjoint shift rules):
let state = runMode(initialState, 'play', rules);   // ↓_play, quiescence → ↑
state = runMode(state, 'scoring', rules);             // ↓_scoring, quiescence → ↑
```

### 10.5 Lax Monad: We Have It Implicitly, Three Paths to Explicit

CALC already does what the lax monad does — the boundary is just hardcoded:

| CLF concept | CALC current | Mechanism |
|-------------|-------------|-----------|
| Backward chaining (outside `{...}`) | prove.js | Persistent predicates, clause resolution |
| Forward chaining (inside `{...}`) | forward.js | Linear matching, committed choice |
| `{A}` monad boundary | Rule compilation | `hasMonad` flag in declarations.js |
| Monadic sequencing | forward.run loop | Fire rules until quiescence |

Three paths to making it explicit:

**Path A: Minimal lax monad (~500 LOC)** — new connective + mode switch. Only two modes (backward/forward). Clean, direct CLF theory.

**Path B: 2-mode adjoint (~800 LOC)** — implement lax monad as `↑(↓A)` within a general adjoint framework. Same result, but extensible to N modes. Recommended.

**Path C: Full N-mode adjoint (~1200 LOC)** — arbitrary modes with arbitrary adjunctions. Gets stages, ownership modes, etc. Future-proof but significant upfront investment.

### 10.6 Higher-Order Linear Logic: Why HOL Didn't Develop for LL

The HOL tradition (Isabelle/HOL, HOL4) never developed for linear logic because:
1. Forum (Miller 1996) — higher-order LL programming — exists but higher-order unification is undecidable, making automated proof search impractical
2. HOAS via LF already provides clean binding representation without full higher-order quantification
3. The judgments-as-types methodology needs dependent types, not just higher-order quantification
4. Linear logic's resource discipline makes simple types (HOL's foundation) less natural than dependent types

For CALC: second-order (polymorphism) is the practical target, not higher-order.

---

## 11. Open Questions

1. **Adjoint logic vs MTDC:** Which framework for Axis 2? Adjoint logic has better mode theory; MTDC has more general proof theory. Can we implement adjoint logic AS an MTDC instance?

2. **muMALL + forward engine interaction:** When a forward rule produces `μX.B(X)`, what happens? Is the unfolding done eagerly (during rule application) or lazily (during pattern matching)? The ephemeral expansion pattern (like arrlit's `acons`/`ae`) suggests lazy unfolding.

3. **Cyclic proofs in execution trees:** CALC's `cycle` nodes are already back-edges. Can we retroactively interpret existing symexec output as cyclic pre-proofs? What is the GTC for execution trees?

4. **Grade inference:** If graded modalities are added, can grades be inferred (like Granule does) rather than annotated? For forward-chaining, the grades are implicit in the rule structure — each rule specifies exactly how many of each resource it consumes/produces.

5. **Polymorphism + forward engine:** How does ∀X.A interact with the compiled matcher? Type variables must be erasable — the compiled matcher operates on term structure, not types. This should be straightforward (ignore type variables during matching) but needs verification.

6. **The "maximum practical system":** muMALL + ∀ + {A} + adjoint modes. Has anyone studied this combination? The interaction between μ/ν and mode shifts is partially explored (Derakhshan-Pfenning 2020 on adjoint session types with recursion). The interaction between μ/ν and ∀ is classic (System Fμ).

---

## 12. References

### Survey (This Project)
- [RES_0073](../research/0073_higher-order-expressiveness-survey.md) — Full expressiveness survey (§8: sequent calc status, §9: HOL question, §10: type status)
- [RES_0071](../research/0071_dependent-types-polymorphism-linear-logic.md) — Dependent types, polymorphism, Pi types deep dive
- [RES_0072](../research/0072_muMALL-cyclic-proofs-tabling.md) — muMALL, cyclic proofs, tabling deep dive
- [RES_0074](../research/0074_qtt-graded-adjoint-subexp-mtdc.md) — QTT, graded, adjoint, MTDC (§10: grade 0, §11: def equality, §12: adjoint vs MTDC, §13: graded example)
- [RES_0008](../research/0008_clf-celf-ceptre.md) — CLF/Celf/Ceptre
- [RES_0024](../research/0024_higher-order-linear-types.md) — Higher-order linear types
- [RES_0031](../research/0031_mumall-fixed-points.md) — muMALL
- [RES_0042](../research/0042_multi-type-display-calculus.md) — MTDC
- [RES_0050](../research/0050_metaproof-verification-landscape.md) — Verification landscape
- [RES_0051](../research/0051_induction-coinduction-termination.md) — Induction/coinduction
- [RES_0052](../research/0052_clf-lax-monad-deep-study.md) — CLF lax monad
- [RES_0056](../research/0056_qtt-gap-analysis.md) — QTT gap analysis

### Key External
- Girard (1987). "Linear Logic." TCS 50. (Second-order quantifiers in sequent calculus from day one.)
- Baelde (2012). "Least and greatest fixed points in linear logic." TOCL
- Watkins et al. (2004). "CLF: A concurrent logical framework." TYPES 2003
- Lopez, Pfenning, Polakow, Watkins (2005). "Monadic concurrent linear logic programming." PPDP. (**LolliMon** — CALC's closest ancestor.)
- Miller (1996). "Forum: A multiple-conclusion specification logic." TCS 165. (Higher-order LL programming.)
- Atkey (2018). "Syntax and semantics of quantitative type theory." LICS
- Pruiksma et al. (2018). "Adjoint logic."
- Pruiksma (2024). "Adjoint Logic with Applications." PhD thesis, CMU. (ADJF focused system.)
- Greco & Palmigiano (2023). "Lattice logic properly displayed."
- Doumane (2017). PhD thesis — cyclic proofs for muMALL
- Simmons (2012). "Substructural logical specifications." PhD thesis, CMU
- Martens (2015). "Programming Interactive Worlds with Linear Logic." PhD thesis, CMU. (Ceptre.)
