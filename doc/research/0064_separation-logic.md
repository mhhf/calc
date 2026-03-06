---
title: "Separation Logic — Foundations, Landscape, and Applications to CALC"
created: 2026-02-26
modified: 2026-02-26
summary: "Deep survey of separation logic: origins, core connectives, variants, tools, and novel application directions for CALC's linear logic engine"
tags: [separation-logic, linear-logic, resource-semantics, proof-theory, verification, memory-model, symbolic-execution, forward-chaining, parallelism, concurrency]
category: "Proof Theory"
---

# Separation Logic

## 1. Origins and Motivation

**Problem:** Hoare logic cannot reason locally about heap-manipulating programs. A triple `{P} C {Q}` describes the *entire* program state — adding a pointer dereference anywhere forces the entire precondition to mention the heap.

**Solution:** John C. Reynolds (2002) and Peter O'Hearn (2001) independently developed separation logic by extending Hoare logic with connectives that express *disjoint ownership* of memory regions.

Key papers:
- Reynolds, "Separation Logic: A Logic for Shared Mutable Data Structures" (LICS 2002)
- Ishtiaq & O'Hearn, "BI as an Assertion Language for Mutable Data Structures" (POPL 2001)
- O'Hearn, Reynolds, Yang, "Local Reasoning about Programs that Alter Data Structures" (CSL 2001)

The central insight: **local reasoning** — verify each program fragment against only the memory it touches, then compose via the frame rule.

## 2. Core Connectives

### Assertion Language

Separation logic extends first-order logic with spatial connectives interpreted over heaps `h : Loc ⇀ Val` (partial functions from locations to values):

| Connective | Syntax | Semantics |
|---|---|---|
| **Emp** | `emp` | `h = ∅` (empty heap) |
| **Points-to** | `x ↦ v` | `dom(h) = {x}` and `h(x) = v` |
| **Separating conjunction** | `P * Q` | `∃h₁,h₂. h = h₁ ⊎ h₂ ∧ P(h₁) ∧ Q(h₂)` |
| **Magic wand** | `P -* Q` | `∀h'. h' # h ∧ P(h') → Q(h ∪ h')` |
| **Classical conjunction** | `P ∧ Q` | Both hold on the *same* heap |

Where `h₁ ⊎ h₂` denotes disjoint union (undefined if domains overlap) and `h' # h` means `dom(h') ∩ dom(h) = ∅`.

### Hoare Triples

The triple `{P} C {Q}` means: if `P` holds on heap `h` before `C`, then `Q` holds on the resulting heap after `C`, and `C` does not access addresses outside `dom(h)`.

This **tight interpretation** (the precondition describes exactly the footprint) enables locality.

### The Frame Rule

```
  {P} C {Q}
─────────────── (Frame)
{P * R} C {Q * R}
```

If `C` is safe and correct w.r.t. `P/Q`, then running `C` in a larger heap `P * R` preserves the frame `R` untouched. This is the engine of compositional reasoning — verify components in isolation, compose freely.

**Soundness condition:** `C` must not access resources in `R` (the "safety monotonicity" or "locality" property).

## 3. Connection to Substructural Logics

### 3.1 The Logic of Bunched Implications (BI)

Separation logic's assertion language is an instance of **BI** (O'Hearn & Pym, 1999) — a substructural logic combining:
- **Additive** (intuitionistic) conjunction `∧` and implication `→` — allow contraction and weakening
- **Multiplicative** conjunction `*` and implication `-*` — no contraction, no weakening

BI contexts are **bunched**: tree structures where each node is either additive (`;`) or multiplicative (`,`).

### 3.2 Mapping to Intuitionistic Linear Logic (ILL)

The multiplicative fragment of separation logic maps directly to ILL:

| Separation Logic | ILL | CALC |
|---|---|---|
| `P * Q` | `P ⊗ Q` (tensor) | Linear facts coexist in multiset |
| `P -* Q` | `P ⊸ Q` (lollipop) | Forward rule / loli continuation |
| `emp` | `1` (unit) | Empty linear context |
| `P ∧ Q` (shared) | `P & Q` (with) | Additive choice |
| `!P` (persistent) | `!P` (bang) | `state.persistent` |

**Key difference:** BI has *both* additive and multiplicative structural rules at once (bunched contexts), while ILL has only multiplicative by default, with `!` to recover additives. In CALC, `state.persistent` (the `!`-zone) provides the additive/shared layer.

### 3.3 Why This Matters for CALC

CALC already implements the core algebraic structure of separation logic:
- **No aliasing by construction** — linear facts exist exactly once (no contraction)
- **Frame rule is structural** — forward rules consume/produce specific facts; everything else is automatically preserved
- **Points-to as linear facts** — `mem M`, `stack N V`, `code PC Op` are resource propositions

CALC doesn't need to *add* separation logic — it already *is* a separation logic engine, operating on a richer set of connectives.

## 4. Variants and Extensions

### 4.1 Concurrent Separation Logic (CSL)

O'Hearn (2007) extended SL to shared-memory concurrency:

```
{P₁} C₁ {Q₁}    {P₂} C₂ {Q₂}
─────────────────────────────── (Par)
  {P₁ * P₂} C₁ ∥ C₂ {Q₁ * Q₂}
```

If `P₁` and `P₂` describe **disjoint** resources, the threads can run in parallel with no interference. Shared state is mediated through **resource invariants** on critical sections.

**Relevance to CALC:** This is the theoretical basis for parallel symexec (see §7.1).

### 4.2 Iris — Higher-Order Concurrent Separation Logic

Iris (Jung et al., 2015–present) is a framework for building separation logics, implemented in Coq:
- **Ghost state:** arbitrary partial commutative monoids (cameras) for abstract resources
- **Invariants:** propositions that hold across steps, accessed via "opening" protocols
- **Later modality ▷:** step-indexing for recursive/impredicative reasoning
- **Prophecy variables:** reason about future nondeterministic choices

Iris subsumes CSL, RGSep, CAP, TaDA, and many other program logics.

### 4.3 Intuitionistic vs. Classical Separation Logic

- **Intuitionistic SL** (default): monotone — `P` in heap `h` implies `P` in any `h' ⊇ h`. Garbage collection is implicit.
- **Classical SL**: exact — `P` holds in *precisely* the described heap. Used for "tight" specifications.

CALC operates in the classical/exact mode: a linear fact that isn't consumed persists exactly, and consumed facts vanish exactly.

### 4.4 Quantitative Separation Logic

Batz et al. (2019) extend SL with quantitative reasoning — expectations, probabilities, costs attached to heap assertions. Relevant for CALC's potential gas cost analysis in EVM verification.

### 4.5 Incorrectness Separation Logic

O'Hearn (2020) inverts the frame rule for **bug finding** rather than verification:

```
[P] C [Q]   means   Q is reachable from P
```

If `[P] C [Q]` and `Q` contains a memory error, then the bug is *real* (not a false positive). This is the theoretical basis for Facebook Infer's Pulse analyzer.

**Relevance to CALC:** Symexec already explores reachable states — incorrectness logic could formalize our leaf classification (STOP, REVERT, stuck).

## 5. Tools and Implementations

| Tool | Approach | Domain |
|---|---|---|
| **Facebook Infer** | Bi-abduction, compositional | C/C++/Java/Objective-C memory safety |
| **VeriFast** | Symbolic execution with SL | C/Java verification |
| **Viper** | Intermediate verification language | Permission-based SL |
| **Smallfoot** | Symbolic execution with SL | Shape analysis |
| **GRASShopper** | SL + SMT | Heap data structures |
| **RustBelt** | Iris + lifetime logic | Rust type system soundness |
| **VST** | Iris-style in Coq | C programs (CompCert) |
| **Gillian** | Parametric SL engine | Multi-language (JS, C, WISL) |

### Bi-Abduction (Infer)

Calcagno et al. (2011): given `H`, find `?anti-frame` and `?frame` such that:
```
H * ?anti-frame ⊢ P * ?frame
```
This enables **compositional analysis**: analyze each function once, then combine summaries. Infer uses this to scale to millions of lines of code.

### Frame Inference

Given a precondition `P * R` and a specification `{P} C {Q}`, infer the frame `R` that passes through unchanged. Berdine et al.'s symbolic execution computes this automatically.

## 6. Separation Logic for Smart Contracts

Several projects apply SL to smart contract verification:
- **VerX** (Permenev et al., 2020): temporal safety for Ethereum contracts
- **Certora Prover**: SL-inspired modular reasoning for Solidity
- **Move language** (Diem/Aptos): resource types directly encode separation — owning a `Coin<T>` is a linear capability

The EVM's memory model is naturally spatial: storage slots, memory bytes, and stack positions are disjoint resources. CALC already models this via linear facts.

## 7. Novel Applications to CALC

### 7.1 Parallel Symbolic Execution via Resource Separation

**Core idea:** CSL's parallel rule says disjoint-resource computations can run in parallel. CALC's symexec explores a tree of states. If we can identify when two branches touch *disjoint linear facts*, they can be explored concurrently.

**Mechanism:**

1. **Footprint analysis** — for each compiled rule, statically compute its *footprint*: the set of predicate tags it reads/writes. This is already available from `rule.antecedent` and `rule.consequent`.

2. **Independence detection** — at a branch point, check if the matches in different children have overlapping footprints. E.g., an arithmetic rule touching `stack` and `gas` is independent of a memory rule touching `mem` and `memsize`.

3. **Parallel exploration** — independent subtrees can be explored in parallel (separate workers or async tasks). The frame rule guarantees correctness: each subtree's mutations are confined to its footprint.

**Where in CALC:** `symexec.js:exploreNode()` — when `findAllMatches` returns multiple matches, partition them by footprint overlap before spawning children.

**Concrete example:** In EVM symexec, after JUMPI creates two branches (true/false), both branches often start with independent opcode sequences (one does PUSH+ADD, the other does PUSH+MUL). These touch disjoint stack regions and could be explored in parallel.

### 7.2 Compositional Rule Summaries (Bi-Abduction for Forward Rules)

**Core idea:** Instead of re-executing common rule sequences, precompute *summaries* — separation logic triples for rule chains.

**Mechanism:**

1. **Rule summary:** A compiled rule `R` with antecedent `A` and consequent `C` already *is* a separation logic triple: `{A} R {C}`. The frame (everything not in A or C) is implicit.

2. **Chain summaries:** If rule `R₁` produces facts that `R₂` consumes, compose: `{A₁} R₁;R₂ {C₂ * (C₁ \ A₂)}`. This is essentially forward-chaining frame inference.

3. **Memoized subtrees:** When symexec revisits a state pattern (not exact state, but matching *shape*), apply the summary instead of re-exploring.

**Where in CALC:** This extends the existing cycle detection (`hashState`) — instead of just detecting cycles, cache the summary triple for each explored pattern.

### 7.3 Resource Separation for State Partitioning

**Core idea:** Partition the linear state into independent *resource regions* that evolve independently, like separation logic's disjoint heap fragments.

**Mechanism:** Static analysis on the rule set:

1. Build a **resource dependency graph**: node = predicate tag, edge = "some rule mentions both in antecedent/consequent"
2. Find **connected components** — each component is an independent resource region
3. During symexec, track regions independently — a rule firing in one region doesn't invalidate the index for other regions

**Example for EVM:**
- **Memory region:** `{mem, memsize, mem_read, mem_expand}` — connected by memory rules
- **Stack region:** `{stack, gas, pc, code}` — connected by arithmetic/control rules
- **Storage region:** `{storage, sstore, sload}` — connected by storage rules

If a rule only touches the stack region, the memory region's index doesn't need rebuilding.

**Where in CALC:** `strategy.js:findAllMatches()` — instead of scanning all rules against all state, scan only rules whose resource region has changed.

### 7.4 Footprint-Guided Exploration (Small Axiom)

**Core idea:** Separation logic's *small axiom* principle — specify only what a command touches. Apply this to guide symexec to explore with minimal state.

**Mechanism:**

1. For each rule, compute its **minimum footprint** (the smallest state fragment it needs)
2. During exploration, only match rules against their footprint, not the entire state
3. This is already partially implemented (fingerprint indexing, disc-tree), but could be made exact using SL-style footprint tracking

**Where in CALC:** This refines `buildStateIndex` — instead of a flat predicate index, build per-rule footprint indexes.

### 7.5 Ownership Types for Resource Tracking

**Core idea:** Rust's ownership model is separation logic at the type level. CALC could infer "ownership" for linear facts — who produced them, who is expected to consume them.

**Mechanism:**

1. **Provenance tracking:** Annotate each linear fact with the rule that produced it
2. **Expected consumer:** Static analysis identifies which rule(s) can consume each fact type
3. **Leak detection:** At leaves, linear facts with no possible consumer indicate stuck states (already done via `classifyLeaf`, but provenance makes it precise)
4. **Invariant inference:** Facts that are consumed and re-produced by the same rule (like `code PC Op` in EVM) are effectively borrowed, not consumed — this is an SL resource invariant

**Where in CALC:** `lib/engine/show.js:classifyLeaf()` could be enriched with provenance to give more precise diagnostics.

### 7.6 Separation Logic for CALL Frame Reasoning

**Core idea:** EVM CALL creates a new execution frame with fresh memory and stack. This is naturally modeled by separation logic's *nested triples* — the callee's frame is a separate heap.

**Mechanism:**

1. On CALL: save current `mem`, `memsize`, `stack` as `saved_mem`, `saved_memsize`, `returnstack`
2. Create fresh heap fragment: new `mem empty_mem * memsize 0`
3. Execute callee in the fresh fragment
4. On RETURN: restore saved state, compose callee's effects via frame rule

**Where in CALC:** TODO_0049 already declares `saved_mem`/`saved_memsize` for this. SL gives the formal framework for correctness: the callee's post-heap is *separate* from the caller's saved heap.

### 7.7 Abstract Predicates for State Abstraction

**Core idea:** Separation logic uses *abstract predicates* to hide internal resource structure behind an interface (Parkinson & Bierman, 2005). CALC could use these for modular symexec.

**Mechanism:**

1. Define abstract predicates that summarize complex state patterns: e.g., `sorted_list(head, len)` abstracts a chain of `cons` cells
2. Rules can be written against abstract predicates
3. Fold/unfold during symexec as needed

This connects to the existing `!` (bang) modality — persistent facts are effectively zero-cost predicates about state. Abstract predicates would extend this to linear state patterns.

### 7.8 Differential Frame Analysis for Incremental Symexec

**Core idea:** When re-exploring after a code change, use the frame rule to identify unchanged subtrees.

**Mechanism:**

1. After initial symexec, record each node's footprint (consumed/produced)
2. On code change, identify which rules changed
3. Only re-explore subtrees whose footprint overlaps the changed rules
4. All other subtrees are preserved by the frame rule

**Where in CALC:** This would enable incremental symexec for the UI — as the user edits `.ill` files, only the affected branches re-execute.

## 8. What CALC Already Has (and What's Missing)

### Already structural in CALC

| SL Concept | CALC Implementation |
|---|---|
| Separating conjunction `*` | Linear multiset (`state.linear`) |
| Frame rule | Automatic — rules touch only their antecedent/consequent |
| Points-to `x ↦ v` | `mem (write Offset Value Prev)`, `stack N V`, `code PC Op` |
| emp | `empty_mem`, empty linear context |
| Magic wand `-*` | Loli continuations (`matchLoli`) |
| `!P` (persistent) | `state.persistent` |
| No aliasing | Linearity — each fact exists exactly once |
| Footprint | Implicit in rule compilation (antecedent patterns) |

### Missing / could add

| SL Concept | Potential in CALC |
|---|---|
| CSL parallel rule | Parallel symexec (§7.1) |
| Bi-abduction / summaries | Compositional rule chaining (§7.2) |
| Resource regions | State partitioning (§7.3) |
| Ownership / provenance | Fact tracking (§7.5) |
| Nested triples | CALL frame reasoning (§7.6) |
| Abstract predicates | State abstraction (§7.7) |
| Differential frames | Incremental re-exploration (§7.8) |

## 9. Key References

1. Reynolds, J.C. "Separation Logic: A Logic for Shared Mutable Data Structures." LICS 2002.
2. O'Hearn, P.W. "Resources, Concurrency and Local Reasoning." TCS 2007 (journal version of the 2004 CONCUR paper).
3. Ishtiaq, S. & O'Hearn, P.W. "BI as an Assertion Language for Mutable Data Structures." POPL 2001.
4. Calcagno, C., Distefano, D., O'Hearn, P.W., Yang, H. "Compositional Shape Analysis by means of Bi-Abduction." JACM 2011.
5. Jung, R. et al. "Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning." POPL 2015.
6. Berdine, J., Calcagno, C., O'Hearn, P.W. "Symbolic Execution with Separation Logic." APLAS 2005.
7. O'Hearn, P.W. "Incorrectness Logic." POPL 2020.
8. Pym, D. "The Semantics and Proof Theory of the Logic of Bunched Implications." Kluwer, 2002.
9. Parkinson, M. & Bierman, G. "Separation Logic and Abstraction." POPL 2005.
10. Jung, R. et al. "RustBelt: Securing the Foundations of the Rust Programming Language." POPL 2018.
11. Batz, K. et al. "Quantitative Separation Logic." POPL 2019.
