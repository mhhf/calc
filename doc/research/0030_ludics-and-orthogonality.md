---
title: "Ludics, Orthogonality, and Girard's Post-Linear-Logic Work"
created: 2026-02-10
modified: 2026-02-10
summary: Girard's Ludics framework with interactive game semantics and orthogonality potentially modeling multi-party consensus through converging interactions.
tags: [Ludics, orthogonality, game-semantics, Girard, consensus]
category: "Related Paradigms"
---

# Ludics, Orthogonality, and Girard's Post-Linear-Logic Work

Comprehensive research on Girard's post-linear-logic research: Ludics, Geometry of Interaction, Transcendental Syntax, and how orthogonality could model consensus in CALC.

> **See also:** [[consensus-modalities-mpst]] for MCP coherence as n-ary orthogonality, [[linear-negation-debt]] for game semantics and duality, [[authorization-logic]] for principal-based reasoning, [[proof-calculi-foundations]] for proof formalisms.

---

## Table of Contents

1. [Girard's Research Trajectory](#girards-research-trajectory)
2. [Geometry of Interaction (GoI)](#geometry-of-interaction)
3. [Ludics Core Concepts](#ludics-core-concepts)
4. [Orthogonality and Behaviours](#orthogonality-and-behaviours)
5. [Orthogonality as Agreement/Consensus](#orthogonality-as-agreementconsensus)
6. [The N-ary Orthogonality Gap](#the-n-ary-orthogonality-gap)
7. [Transcendental Syntax](#transcendental-syntax)
8. [Relevance to CALC](#relevance-to-calc)
9. [Open Questions](#open-questions)
10. [References](#references)

---

## Girard's Research Trajectory

| Year | Contribution | Key Idea |
|------|--------------|----------|
| 1987 | **Linear Logic** | Resource-sensitive logic, "!" for reuse |
| 1989 | **Geometry of Interaction** | Proofs as algebraic operators, cut = composition |
| 2001 | **Ludics** | Proofs as interactive games, meaning from interaction |
| 2011+ | **Transcendental Syntax** | Logic from computation, not vice versa |

Each step abstracts further from traditional logic, seeking deeper foundations.

---

## Geometry of Interaction

### Core Idea

Instead of interpreting proofs as morphisms in a category, GoI interprets them as **endomorphisms** (operators acting on themselves).

```
Proof of A ⊢ B  →  Endomorphism on (A ⊸ B)
Cut elimination  →  Operator composition + trace
```

### Mathematical Framework

- **Traced monoidal categories**: Provide the structure
- **Int(C) construction**: Pairs (A⁺, A⁻) with traced composition
- **C*-algebras**: Girard's original setting (von Neumann algebras)

Cut elimination becomes **algebraic**: compose operators, compute trace. No syntactic manipulation needed.

### Connection to Quantum

The GoI framework overlaps with **quantum operations**:
- Completely positive maps on density matrices
- Subcategories of Int(C) = quantum channels

This suggests deep connections between proof theory and quantum computation.

---

## Ludics Core Concepts

### The Shift from Syntax to Interaction

Traditional logic:
```
Formulas → Proofs → Semantics (models)
```

Ludics:
```
Interaction → Orthogonality → Behaviours (types) → Logic
```

**"From the rules of logic to the logic of rules"** — Logic emerges FROM interaction.

### 1. Designs

**Designs** are the primitive objects — abstractions of proofs where:
- Formulas are replaced by **addresses** (locations/loci)
- Only information relevant for interaction is retained
- They can be seen as strategies in a game

A design consists of:
- **Positive actions**: Player chooses a locus and ramification (like making a move)
- **Negative actions**: Opponent responds (like awaiting a move)
- **Daimon (†)**: Termination signal (successful end)

```
Design = alternating tree of positive/negative actions
         possibly ending in daimon
```

### 2. Polarity and Focalization

Ludics crucially uses **polarity**:

| Polarity | Connectives | Meaning |
|----------|-------------|---------|
| Positive | ⊗, ⊕, ∃ | Active, irreversible, non-deterministic |
| Negative | ⅋, &, ∀ | Passive, reversible, deterministic |

**Focalization**: Proofs alternate between positive and negative phases.
- Positive phases: make all positive moves at once
- Negative phases: wait for all negative inputs

This is the computational foundation: **continuation-passing style**.

### 3. Interaction (Normalization)

When two designs interact (via cut/composition):

```
[[D, E]] = result of interaction between D and E
```

The interaction proceeds:
1. D makes a positive move
2. E responds with matching negative move
3. Alternation continues
4. Ends when either:
   - † (daimon) is reached → **convergence** (success)
   - No matching move exists → **divergence** (failure/deadlock)

---

## Orthogonality and Behaviours

### Definition

Two designs D and E are **orthogonal** (D ⊥ E) iff their interaction converges to daimon.

```
D ⊥ E  ⟺  [[D, E]] = †
```

Meaning: D and E "fit together" — they can successfully interact.

### Orthogonal of a Set

```
A⊥ = { E | ∀D ∈ A. D ⊥ E }
```

All designs that successfully interact with every element of A.

### Bi-Orthogonality and Behaviours

**Behaviour**: A set of designs closed under bi-orthogonal:
```
G is a behaviour  ⟺  G = G⊥⊥
```

**Key insight**: Behaviours ARE types!
- A behaviour is all designs that pass the same tests
- Formulas/types emerge from orthogonality, not defined a priori

**Internal completeness**: For well-behaved constructions:
```
(A ⊗ B)⊥⊥ = A ⊗ B   (no need for closure!)
```

---

## Orthogonality as Agreement/Consensus

### The Dialogue Interpretation

In Ludics, interaction models **dialogue**:

```
Design D = Alice's strategy
Design E = Bob's strategy
D ⊥ E = Alice and Bob can successfully complete a dialogue
```

**Convergence** = the speakers reach a point of agreement (one gives daimon)
**Divergence** = breakdown, misunderstanding, deadlock

From Lecomte & Quatrini: "A dialogue converges when the two speakers go together towards a situation where they agree at least on some points."

### Consensus as Mutual Orthogonality

**Hypothesis**: `[A ∧ B] φ` (consensus of A and B on φ) can be modeled as:

```
D_Alice ⊥ D_φ  ∧  D_Bob ⊥ D_φ
```

Or more strongly, as the existence of compatible designs:
```
∃D_A, D_B. D_A ⊥ D_B  ∧  D_A ∈ Alice's_behaviour  ∧  D_B ∈ Bob's_behaviour
```

### Atomic Swap as Interaction

```
[Alice] coin(BTC, 0.5) ⊗ [Bob] coin(ETH, 5.0)
                       ⊸
[Bob] coin(BTC, 0.5) ⊗ [Alice] coin(ETH, 5.0)
```

In Ludics terms:
- Alice's design: "I will give BTC if I receive ETH"
- Bob's design: "I will give ETH if I receive BTC"
- These designs are ORTHOGONAL — they fit together

```
D_Alice = (+, give_BTC, {receive_ETH}).(−, receive_ETH, {}).†
D_Bob = (+, give_ETH, {receive_BTC}).(−, receive_BTC, {}).†

D_Alice ⊥ D_Bob  ⟺  swap succeeds
```

The swap is **atomic** because:
1. Either both transfers happen (convergence to †)
2. Or neither happens (divergence before either transfer)

---

## The N-ary Orthogonality Gap

### The Problem

Standard Ludics orthogonality is **binary**: D ⊥ E.

But consensus typically involves **n parties**:
```
[Alice ∧ Bob ∧ Carol] φ   -- 3-way consensus
```

### Attempted Solutions

**Attempt 1: Pairwise Orthogonality**
```
D_A ⊥ D_B ∧ D_B ⊥ D_C ∧ D_A ⊥ D_C
```
**Problem**: Pairwise orthogonality ≠ global compatibility.

**Attempt 2: Sequential Composition**
```
D_A ⊥ (D_B ⊥ D_C)    [associative?]
```
**Problem**: Orthogonality is NOT associative in general.

### The Solution: Coherence (MCP)

From Multiparty Session Types, replace binary duality with n-ary **coherence**:

```
coherent(T₁, T₂, ..., Tₙ) ⟺ types can jointly participate in session
```

**Key insight**: Coherence generalizes duality
- Duality: T ⊥ T⊥ (two types fit)
- Coherence: T₁, ..., Tₙ all fit together (n types fit)

### The MCut Rule

Classical Linear Logic has **Cut** for binary composition:
```
Γ ⊢ A    A ⊢ Δ
─────────────── Cut
    Γ ⊢ Δ
```

MCP (Multiparty Classical Processes) has **MCut**:
```
Γ₁ ⊢ T₁  ...  Γₙ ⊢ Tₙ    coherent(T₁,...,Tₙ)
────────────────────────────────────────────── MCut
              Γ₁,...,Γₙ ⊢ ·
```

### L-Nets Extension

**L-nets** (Faggian & Maurel) extend Ludics for concurrent interaction:
- Designs become **graphs** (not just trees)
- Interactions produce **partial orders** (allowing parallelism)
- Multiple participants can interact concurrently

---

## Transcendental Syntax

### The Program

Girard's most recent work, inspired by Kant:

> "What are the conditions of possibility for logic?"

Rather than assuming logic (rules, formulas, truth), derive it from computation.

### The Four Levels ("Infernos")

|  | Analytic (Answers) | Synthetic (Questions) |
|--|---------------------|------------------------|
| **A posteriori** | Constat (normal forms) | Usine (testing) |
| **A priori** | Performance (potential) | Usage (meaning-in-use) |

### Constellations and Stellar Resolution

**Constellations**: Multisets of clauses containing first-order terms
- No inherent logical meaning
- Can interact via Robinson's resolution

**Stellar Resolution**: A "logic-free" reformulation of resolution:
- Terms interact via unification
- Results in new constellations
- Cut elimination encoded as resolution dynamics

### Key Papers

1. **Transcendental Syntax I: Deterministic Case** (2017)
2. **Transcendental Syntax II: Non-deterministic Case** (2016)
3. **Transcendental Syntax III: Equality** (2018)
4. **Transcendental Syntax IV: Logic Without Systems** (2020)

**Boris Eng's Thesis** (2023) "An Exegesis of Transcendental Syntax" provides the clearest exposition.

---

## Relevance to CALC

### Potentially Relevant

| Concept | Connection to CALC |
|---------|-------------------|
| **Orthogonality** | Model "compatible transactions" — both parties agree |
| **Designs as Protocols** | Smart contract interaction patterns |
| **Behaviours as Types** | Semantics for ownership modalities |
| **Focalization** | We already use this in proof search |
| **GoI for Verification** | Algebraic proof verification |

### Comparison: Orthogonality vs Other Approaches

| Aspect | Orthogonality | Session Types | Auth Logic |
|--------|---------------|---------------|------------|
| Primitive | Interaction | Protocol | Says/speaks-for |
| Types emerge from | Tests | Global types | Policies |
| Consensus | D ⊥ E | coherent(T₁,...,Tₙ) | (A ∧ B) says S |
| n-party | Needs extension | Built-in (MPST) | Composite principals |

### Recommendations for CALC

**Short-term:**
- Don't add Ludics primitives — too complex
- Use orthogonality as **intuition** — guides design decisions
- Model atomic swap as orthogonal designs — informal verification

**Medium-term:**
- Study coherence from MCP — closest to what we need
- Consider principal-indexed behaviours
- Prototype n-ary orthogonality for composite principals

**Long-term:**
- Formal Ludics model for CALC — full semantic foundation
- Prove internal completeness for CALC-specific types
- Connect authorization to behaviours — policies as bi-orthogonal closed sets

---

## Open Questions

### 1. n-ary Orthogonality — PARTIAL ANSWER

MCP's **coherence** is the best existing answer. Properties:
- **NOT symmetric** in general: order may matter for causal dependencies
- **Conservative** for n=2: reduces to standard duality
- **NOT associative**: intermediate interaction may differ from global interaction

**For CALC**: Use coherence from MCP rather than extending Ludics orthogonality.

### 2. Principal-Aware Designs — NO EXISTING WORK

No existing work found on principal-annotated Ludics designs. Challenges:
- Ludics doesn't track "who" makes moves — only THAT moves are made
- Would need to define what `D^Alice ⊥ E^Bob` means semantically

**For CALC**: Use principal indexing at formula level `[Alice] A` for now.

### 3. Threshold Orthogonality — LIKELY IMPOSSIBLE

The combinatorial explosion affecting threshold modalities also affects threshold orthogonality.

**For CALC**: Don't express threshold as orthogonality. Use threshold predicate at formula level.

### 4. Authorization via Behaviours — PROMISING

Conceptually YES, but no formalization found.
- Behaviour G = G⊥⊥ = all designs that pass the same tests
- Policy_P = all strategies satisfying P's authorization requirements
- Two strategies satisfying the same policy can't be distinguished by interaction

### 5. Consensus = Deadlock Freedom — YES (from MCP)

```
coherent(T₁,...,Tₙ) ⟹ protocols with these types won't deadlock
```

Deadlock freedom for coherent types implies all parties CAN reach consensus.

**Nuance**: "Can reach" ≠ "Will reach". Liveness requires additional assumptions.

---

## References

### Ludics Core
- [Girard, "Locus Solum: From the rules of logic to the logic of rules" (MSCS 2001)](https://nguyentito.eu/locus-solum-mscs.pdf)
- [Grokipedia: Ludics](https://grokipedia.com/page/ludics)

### Ludics Tutorials
- [Curien, "Introduction to linear logic and ludics, Part II"](https://www.irif.fr/~curien/LL-ludintroII.pdf)
- [Vaux, "An introduction to ludics"](https://www.i2m.univ-amu.fr/perso/lionel.vaux/pub/ludique-clmps11.pdf)

### Geometry of Interaction
- [nLab: Geometry of Interaction](https://ncatlab.org/nlab/show/Geometry+of+Interaction)
- Girard, "Geometry of Interaction I-V" (1989-1995)

### Concurrent Ludics
- [Faggian & Maurel, "Ludics nets, a game model of concurrent interaction" (LICS 2005)](https://www.irif.fr/~faggian/pubs/lics05.pdf)
- [Faggian & Piccolo, "Ludics is a Model for the Finitary Linear Pi-Calculus"](https://link.springer.com/chapter/10.1007/978-3-540-73228-0_12)

### Transcendental Syntax
- Girard, "Transcendental Syntax I-IV" (2016-2020)
- [nLab: Transcendental Syntax](https://ncatlab.org/nlab/show/transcendental+syntax)
- [Eng, "A Gentle Introduction to Girard's Transcendental Syntax"](https://arxiv.org/abs/2012.04752)
- [Eng, "An Exegesis of Transcendental Syntax" (PhD thesis, 2023)](https://hal.science/tel-04179276)

### Multiparty Session Types
- [Carbone et al., "Multiparty session types as coherence proofs" (Acta Informatica 2017)](https://link.springer.com/article/10.1007/s00236-016-0285-y)
- [Carbone et al., "Coherence Generalises Duality" (CONCUR 2016)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2016.33)

### Dialogue and Ludics
- [Lecomte & Quatrini, "Figures of dialogue: a view from Ludics" (Synthese 2011)](https://link.springer.com/article/10.1007/s11229-011-0014-6)

---

*Created: 2026-02-10 (merged from girard-recent-work.md and ludics-orthogonality-consensus.md)*
