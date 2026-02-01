# Ludics Orthogonality for Consensus Semantics

This document explores Girard's Ludics framework and how its orthogonality relation could provide a semantic foundation for consensus in CALC.

---

## The Central Question

Can Ludics orthogonality model consensus semantics?

```
D ⊥ E    -- Designs D and E "agree" (interaction converges)
```

**Hypothesis**: Consensus between principals is orthogonality between their designs.

---

## Background: What is Ludics?

### Overview

Ludics is a logical framework introduced by Girard (2001) that rebuilds linear logic from interaction alone. The key insight: **proofs are defined by their behavior when tested**, not by syntactic rules.

Key slogan: "The meaning of a proof is determined by its interactions."

### The Shift from Syntax to Interaction

Traditional logic:
```
Formulas → Proofs → Semantics (models)
```

Ludics:
```
Interaction → Orthogonality → Behaviours (types) → Logic
```

Logic emerges FROM interaction, not the other way around.

---

## Core Concepts of Ludics

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

### 4. Orthogonality

**Definition**: Two designs D and E are **orthogonal** (D ⊥ E) iff their interaction converges to daimon.

```
D ⊥ E  ⟺  [[D, E]] = †
```

Meaning: D and E "fit together" — they can successfully interact.

**Orthogonal of a set**:
```
A⊥ = { E | ∀D ∈ A. D ⊥ E }
```

All designs that successfully interact with every element of A.

### 5. Bi-Orthogonality and Behaviours

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

## Orthogonality as Agreement

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

Meaning: Both Alice and Bob have strategies that "fit with" φ.

Or more strongly, as the existence of compatible designs:
```
∃D_A, D_B. D_A ⊥ D_B  ∧  D_A ∈ Alice's_behaviour  ∧  D_B ∈ Bob's_behaviour
```

---

## The Gap: Binary vs N-ary Orthogonality

### The Problem

Standard Ludics orthogonality is **binary**: D ⊥ E.

But consensus typically involves **n parties**:
```
[Alice ∧ Bob ∧ Carol] φ   -- 3-way consensus
```

### Attempt 1: Pairwise Orthogonality

```
D_A ⊥ D_B ∧ D_B ⊥ D_C ∧ D_A ⊥ D_C
```

**Problem**: Pairwise orthogonality ≠ global compatibility.
Each pair can interact, but all three together might fail.

### Attempt 2: Sequential Composition

```
D_A ⊥ (D_B ⊥ D_C)    [associative?]
```

**Problem**: Orthogonality is NOT associative in general.
The order of composition matters.

### Attempt 3: Coherence (Carbone et al.)

**Solution from multiparty session types**: Replace binary duality with n-ary **coherence**.

From "Multiparty Session Types as Coherence Proofs":
```
coherent(T₁, T₂, ..., Tₙ) ⟺ types can jointly participate in session
```

**Key idea**: Coherence generalizes duality
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

---

## Ludics Extensions for Multi-Party

### L-Nets (Faggian & Maurel)

**L-nets** extend Ludics for concurrent interaction:

- Designs become **graphs** (not just trees)
- Interactions produce **partial orders** (allowing parallelism)
- Multiple participants can interact concurrently

Key features:
- Parallel composition + hiding of internal communication
- Logical L-nets can be sequentialized back to trees
- Model for multiplicative additive linear logic (MALL)

### Connection to π-Calculus (Faggian & Piccolo)

"Ludics is a model for the finitary linear π-calculus"

Key insight: **Addresses in Ludics ≈ Channels in π-calculus**

```
Ludics address discipline ≈ internal π-calculus (π-I)
```

This suggests: Multi-party session types could map to multi-party Ludics.

---

## Realizability and Orthogonality

### Krivine's Classical Realizability

Orthogonality in Ludics is closely related to **Krivine realizability**:

```
t ⊥ π  ⟺  t ⋆ π ∈ ⊥⊥  (process is in the pole)
```

Where:
- t = term (realizer)
- π = stack (continuation/test)
- ⊥⊥ = pole (set of "good" processes)

**Truth value**: |A| = {t | ∀π ∈ ‖A‖. t ⋆ π ∈ ⊥⊥}

A realizer of A is a term that passes all tests in A's falsity value.

### The Pole as Parameter

The pole ⊥⊥ is a **parameter** of the model:
- Different poles give different notions of "success"
- This is analogous to choosing what counts as "agreement"

**For consensus**: We could parameterize by what counts as successful n-party interaction.

---

## Proposed Model for CALC

### Design: Principal-Indexed Designs

Extend designs with principal annotations:

```
D^Alice : ξ⁺    -- Alice's positive design at address ξ
E^Bob : ξ⁻      -- Bob's negative design at address ξ
```

### Orthogonality per Principal

```
D^A ⊥ E^B  ⟺  [[D^A, E^B]] = †
```

Alice's strategy and Bob's strategy successfully interact.

### N-ary Coherence

Define n-ary coherence for CALC:

```
coherent(D^{P₁}, ..., D^{Pₙ})  ⟺
    ∃ global interaction G.
    ∀i. G↾Pᵢ = D^{Pᵢ}  ∧  G converges
```

Where G↾P is the projection to principal P.

### Consensus Modality Semantics

```
⟦[A ∧ B] φ⟧ = { D | ∃D_A, D_B. coherent(D_A, D_B, D) ∧ D_A ∈ ⟦A⟧ ∧ D_B ∈ ⟦B⟧ }
```

Meaning: D realizes consensus if there exist compatible strategies for A and B.

---

## Connection to Atomic Swap

### The Atomic Swap as Interaction

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

### Why Atomicity = Orthogonality

The swap is **atomic** because:
1. Either both transfers happen (convergence to †)
2. Or neither happens (divergence before either transfer)

Orthogonality ensures: You can't get one transfer without the other.

---

## Comparison: Orthogonality vs Other Approaches

| Aspect | Orthogonality | Session Types | Auth Logic |
|--------|---------------|---------------|------------|
| Primitive | Interaction | Protocol | Says/speaks-for |
| Types emerge from | Tests | Global types | Policies |
| Consensus | D ⊥ E | coherent(T₁,...,Tₙ) | (A ∧ B) says S |
| Composition | Cut | MCut | ⊗ |
| n-party | Needs extension | Built-in (MPST) | Composite principals |

### Advantages of Orthogonality Approach

1. **Semantic foundation**: Types emerge from behavior, not syntax
2. **Computational**: Directly models execution (normalization)
3. **Completeness**: Internal completeness gives constructive semantics
4. **Compositionality**: Clear how strategies compose

### Disadvantages

1. **Binary by default**: Need coherence extension for n-party
2. **Complexity**: Full Ludics is technically demanding
3. **Principal identity**: Doesn't natively track WHO is interacting

---

## Research Update: Open Questions

### 1. n-ary Orthogonality — PARTIAL ANSWER

**Question**: Is there a natural n-ary orthogonality that is symmetric, conservative, associative-like?

**Finding**: MCP's **coherence** is the best existing answer. No native Ludics n-ary orthogonality, but:

```
coherent(T₁, ..., Tₙ)  ⟺  types can jointly participate in session
```

**Properties**:
- **NOT symmetric** in general: order may matter for causal dependencies
- **Conservative** for n=2: reduces to standard duality
- **NOT associative**: ⊥(⊥(D₁,D₂),D₃) may differ from global 3-party interaction

**Why not associative**: Intermediate interaction ⊥(D₁,D₂) may produce a result that interacts differently with D₃ than simultaneous 3-party interaction would.

**For CALC**: Use coherence from MCP rather than trying to extend Ludics orthogonality. Accept non-associativity as fundamental to multi-party interaction.

### 2. Principal-Aware Designs — NO EXISTING WORK

**Question**: Can we annotate designs with principals cleanly?

**Finding**: No existing work found on principal-annotated Ludics designs.

**Challenges**:
- Ludics doesn't natively track "who" makes moves — only THAT moves are made
- Adding principal annotation is external structure, not native to the theory
- Would need to define: what does `D^Alice ⊥ E^Bob` mean semantically?

**Potential approach**:
```
D^Alice : ξ⁺    -- Design D with Alice controlling positive actions at ξ
```

Would need rules for:
- Interaction between D^A and E^B (different principals)
- Composition of D^A with D^A (same principal)
- What "control" means operationally

**For CALC**: This remains research direction. Use principal indexing at formula level `[Alice] A` rather than design level for now.

### 3. Threshold Orthogonality — LIKELY IMPOSSIBLE

**Question**: Can we define k-of-n orthogonality?

**Analysis**: The combinatorial explosion that affects threshold modalities also affects threshold orthogonality:
```
⊥_{2-of-3}(D_A, D_B, D_C)
≈  (D_A ⊥ D_B) ∨ (D_A ⊥ D_C) ∨ (D_B ⊥ D_C)  -- but convergence is not OR
```

**Problem**: Orthogonality is about interaction CONVERGING (reaching †). "At least 2 of 3 converge" doesn't have the same clean structure.

**For CALC**: Don't try to express threshold as orthogonality. Use threshold predicate at the formula level: `threshold(k, [A,B,C], φ)`.

### 4. Authorization via Behaviours — CONCEPTUALLY PROMISING

**Question**: Can authorization policies be behaviours?

**Finding**: Conceptually YES, but no formalization found.

**The analogy**:
- Behaviour G = G⊥⊥ = all designs that pass the same tests
- Policy_P = all strategies that satisfy P's authorization requirements

**If requirements can be expressed as tests**:
```
policy_P = { D | D realizes P's authorization }
policy_P = policy_P⊥⊥   iff  authorization is "closed under testing"
```

**What this would mean**:
- Two strategies satisfying the same policy can't be distinguished by any interaction
- Policy is defined by what it ALLOWS, not how it's syntactically written
- Equivalent policies (same authorized behaviors) are identical

**For CALC**: This is a promising long-term research direction. Would give semantic foundation for authorization that emerges from interaction, not syntactic rules.

### 5. Consensus = Deadlock Freedom? — YES (from MCP)

**Question**: Does orthogonality (convergence) = consensus achievability?

**Finding from MCP**:
```
coherent(T₁,...,Tₙ) ⟹ protocols with these types won't deadlock
```

This IS a theorem in MCP. Deadlock freedom for coherent types implies all parties CAN reach consensus.

**Nuance**: "Can reach" ≠ "Will reach". Deadlock freedom means consensus is ACHIEVABLE if parties follow the protocol. Doesn't guarantee they WILL (liveness ≠ safety).

**For CALC**: Coherence/orthogonality gives us safety ("if everyone participates correctly, consensus is reachable"). Liveness ("everyone eventually participates") requires additional assumptions.

---

## Relationship to Other Research

### Multiparty Session Types

Coherence in MCP is closest to what CALC needs:
- Generalized cut rule (MCut)
- n-ary type compatibility
- Deadlock freedom as theorem

**Key paper**: Carbone et al., "Multiparty Session Types as Coherence Proofs"

### Transcendental Syntax

Girard's later work pushes further:
- Stellar resolution (logic-free computation)
- Constellations as independent agents
- Even more radical: computation generates logic

### Interactive Observability

Faggian's work on what can be "seen" about a design:
- Designs as black boxes
- Testing reveals behavior
- Geometry of tests

---

## Recommendations for CALC

### Short-term

1. **Don't add Ludics primitives** — too complex for now
2. **Use orthogonality as intuition** — guides design decisions
3. **Model atomic swap as orthogonal designs** — informal verification

### Medium-term

1. **Study coherence from MCP** — closest to what we need
2. **Consider principal-indexed behaviours**
3. **Prototype n-ary orthogonality** — for composite principals

### Long-term

1. **Formal Ludics model for CALC** — full semantic foundation
2. **Prove internal completeness** — for CALC-specific types
3. **Connect to authorization** — behaviours as policies

---

## Summary

**Can Ludics orthogonality model consensus?**

**Partially YES:**
- Binary orthogonality captures 2-party agreement beautifully
- Convergence = successful interaction = consensus achieved
- Behaviours (bi-orthogonal closed sets) = types emerging from tests

**Challenges:**
- Need n-ary extension (coherence from MCP)
- Principal identity not native to Ludics
- Technical complexity is high

**Key insight**:
Consensus is not a syntactic property — it's a SEMANTIC property about whether strategies can successfully interact. Orthogonality captures exactly this.

**Recommendation**:
Use Ludics/orthogonality as the **semantic foundation** for understanding consensus in CALC, while using simpler syntactic mechanisms (protocol patterns, composite principals) for implementation.

---

## References

### Ludics Core
- [Girard, "Locus Solum: From the rules of logic to the logic of rules" (MSCS 2001)](https://nguyentito.eu/locus-solum-mscs.pdf)
- [Grokipedia: Ludics](https://grokipedia.com/page/ludics)

### Ludics Tutorials
- [Curien, "Introduction to linear logic and ludics, Part II"](https://www.irif.fr/~curien/LL-ludintroII.pdf)
- [Vaux, "An introduction to ludics"](https://www.i2m.univ-amu.fr/perso/lionel.vaux/pub/ludique-clmps11.pdf)

### Concurrent Ludics
- [Faggian & Maurel, "Ludics nets, a game model of concurrent interaction" (LICS 2005)](https://www.irif.fr/~faggian/pubs/lics05.pdf)
- [Faggian & Piccolo, "Ludics is a Model for the Finitary Linear Pi-Calculus"](https://link.springer.com/chapter/10.1007/978-3-540-73228-0_12)

### Multiparty Session Types
- [Carbone et al., "Multiparty session types as coherence proofs" (Acta Informatica 2017)](https://link.springer.com/article/10.1007/s00236-016-0285-y)
- [Carbone et al., "Coherence Generalises Duality" (CONCUR 2016)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2016.33)

### Dialogue and Ludics
- [Lecomte & Quatrini, "Figures of dialogue: a view from Ludics" (Synthese 2011)](https://link.springer.com/article/10.1007/s11229-011-0014-6)
- ["Dialogue and Interaction: the Ludics view"](https://www.academia.edu/17124858/Dialogue_and_Interaction_the_Ludics_view)

### Realizability
- [Abramsky & Lenisa, "Linear realizability and full completeness"](https://link.springer.com/chapter/10.1007/978-3-540-74915-8_32)
- [Miquel, "An introduction to Krivine realizability"](https://www.fing.edu.uy/~amiquel/intro-krivine.pdf)

### Related CALC Research
- [[consensus-modalities-mpst]] — How consensus fits with MPST
- [[adjoint-logic-unifying-framework]] — Adjoint logic as unifying framework
- [[adjunctions-deep-study]] — Deep study of adjunctions

---

*Last updated: 2026-01-29*
