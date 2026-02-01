# Girard's Recent Work: Ludics, Geometry of Interaction, and Transcendental Syntax

Brief overview of Jean-Yves Girard's post-linear-logic research program and its potential relevance to CALC.

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

## Geometry of Interaction (GoI)

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

### Key Innovation

Cut elimination becomes **algebraic**: compose operators, compute trace. No syntactic manipulation needed.

### Connection to Quantum

The GoI framework overlaps with **quantum operations**:
- Completely positive maps on density matrices
- Subcategories of Int(C) = quantum channels

This suggests deep connections between proof theory and quantum computation.

---

## Ludics (2001)

### Core Idea

**"From the rules of logic to the logic of rules"**

Proofs are not static syntactic objects but **interactive strategies** in a game between Player (prover) and Opponent (challenger).

### Key Concepts

**Designs** (generalized proofs):
- Sequences of alternating positive/negative actions
- Prefix-closed, coherent, terminate positively
- Like "focalized proofs without formulas"

**Orthogonality** (proof validity):
- Two designs are orthogonal if their interaction converges (reaches daimon †)
- D ⊥ E means "D and E interact successfully"

**Behaviours** (generalized formulas):
- Sets of designs closed under bi-orthogonality: B = B⊥⊥
- Formulas emerge from interaction patterns

### The Radical Move

Ludics inverts the usual order:
```
Traditional:  Formulas → Proofs → Semantics
Ludics:       Interaction → Designs → Behaviours (= formulas)
```

Meaning arises from **use** (Wittgenstein), not from pre-existing semantic interpretation.

### Connection to Game Semantics

Ludics is closely related to Hyland-Ong game semantics:
- Designs ≈ Innocent strategies
- Orthogonality ≈ Strategy composition
- Behaviours ≈ Arena/game types

But Ludics is more abstract — it doesn't presuppose games, just interaction.

---

## Transcendental Syntax (2011+)

### The Program

Girard's most recent work, inspired by Kant's transcendental philosophy:

> "What are the conditions of possibility for logic?"

Rather than assuming logic (rules, formulas, truth), derive it from computation.

### The Four Levels ("Infernos")

Girard organizes meaning into 2×2 matrix:

|  | Analytic (Answers) | Synthetic (Questions) |
|--|---------------------|------------------------|
| **A posteriori** | Constat (normal forms) | Usine (testing) |
| **A priori** | Performance (potential) | Usage (meaning-in-use) |

Each level is "deeper" than the one above.

### Constellations

The basic objects are **constellations**:
- Multisets of clauses containing first-order terms
- No inherent logical meaning
- Can interact via Robinson's resolution

### Stellar Resolution

A "logic-free" reformulation of resolution:
- Terms interact via unification
- Results in new constellations
- Cut elimination encoded as resolution dynamics

### Key Papers

1. **Transcendental Syntax I: Deterministic Case** (2017)
   - Studies the deterministic fragment
   - Analytic/synthetic distinction

2. **Transcendental Syntax II: Non-deterministic Case** (2016)
   - Handles non-determinism
   - "Le fantôme de la transparence"

3. **Transcendental Syntax III: Equality** (2018)
   - Reconstructs predicate and second-order logic

4. **Transcendental Syntax IV: Logic Without Systems** (2020)
   - Removes remaining logical assumptions

### Boris Eng's Thesis (2023)

"An Exegesis of Transcendental Syntax" provides the clearest exposition:
- Formal definition of stellar resolution
- Connection to linear logic multiplicatives
- Sketch of extension to full linear logic

---

## Relevance to CALC

### Potentially Relevant

1. **Ludics' Orthogonality**
   - Could model "compatible transactions" (both parties agree)
   - D ⊥ E = "D and E can interact without deadlock"
   - Relates to our atomic swap: both parties must consent

2. **Designs as Protocols**
   - A design is like a "interaction protocol"
   - Could model smart contract interaction patterns
   - Relates to session types (Nomos research)

3. **Behaviours as Types**
   - Behaviours emerge from interaction patterns
   - Could give semantics to ownership modalities
   - `[Alice] A` as "behaviour of Alice-controlled proofs"?

4. **Geometry of Interaction for Verification**
   - Algebraic semantics could provide verification
   - Proof = operator, verification = trace computation
   - Could connect to our proof search

### Probably Not Immediately Relevant

1. **Transcendental Syntax**
   - Very foundational/philosophical
   - Mostly about "what is logic?" not "how to use logic"
   - May be relevant later for deep foundations

2. **C*-algebras/Operator Algebras**
   - Girard's original GoI setting
   - High mathematical overhead
   - Simpler categorical versions (Int(C)) suffice for us

3. **Quantum Connections**
   - Interesting but not our focus
   - May become relevant if modeling quantum cryptography

### Concrete Next Steps

If we want to pursue Girard's ideas:

1. **Study Ludics for interaction semantics**
   - Could give semantics to multi-party protocols
   - Orthogonality = consensus/agreement?

2. **Study focalization more deeply**
   - Ludics is based on focalized proofs
   - We already use focusing in proof search
   - Could improve our implementation

3. **Consider GoI for verification**
   - Algebraic semantics for proofs
   - Could verify that proof search is correct

---

## Open Questions (for TODO)

1. **Can ownership modalities be understood as ludic behaviours?**
   - `[Alice]` as a class of designs?
   - Orthogonality = Alice agrees to the interaction?

2. **Is there a ludic interpretation of the accounting equation?**
   - Debits ⊥ Credits (they "cancel out")?
   - Balanced transaction = successful interaction?

3. **Can stellar resolution model transaction validation?**
   - Transactions as constellations?
   - Validation as resolution to normal form?

---

## Summary

Girard's post-linear-logic work explores increasingly deep foundations:

- **GoI**: Proofs as operators, cut as composition
- **Ludics**: Proofs as interactive strategies, meaning from orthogonality
- **TS**: Logic derived from computation

For CALC, the most relevant ideas are:
- **Orthogonality** as a model for "agreement" or "consensus"
- **Behaviours** as a way to understand type-like concepts
- **Focalization** which we already use implicitly

The transcendental syntax program is philosophically interesting but likely too foundational for immediate practical use.

---

## References

### Primary Sources
- Girard, "Locus Solum: From the Rules of Logic to the Logic of Rules" (2001)
- Girard, "Geometry of Interaction I-V" (1989-1995)
- Girard, "Transcendental Syntax I-IV" (2016-2020)

### Expository
- [nLab: Transcendental Syntax](https://ncatlab.org/nlab/show/transcendental+syntax)
- [nLab: Geometry of Interaction](https://ncatlab.org/nlab/show/Geometry+of+Interaction)
- [Grokipedia: Ludics](https://grokipedia.com/page/ludics)
- [Eng, "A Gentle Introduction to Girard's Transcendental Syntax"](https://arxiv.org/abs/2012.04752)
- [Eng, "An Exegesis of Transcendental Syntax" (PhD thesis, 2023)](https://hal.science/tel-04179276)

### Related
- [Wikipedia: Game Semantics](https://en.wikipedia.org/wiki/Game_semantics)
- [Stanford Encyclopedia: Linear Logic](https://plato.stanford.edu/entries/logic-linear/)

---

*Last updated: 2026-01-29*
