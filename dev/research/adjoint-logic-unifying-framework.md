# Adjoint Logic as a Unifying Framework

This document evaluates whether adjoint logic should serve as the unifying framework for CALC's various modalities: ownership, authorization, consensus, session types, and resource tracking.

---

## What is Adjoint Logic?

**Adjoint logic** (or adjoint type theory) is a formal logic that natively expresses adjunctions between modal operators. It provides a general framework for combining multiple logics with different structural properties.

### Historical Development

| Year | Contribution | Authors |
|------|--------------|---------|
| 1994 | LNL (Linear/Non-Linear) logic | Benton |
| 1996 | Adjoint λ-calculus | Benton, Wadler |
| 2009 | Judgmental deconstruction with mode preorder | Reed |
| 2016 | Adjoint logic with 2-category of modes | Licata, Shulman |
| 2017 | Fibrational framework | Licata, Shulman, Riley |
| 2018 | Adjoint logic (comprehensive treatment) | Pruiksma, Chargin, Pfenning, Reed |
| 2020 | Graded adjoint logic | Eades, Orchard |
| 2021 | Message-passing interpretation | Pruiksma, Pfenning |

### Core Idea

Instead of having ad-hoc modal operators, adjoint logic:
1. Parametrizes the logic by a **preorder (or 2-category) of modes**
2. Each mode can have different **structural properties** (weakening, contraction)
3. **Adjoint modalities** F and U (or ↑ and ↓) bridge between modes
4. Cut elimination follows **generically** from the framework

---

## Modes and Structural Properties

### The Mode Preorder

A mode preorder `(M, ≤)` specifies:
- A set of **modes** M (e.g., `{linear, affine, cartesian}`)
- A **preorder** ≤ on modes (e.g., `cartesian ≥ linear`)
- Each mode morphism `m ≥ k` induces an **adjunction** F ⊣ U

**Interpretation**: `m ≥ k` means "a proof of something at mode k may depend on an assumption at mode m."

### Structural Properties Per Mode

Each mode m has a set σ(m) ⊆ {W, C}:

| Property | Meaning | σ(m) contains |
|----------|---------|---------------|
| **Weakening (W)** | Antecedent need not be used | W ∈ σ(m) |
| **Contraction (C)** | Antecedent can be used multiple times | C ∈ σ(m) |

**Standard modes:**
- **Linear**: σ(L) = {} (no W, no C) — use exactly once
- **Affine**: σ(A) = {W} (W, no C) — use at most once
- **Relevant**: σ(R) = {C} (no W, C) — use at least once
- **Cartesian/Intuitionistic**: σ(U) = {W, C} — use any number of times

**Monotonicity requirement**: If m ≥ k, then σ(m) ⊇ σ(k).

This ensures you can always use a "more structural" assumption where a "less structural" one is expected.

---

## The Adjoint Modalities

### Upshift and Downshift

For modes m ≥ k, two modalities bridge between them:

```
↑ᵏₘ Aₖ   (upshift)   -- "lift" A from mode k to mode m
↓ᵐₖ Aₘ   (downshift) -- "project" A from mode m to mode k
```

These form an **adjunction**: F = ↓ᵐₖ ⊣ U = ↑ᵏₘ

### Key Rules (Sequent Calculus)

```
Downshift Right:
   Γ ⊢ Aₘ
   ─────────────  (where Γ ≥ m)
   Γ ⊢ (↓ᵐₖ A)ₖ

Downshift Left:
   Γ, Aₘ ⊢ Cₚ
   ───────────────
   Γ, (↓ᵐₖ A)ₖ ⊢ Cₚ

Upshift Right:
   Γ ⊢ Aₖ
   ─────────────
   Γ ⊢ (↑ᵏₘ A)ₘ

Upshift Left:
   Γ, Aₖ ⊢ Cₚ
   ───────────────  (where Γ ≥ k)
   Γ, (↑ᵏₘ A)ₘ ⊢ Cₚ
```

### The Comonad and Monad

From the adjunction F ⊣ U:
- **Comonad**: ↓ᵐₖ ↑ᵏₘ A (like □ or !)
- **Monad**: ↑ᵏₘ ↓ᵐₖ A (like ○ or the monad of Moggi's metalanguage)

---

## What Adjoint Logic Unifies

### 1. LNL Decomposition of !

Benton's LNL logic has two modes: `{U, L}` with U > L.

```
F = ↓ᵁₗ : U → L    (Lin: embed intuitionistic into linear)
G = ↑ₗᵁ : L → U    (Mny: extract reusable part)

! A = F(G(A)) = ↓ᵁₗ ↑ₗᵁ A
```

**This is exactly CALC's current implementation!**
- `persistent_ctx` = mode U (Cartesian)
- `linear_ctx` = mode L (Linear)
- `Bang_L` rule = the F modality crossing the boundary

### 2. Intuitionistic S4

Two modes: `{V, U}` with V > U (V = "valid", U = "true").

```
□ A = ↓ᵁᵥ ↑ᵁᵥ Aᵤ   (necessity = comonad)
```

Models Pfenning-Davies' "judgmental S4" where □ A means "A is valid (true in all worlds)."

### 3. Lax Logic

Two modes: `{U, X}` with U > X.

```
○ A = ↑ˣᵤ ↓ˣᵤ Aᵤ   (possibility = monad)
```

Models computational effects: ○ A means "a computation that may produce A."

### 4. Subexponentials

Subexponentials extend linear logic with a **family** of comonads `!ₐ A` indexed by elements of a preorder.

```
Modes = elements of the subexponential index set
m ≥ k means !ₖ A ⊢ !ₘ A
```

Adjoint logic generalizes this by allowing different structural rules per subexponential.

### 5. Session Types (Nomos)

Nomos uses adjoint modes for shared/linear channel discipline:

```
Modes = {shared, linear}  with shared > linear

/\ A = ↑ˢₗ A   (acquire: shared → linear)
\/ A = ↓ˢₗ A   (release: linear → shared)
```

The acquire-release discipline prevents re-entrancy:
1. Client acquires shared channel → gets private linear channel
2. Uses linear channel exclusively
3. Releases back to shared mode

### 6. Bunched Implications

The fibrational framework captures BI (bunched implications):

```
Modes = {cartesian, linear}
Both tensor products (×, ⊗) and both implications (→, ⊸)
Adjoint modalities bridge between them
```

---

## The Fibrational Framework (Licata-Shulman-Riley)

### General Structure

The 2017 framework abstracts common features:

1. **Context descriptors** are terms from a mode theory
2. **Types** are formed from context descriptors
3. **Two general connectives** (positive and negative) manipulate descriptors
4. **Cut/identity admissibility** proven once for the framework

### What It Covers

From the paper:
> "The resulting framework covers many existing connectives: non-associative, ordered, linear, affine, relevant, and cartesian products and implications; bunched logic; n-linear variables; the comonadic □ and linear exponential ! and subexponentials; monadic ♦ and ○; and adjoint logic F and G."

### Key Theorem

**Cut and identity are admissible** for the framework itself, which implies cut admissibility for any logic describable in the framework.

---

## Graded Adjoint Logic

### Combining Grades and Modes

Eades & Orchard (2020) combine adjoint logic with graded modalities:

```
□ᵣ A    (graded necessity, where r is from a semiring)
```

This enables tracking:
- **Exact usage counts**: r ∈ ℕ
- **Sensitivity bounds**: r ∈ ℝ≥0
- **Security levels**: r ∈ {public, secret}
- **Resource quantities**: r ∈ Currencies × Quantities

### Relevance to CALC

For coin quantities, we want:
```
[Alice] coin(BTC, r)   where r : ℝ≥0
```

Graded adjoint logic provides a framework where:
- **Mode** = principal (Alice, Bob, ...)
- **Grade** = quantity
- **Structural rules** depend on both mode and grade

---

## Potential for CALC: Principals as Modes

### The Hypothesis

Could ownership modalities `[Alice] A` be modes in adjoint logic?

```
Modes = {Alice, Bob, shared, ...}

Mode ordering:
  shared ≥ Alice
  shared ≥ Bob
  Alice ⊥ Bob  (incomparable)
```

### What Would Work

**Transfer as mode shift:**
```
[Alice] A ⊸ [Bob] A  ≈  ↓ᴮₛ ↑ᴬₛ A  (via shared intermediate)
```

**Delegation as mode morphism:**
```
Alice speaks for Bob  ≈  Alice ≤ Bob in mode order
```

**Structural rules:**
```
σ(shared) = {W, C}   (shared resources can be copied)
σ(Alice) = {}        (Alice's resources are linear)
```

### What's Missing

**Composite principals:**
```
[Alice ∧ Bob] A = ???
```

Standard adjoint logic doesn't have "products of modes." We'd need:
- Mode tensor: `Alice ⊗ Bob` (both must act)
- Mode sum: `Alice ⊕ Bob` (either can act)

**Authorization reasoning:**
```
(Alice says transfer) ⊢ ???
```

The `says` modality is orthogonal to structural modes. Authorization is about **who affirms**, not **what structural rules apply**.

---

## Assessment: Should Adjoint Logic Be the Unifying Framework?

### What Adjoint Logic Handles Well

| Feature | Adjoint Logic Support |
|---------|----------------------|
| LNL decomposition (!) | ✅ Direct embedding |
| Subexponentials | ✅ Modes as indices |
| Session types (shared/linear) | ✅ Nomos demonstrates |
| S4/lax modalities | ✅ Standard examples |
| Graded types | ✅ Via graded extension |
| Cut elimination | ✅ Generic proof |

### What Adjoint Logic Doesn't Handle Directly

| Feature | Support Level |
|---------|--------------|
| Principal identity (WHO owns) | ⚠️ Modes don't naturally identify principals |
| Composite principals (A ∧ B) | ❌ No mode products |
| Authorization (says, speaks for) | ❌ Different concern |
| Threshold (k-of-n) | ❌ Not expressible |
| Classical linear negation | ⚠️ Primarily intuitionistic |

### Comparison with Alternatives

| Framework | Pros | Cons |
|-----------|------|------|
| **Adjoint Logic** | Generic cut elim, unifies LNL/S4/lax/sessions | No authorization, no composite principals |
| **Multi-Type Display Calculus** | Very general, handles display postulates | Complex, no modes |
| **Authorization Logic** | Principals, says, speaks for | No resource tracking, not substructural |
| **Labelled Sequents** | Very flexible, explicit worlds | Externalized semantics |

---

## Synthesis: A Layered Approach

### Recommendation: Use Adjoint Logic as Foundation, Extend for Authorization

**Layer 1: Adjoint Logic (structural)**
- Handles: linear vs cartesian, resource tracking, grades
- CALC already implements this via persistent_ctx/linear_ctx

**Layer 2: Principal Modes (extension)**
- Add principal-indexed modes: `M_Alice`, `M_Bob`
- Mode morphisms for delegation
- This is **speculative but promising**

**Layer 3: Authorization Logic (orthogonal)**
- `A says φ` is separate from mode structure
- Compose with adjoint logic, don't encode into it
- Keep as separate judgment form

**Layer 4: Consensus (built on top)**
- Composite principals via protocol encoding (not mode products)
- OR extend mode theory with products (research direction)

### Concrete Next Steps for CALC

1. **Document current LNL implementation** as adjoint logic instance
   - Two modes: U (persistent_ctx), L (linear_ctx)
   - Bang_L = F modality

2. **Consider principal modes** as research direction
   - Would modes `M_Alice`, `M_Bob` give clean semantics?
   - What are the mode morphisms? (speaks for?)
   - What structural rules per principal? (all linear?)

3. **Keep authorization separate**
   - `A says φ` is not a mode shift
   - It's an additional judgment form

4. **Study graded adjoint logic** for quantities
   - Could combine principal modes with quantity grades
   - `□ᵣ_Alice A` = "Alice has r units of A"

---

## Key Theorems and Results

### Cut Elimination (Pruiksma et al. 2018)

> "Cut elimination follows straightforwardly by induction on the lexicographically ordered triple (Aₘ, D, E), where D is the proof of the first premise and E is the proof of the second."

### Identity Admissibility (Licata-Shulman 2016)

> "We give a sequent calculus, show that identity and cut are admissible, and define an equational theory on proofs."

### Soundness and Completeness (Licata-Shulman 2016)

> "We show that this syntax is sound and complete for pseudofunctors from the mode 2-category to the 2-category of categories, adjunctions, and adjunction morphisms."

### Fibrational Cut Admissibility (LSR 2017)

> "We prove cut (and identity) admissibility independently of the mode theory, obtaining it for many different logics at once."

---

## Connections to Other CALC Research

### Linear Negation as Debt

From [[linear-negation-debt]]:
- A⊥ = debt/obligation
- Settlement: A ⊗ A⊥ ⊢ 1

**Connection**: Adjoint logic is primarily intuitionistic. For CLL (classical), would need to extend with negation. The fibrational framework might handle this.

### Session Types and Ownership

From [[ownership-as-session-types]]:
- Session types capture protocol, not principal identity
- Recommendation: keep complementary

**Connection**: Adjoint logic's message-passing interpretation (Pruiksma-Pfenning 2021) shows session types ARE adjoint logic. The modes are shared/linear. Principal identity remains separate.

### Consensus Modalities

From [[consensus-modalities-mpst]]:
- `[A ∧ B]` not directly expressible
- Encode as protocol pattern

**Connection**: Adjoint logic doesn't help with composite principals directly. Would need mode products (research direction).

### Algebraic Accounting

From [[algebraic-accounting]]:
- T-accounts as [debit // credit]
- Grothendieck group construction

**Connection**: Graded adjoint logic could track quantities. Mode shifts could model transfers. The accounting equation might emerge from mode invariants.

---

## Research Update: Principal-Indexed Adjoint Operators

### Existing Work: Agent-Indexed Adjoint Pairs

Research by Sadrzadeh & Dyckhoff (2013) demonstrates **agent-indexed families of adjoint pairs**:

> "A simple modal logic whose modalities come in adjoint pairs, but are not in general closure operators. Such logics are useful for encoding and reasoning about information and misinformation in multi-agent systems. We present an algebraic semantics using **lattices with agent-indexed families of adjoint pairs of operators**."

Key features:
- **Left adjoints** express agents' *uncertainties*
- **Right adjoints** express agents' *beliefs*
- **Update rules** encode learning as discarding uncertainty
- Applied to muddy children puzzle with honest/dishonest agents

**Implication**: Agent-indexed adjoint operators are well-founded mathematically!

### Authorization Logic: Principal-Indexed Modalities

Authorization logics extend modal logic with principal-indexed "says" modality:

**IIK (Indexed Intuitionistic K)**: Intuitionistic propositional logic + "K says ·" for each principal K.

**DTL₀**: Relativizes reasoning to beliefs of principals:
- Includes "conceited" axiom: principal believes they believe φ
- Translates to CS4: `A says φ` → `□_A φ`
- Sound and complete for Kripke semantics

**Key insight from Garg (2008)**:
> "In the degenerate case where there is only one principal, the sole modality 'ℓ says A' behaves exactly like the necessitation modality □A from CS4."

### Composite Principals: Established Semantics

From Nexus Authorization Logic (NAL) and standard access control:

**Conjunctive principals (A ∧ B)**:
```
(A ∧ B) says φ  ≡  (A says φ) ∧ (B says φ)
```
Both must affirm. Intersection semantics: belief in worldview of group iff in intersection of member worldviews.

**Disjunctive principals (A ∨ B)**:
```
(A ∨ B) says φ  ≡  (A says φ) ∨ (B says φ)
```
Either suffices. BUT: NAL notes "or-groups are not sound with respect to IMP-E" — requires special rules.

**Delegation (speaks for)**:
```
A speaks for B  ⟺  ∀φ. (A says φ) → (B says φ)
```
Creates transitive authority chains.

### The Two Parallel Structures

| Adjoint Logic | Authorization Logic |
|--------------|---------------------|
| Modes (L, U, S, ...) | Principals (Alice, Bob, ...) |
| Mode preorder (m ≥ k) | Principal hierarchy (speaks for) |
| Structural properties σ(m) | Epistemic properties |
| Adjoint modalities ↑/↓ | Says modality □_A |
| Mode shifts | Authority transfer |

**Key question**: Can these be unified, or are they fundamentally orthogonal?

### Analysis: Why Mode Products Are Hard

In category theory, monoidal categories have tensor products satisfying coherence laws. Adjoint logic's modes form a **preorder** (or 2-category), not a monoidal category.

**The problem with mode tensor products**:
- Preorder has at most one morphism between objects
- Tensor product would need: `m ⊗ n` with morphisms from m, n
- Need associativity: `(m ⊗ n) ⊗ p ≅ m ⊗ (n ⊗ p)`
- Need compatibility with existing mode morphisms

**Possible approaches**:
1. **Extend to symmetric monoidal category of modes** — adds complexity
2. **Use conjunction as a type-former** — `[A ∧ B]` as formula, not mode
3. **Encode via protocol** — both parties act sequentially

### Synthesis: Two-Layer Architecture

Based on this research, the cleanest architecture separates:

**Layer 1: Adjoint Logic (structural properties)**
```
Modes: {U (cartesian), L (linear), S (shared), A (affine), ...}
Morphisms: structural inclusions (U ≥ L, S ≥ L, ...)
Modalities: ↑/↓ for resource management
```

**Layer 2: Principal Index (epistemic properties)**
```
Principals: {Alice, Bob, shared, ...}
Index on formulas: [Alice] A, [Bob] A, [Alice ∧ Bob] A
Delegation: Alice speaks for Bob
Says: Alice says φ
```

**The combination**:
```
[Alice] (↓ᵁₗ A)    -- Alice controls a linear resource lifted from cartesian
(Alice says ↓ᵁₗ A) -- Alice affirms this lifted resource
```

Principal indexing is **orthogonal to** mode indexing — they combine multiplicatively.

---

## Open Questions (Revised)

### 1. Principal Modes — PARTIALLY ANSWERED

**Status**: Agent-indexed adjoint operators exist (Sadrzadeh-Dyckhoff). Authorization logic gives modal semantics (Garg). But direct embedding of principals AS modes remains unexplored.

**Research direction**: Could combine adjoint logic's structural modes with an orthogonal principal index:
```
Aₘ^Alice    -- formula A at mode m, owned by Alice
```

### 2. Mode Products for Consensus — REMAINS OPEN

**Status**: Would require extending mode theory to monoidal structure. No existing work on this for adjoint logic.

**Workaround**: Keep composite principals at formula level:
```
[Alice ∧ Bob] A    -- formula-level composite
```
Rather than:
```
A at mode (Alice ⊗ Bob)    -- mode-level composite (not supported)
```

### 3. Graded Principals — PROMISING DIRECTION

Combine grades and principal index:
```
□ᵣ [Alice] A  =  "Alice has r units of A"
```

**Insight**: Grade is on the comonad, principal is on the formula. They compose naturally.

### 4. Authorization Composition — KEEP SEPARATE

**Recommendation**: Keep `A says φ` as separate judgment form, not encoded into modes.

Two judgment forms:
```
Γ ⊢ A : type      -- standard typing
Γ ⊢ A says φ      -- authorization (different judgment form)
```

This matches Garg et al.'s approach in BL logic family.

### 5. Can Ownership Transfer Be an Adjunction? — ANALYZED

**The question**: Is `[Alice] A ⊸ [Bob] A` an adjunction-derived operation?

**Analysis of existing adjunctions in linear logic:**

| Adjunction | Left Adjoint | Right Adjoint | Effect |
|------------|-------------|---------------|--------|
| LNL (!) | F: Cart → Lin | G: Lin → Cart | Reusability |
| Shared/Linear | acquire | release | Access mode |

**For ownership transfer**:
- Would need functors between "Alice's resources" and "Bob's resources"
- Transfer: T_A→B : Res_Alice → Res_Bob
- What would the adjoint be? T_B→A?

**Issues**:
1. **Non-symmetric**: Transfer from Alice to Bob requires Alice's consent, not Bob's
2. **Linear, not adjoint**: Transfer consumes [Alice] A, creates [Bob] A — this is a morphism, not an adjunction
3. **Modes don't match**: Ownership is an index on formulas, not a mode with structural properties

**Conclusion**: Ownership transfer is NOT an adjunction. It's a **linear implication** (a morphism in the linear category):
```
transfer : [Alice] A ⊸ [Bob] A
```

The ownership modality `[P]` is an **index** (like in indexed categories), not a mode in the adjoint logic sense. The correct categorical picture:

```
Category of CALC proofs
├── Objects: formulas [Alice] A, [Bob] B, ...
├── Morphisms: linear implications
└── Ownership: indexing structure (fibration over principals)
```

**Research direction**: Ownership might be better modeled as a **fibration** over the set of principals, where:
- Base category: Principals
- Fiber over P: Resources owned by P
- Transfer: Reindexing along principal morphisms

---

## Conclusion

**Should adjoint logic be the unifying framework?**

**Yes, as the structural foundation.** Adjoint logic:
- Already underlies CALC's LNL implementation
- Provides generic cut elimination
- Handles session types (via Nomos)
- Extends to graded types (via Eades-Orchard)

**But not as the complete solution.** Adjoint logic doesn't directly handle:
- Principal identity (who owns)
- Authorization reasoning (says, speaks for)
- Composite principals (A ∧ B)

**Recommendation**: Use adjoint logic as Layer 1 (structural), add principal modes as Layer 2 (speculative extension), keep authorization as Layer 3 (orthogonal concern).

The framework is powerful and well-understood. Extending it with principal-indexed modes is a promising research direction that could unify ownership, session types, and resource tracking—while keeping authorization logic as a complementary system.

---

## References

### Core Adjoint Logic Papers
- [Pruiksma et al., "Adjoint Logic" (2018)](http://www.cs.cmu.edu/~fp/papers/adjoint18b.pdf)
- [Licata & Shulman, "Adjoint Logic with a 2-Category of Modes" (2016)](https://link.springer.com/chapter/10.1007/978-3-319-27683-0_16)
- [Licata, Shulman & Riley, "A Fibrational Framework" (FSCD 2017)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.25)
- [Pruiksma & Pfenning, "A Message-Passing Interpretation" (JLAMP 2021)](https://www.sciencedirect.com/science/article/pii/S235222082030122X)

### Agent-Indexed Adjoint Modalities
- [Sadrzadeh & Dyckhoff, "Positive Logic with Adjoint Modalities" (RSL 2013)](https://www.cambridge.org/core/journals/review-of-symbolic-logic/article/abs/positive-logic-with-adjoint-modalities-proof-theory-semantics-and-reasoning-about-information/76D3064EC7F72D25C73452544C23798C)
- [Dyckhoff, Sadrzadeh & Truffaut, "Algebra, proof theory and applications for adjoint modal operators" (TOCL 2013)](https://dl.acm.org/doi/abs/10.1145/2480359.2480362)

### Authorization Logic
- [Garg, "Principal-Centric Reasoning in Constructive Authorization Logic" (2008)](https://apps.dtic.mil/sti/pdfs/ADA506999.pdf)
- [Hirsch & Clarkson, "Belief Semantics of Authorization Logic" (CCS 2013)](https://arxiv.org/abs/1302.2123)
- [Schneider et al., "Nexus Authorization Logic: Design Rationale and Applications"](https://www.cs.cornell.edu/fbs/publications/NexusNalRationale.pdf)

### Foundational
- [Benton, "A Mixed Linear and Non-Linear Logic" (1994)](https://www.researchgate.net/publication/221558077)
- [Reed, "A Judgmental Deconstruction of Modal Logic" (2009)](http://www.cs.cmu.edu/~fp/papers/modal09.pdf)
- [nLab: Adjoint Logic](https://ncatlab.org/nlab/show/adjoint+logic)

### Graded Extensions
- [Eades & Orchard, "Grading Adjoint Logic" (2020)](https://arxiv.org/abs/2006.08854)
- [Hanukaev & Eades, "Combining Dependency, Grades, and Adjoint Logic" (2023)](https://arxiv.org/abs/2307.09563)

### Applications
- [Das et al., "Resource-Aware Session Types for Digital Contracts" (Nomos)](https://arxiv.org/abs/1902.06056)
- [Balzer et al., "Manifest Deadlock-Freedom for Shared Session Types" (ESOP 2019)](https://www.cs.cmu.edu/~fp/papers/esop19.pdf)

### Lecture Notes
- [Pfenning, "Lecture Notes on Adjoint SAX" (15-836, 2023)](https://www.cs.cmu.edu/~fp/courses/15836-f23/lectures/15-adjsax.pdf)
- [Pfenning, "Lecture Notes on Mixed Linear/Nonlinear Logic"](https://www.cs.cmu.edu/~fp/courses/15836-f23/lectures/10-mixed.pdf)

### Related CALC Research
- [[linear-negation-debt]] — A⊥ as debt
- [[ownership-as-session-types]] — Partial correspondence
- [[consensus-modalities-mpst]] — Composite principals
- [[authorization-logic]] — Says, speaks for, controls

---

*Last updated: 2026-01-29*
