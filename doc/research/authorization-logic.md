# Authorization Logic: Deep Research

This document covers the theory and practice of authorization logics, particularly their connection to linear logic and relevance to CALC's ownership/consensus modality goals.

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [The "Says" Modality](#the-says-modality)
3. [Garg et al.'s Linear Authorization Logic](#garg-et-als-linear-authorization-logic)
4. [The BL Family of Authorization Logics](#the-bl-family-of-authorization-logics)
5. [Key Authorization Concepts](#key-authorization-concepts)
6. [Composite Principals and Thresholds](#composite-principals-and-thresholds)
7. [Connection to CALC](#connection-to-calc)
8. [Related Systems](#related-systems)
9. [Open Problems and Our Contribution](#open-problems-and-our-contribution)
10. [Sources](#sources)

---

## Executive Summary

**Core Insight:** Authorization logic combines modal logic with access control. The `A says φ` modality expresses that principal A affirms proposition φ. Combined with linear logic, this enables modeling of **consumable credentials** (one-time authorizations) vs **reusable credentials** (permanent permissions).

**Why This Matters for CALC:**

| Authorization Concept | CALC Analog | Status |
|-----------------------|-------------|--------|
| `A says φ` (affirmation) | `[Alice] A` (ownership modality) | Goal |
| Linear affirmation (consumable) | `linear_ctx` | ✓ Implemented |
| Exponential affirmation (reusable) | `persistent_ctx` | ✓ Implemented |
| `A speaks for B` (delegation) | Mode hierarchy in adjoint logic | Goal |
| Composite principals (`A ∧ B`) | Multi-sig modalities | Goal |
| Threshold (`k-of-n`) | Weighted voting modalities | Goal |

**Key Papers:**
- Garg et al. (2006): Linear Logic of Authorization and Knowledge
- Garg (2009): Proof Theory for Authorization Logic (PhD thesis)
- Garg & Pfenning (2011): Stateful Authorization Logic
- Garg & Abadi (2008): Modal Deconstruction of Access Control Logics

---

## The "Says" Modality

### Origin: ABLP Logic

The foundational authorization logic is **ABLP** (Abadi, Burrows, Lampson, Plotkin, 1993):

```
A says φ     -- Principal A affirms/supports φ
A controls φ -- Abbreviation for (A says φ) → φ
A speaks for B -- If A says φ then B says φ (delegation)
```

### Intuition

- `A says φ` means A believes φ is true or authorizes actions based on φ
- It's a modal operator indexed by principal A
- Multiple principals have independent "says" modalities
- This is **subjective** — different principals can disagree

### Proof Rules (Natural Deduction)

```
    Γ ⊢ φ                     Γ ⊢ A says φ    Γ, A says φ ⊢ ψ
  ─────────── (says-I)       ─────────────────────────────────── (says-E)
  Γ ⊢ A says φ                           Γ ⊢ ψ
```

The introduction rule is strong: if φ is universally true, then any principal says it.
The elimination requires using the statement in a context that expects it.

### Connection to Modal Logic

Garg & Abadi (2008) showed that authorization logics translate to **modal S4**:
- `A says φ` behaves like `□_A φ` (necessity indexed by principal A)
- Constructive (intuitionistic) base logic
- The translation is sound and complete

---

## Garg et al.'s Linear Authorization Logic

### The Key Innovation (ESORICS 2006)

**Problem:** Standard authorization logics treat credentials as reusable. But some authorizations should be **consumable** — use once, then invalid.

**Solution:** Combine authorization modalities with linear logic:
- **Linear affirmations**: One-time credentials (consumed on use)
- **Exponential affirmations**: Reusable credentials (use unlimited times)

### The Three Dimensions

```
              Affirmation    Knowledge    Linearity
              ───────────    ─────────    ─────────
Use Case      Authorization  Info flow    Resource tracking
Modality      A says φ       K knows φ    ⊗, ⊸, !
Consumption   Yes            No           Yes
```

### Syntax

```
φ ::= p | φ ⊗ φ | φ ⊸ φ | !φ | A says φ | K knows φ | ...
```

- Standard linear logic connectives (⊗, ⊸, !, &, ⊕)
- Authorization modality: `A says φ`
- Knowledge modality: `K knows φ`

### Key Inference Rules

**Linear Says (consumable credential):**
```
Γ ⊢ A says φ    Δ, φ ⊢ ψ
───────────────────────── (says-L linear)
      Γ, Δ ⊢ ψ
```
The credential `A says φ` is consumed — Γ doesn't include it in conclusion.

**Exponential Says (reusable credential):**
```
!Γ ⊢ A says φ    !Δ, !φ ⊢ ψ
────────────────────────────── (says-L exponential)
        !Γ, !Δ ⊢ ψ
```
The credential can be used repeatedly.

### Cut Elimination

The logic satisfies cut elimination — crucial for:
- Soundness (no inconsistencies)
- Proof search (subformula property)
- Compositional reasoning

---

## The BL Family of Authorization Logics

Garg's thesis (2009) develops a hierarchy of authorization logics:

### BL0: Core Authorization Logic

- Sorted first-order intuitionistic logic
- Principal-indexed modality `k says s`
- No state, no time

```
BL0 judgment: K · ⊢ A
              ↑     ↑
           view   formula
```

The "view" K tracks which principal's perspective we're reasoning from.

### BL1: With State Predicates

Adds **interpreted predicates** for system state:
- File permissions
- Time of day
- Access control lists

State can change non-deterministically between derivation steps.

### BL (Full): With Explicit Time

Adds temporal connective:
```
s @ [u1, u2]    -- s holds during time interval [u1, u2]
```

Enables reasoning about:
- Credential expiration
- Time-limited permissions
- Audit trails

### BLL: Linear Extension

Combines BL with linear logic for consumable resources:
- Linear credentials (one-time use)
- Resource consumption
- Token-based access

**This is the most relevant variant for CALC.**

### Kripke Semantics

All BL variants have Kripke semantics:
- Possible worlds W
- Accessibility relations R_k for each principal k
- **Views** θ(w) = set of principals who can see world w
- Truth: `w ⊩ k says φ` iff `∀v. wR_k v → v ⊩ φ`

---

## Key Authorization Concepts

### Delegation: "Speaks For"

```
A speaks for B    -- A can act on B's behalf
                  -- If A says φ, then B says φ
```

**Intuition:** When A speaks for B, anything A says is automatically also said by B. It's like A has been given power of attorney to make statements on B's behalf.

**Simple Examples:**

**Example 1: SSH Key Authentication**
```
my_ssh_key speaks for Alice
```
When I authenticate with my SSH key, the system treats it as if Alice herself authenticated. The key "speaks for" me.

```
my_ssh_key says "open session"
─────────────────────────────── (speaks for)
Alice says "open session"
```

**Example 2: Corporate Hierarchy**
```
CEO speaks for Company
CFO speaks for Company (for financial matters)
```
When the CEO signs a contract, it's as if the Company signed it. The CEO speaks for the Company.

```
CEO says "approve merger"
─────────────────────────── (speaks for)
Company says "approve merger"
```

**Example 3: Delegation Chain**
```
Alice speaks for Admin
Admin speaks for Root
```
This creates a chain: if Alice says something, Admin says it, and therefore Root says it too.

```
Alice says φ
────────────── (Alice speaks for Admin)
Admin says φ
────────────── (Admin speaks for Root)
Root says φ
```

**Example 4: Smart Contract Proxy**
```
proxy_contract speaks for user_wallet
```
A proxy contract can execute transactions as if the user's wallet executed them directly.

**Key Properties:**

1. **Transitivity:** If A speaks for B, and B speaks for C, then A speaks for C
2. **Reflexivity:** A speaks for A (trivially)
3. **NOT symmetric:** A speaks for B does NOT imply B speaks for A

**Formal Definition:**
```
speaks_for(A, B) ≡ ∀φ. (A says φ) → (B says φ)
```

This requires **second-order quantification** in general (quantifying over all formulas), but can be restricted to decidable fragments.

**Restricted Delegation:**
In practice, delegation is often limited:
```
A speaks for B on topic T    -- A can only speak for B about T
```
Example: "CFO speaks for Company on financial matters" but not on hiring decisions.

### Trust: "Controls"

```
A controls φ    -- A is authoritative about φ
                -- Abbreviation for (A says φ) → φ
```

If A controls φ and A says φ, then φ is objectively true.

### Composite Principals

ABLP and successors support combining principals in modalities:

| Composite | Meaning | Example |
|-----------|---------|---------|
| `[A ∧ B] φ` | Both A and B affirm φ | Multi-signature: both must sign |
| `[A ∨ B] φ` | Either A or B affirms φ | Either party can authorize |
| `[A │ B] φ` | A quoting B | "A says that B says φ" |
| `[A as R] φ` | A acting in role R | Alice as Admin |

**Simple Examples:**

```
[Alice ∧ Bob] transfer(100, to: Charlie)
-- Both Alice AND Bob must approve this transfer (multi-sig)

[Alice ∨ Bob] unlock(door)
-- Either Alice OR Bob can unlock the door

[Alice as Admin] delete(file)
-- Alice, acting in her Admin role, can delete
```

**For CALC:** We start with simple `[A]` ownership, then add `[A ∧ B]` and `[A ∨ B]`. More complex consensus (thresholds, weights) comes later.

### Threshold Structures (Future Extension)

**Delegation Logic (Li et al.)** introduced k-of-n thresholds:

```
[2-of-{A, B, C}] φ    -- Any 2 of the 3 principals suffice
```

**Problem:** Without native support, threshold expands to disjunction of conjunctions:
```
[2-of-{A,B,C}] φ  =  [(A ∧ B) ∨ (A ∧ C) ∨ (B ∧ C)] φ
```

For k-of-n, this is C(n,k) combinations — exponential in worst case.

**Future goal:** Native threshold and weighted consensus support, but start simple with `∧` and `∨`.

---

## Composite Principals and Thresholds

> **See also:** [[consensus-modalities-mpst]] for threshold limitations and alternatives.

### What Exists

| System | Conjunction | Disjunction | Threshold | Weights |
|--------|-------------|-------------|-----------|---------|
| ABLP | ✓ | ✓ | ✗ | ✗ |
| D1LP | ✓ | Limited | ✓ | ✗ |
| NAL | ✓ | ✓ | ✓ (unweighted) | ✗ |
| DKAL | ✓ | ✗ | ✗ | ✗ |

### What Doesn't Exist (Our Opportunity)

No existing system handles:
- **Weighted voting**: `[Alice:0.3, Bob:0.7, threshold:0.5] φ`
- **Proof of Work**: `[PoW(nonce, difficulty)] φ`
- **Proof of Stake**: `[Stake(Alice, amount)] φ`

These require:
1. Graded modalities (semiring quantities)
2. Composite principal operations
3. Threshold predicates
4. Computational verification

**This is CALC's potential contribution!**

---

## Connection to CALC

> **See also:** [[ownership-design]] for ownership modality design, `dev/ownership-authorization-plan.md` for implementation planning.

---

## Related Systems

### Nomos (CMU)

**What:** Language for digital contracts with session types + linear types.

**Relevance:**
- Models digital assets as linear resources
- Session types for contract protocols
- Prevents re-entrancy via acquire-release discipline
- Authors overlap with authorization logic group (Pfenning, Das)

**Key Insight:** Linear types ensure assets aren't duplicated. This is exactly our `linear_ctx`.

### Move Language (Sui/Aptos)

**What:** Smart contract language with resource types.

**Relevance:**
- Resources can't be copied or dropped
- First-class representation of ownership
- Practical implementation of linear types for blockchain

### Session Types

**What:** Types for communication protocols.

**Connection:** Session types are the computational interpretation of linear logic (Caires & Pfenning, 2010). Authorization can be viewed as a session between principal and resource.

---

## Sources

### Foundational Papers

- [ABLP (1993): A Calculus for Access Control in Distributed Systems](https://www.researchgate.net/publication/220404387_A_Calculus_for_Access_Control_in_Distributed_Systems) — Original "says" logic
- [Garg et al. (2006): A Linear Logic of Authorization and Knowledge](https://link.springer.com/chapter/10.1007/11863908_19) — **Key paper** combining linear logic with authorization

### Garg's Work

- [Garg (2009): Proof Theory for Authorization Logic](https://www.cs.cmu.edu/~rwh/students/garg.pdf) — PhD thesis, comprehensive treatment
- [Garg & Pfenning (2011): Stateful Authorization Logic](https://people.mpi-sws.org/~dg/papers/jcs12.pdf) — Adds state predicates
- [Garg & Abadi (2008): Modal Deconstruction of Access Control Logics](https://link.springer.com/chapter/10.1007/978-3-540-78499-9_16) — Translation to S4

### Delegation and Thresholds

- [Li et al. (2003): Delegation Logic](http://cs-www.cs.yale.edu/homes/jf/Ninghui-thesis.pdf) — k-of-n thresholds
- [NAL: Nexus Authorization Logic](https://www.cs.cornell.edu/fbs/publications/NexusNalRationale.pdf) — Dynamic principals

### Related Systems

- [Nomos (2021): Resource-Aware Session Types for Digital Contracts](https://www.cs.cmu.edu/~balzers/publications/nomos.pdf) — Linear types for smart contracts
- [Abadi: Logic in Access Control (Tutorial)](https://users.soe.ucsc.edu/~abadi/Papers/fosad-acllogic.pdf) — Overview

### Cross-References

See also in this knowledge base:
- [[multi-type-display-calculus]] — Our framework for ownership modalities
- [[proof-calculi-foundations]] — Hierarchy of proof systems
- [[RESEARCH]] — Project goals including blockchain modeling
- [[nomos]] — Linear types for blockchain (separate doc)

---

*Last updated: 2026-02-10*
