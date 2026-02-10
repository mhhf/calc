# Nomos: Session Types + Linear Types for Smart Contracts

> **See also:** [[authorization-logic]] for principals and says modality, [[multi-type-display-calculus]] for adjunctions between modes, [[ownership-as-session-types]] for ownership-channel correspondence, [[graded-resource-tracking]] for resource analysis.

---

## Table of Contents

1. [Overview](#overview)
2. [Propositions-as-Sessions](#the-propositions-as-sessions-correspondence)
3. [Session Type Syntax](#session-type-syntax)
4. [Process Definition Syntax](#process-definition-syntax)
5. [Re-entrancy Prevention](#re-entrancy-prevention-acquire-release-discipline)
6. [Asset Tracking with Linear Types](#asset-tracking-with-linear-types)
7. [Resource-Aware Types: Automatic Gas Analysis](#resource-aware-types-automatic-gas-analysis)
8. [Deadlock Freedom](#deadlock-freedom)
9. [Connection to Authorization Logic](#connection-to-authorization-logic)
10. [Adjoint Logic Foundation](#adjoint-logic-foundation)
11. [Rast: Resource-Aware Session Types](#rast-resource-aware-session-types)
12. [Relevance to CALC](#relevance-to-calc)
13. [Implementation](#implementation)
14. [Key Papers](#key-papers)

---

## Overview

**Nomos** is a domain-specific language for smart contracts developed at CMU by Ankush Das, Stephanie Balzer, Jan Hoffmann, and Frank Pfenning. It combines:
- **Session types** (communication protocols)
- **Linear types** (resource safety)
- **Automatic amortized resource analysis** (gas bounds)

Key paper: Das et al., "Resource-Aware Session Types for Digital Contracts" (CSF 2021)

## Core Problems Nomos Solves

| Problem | Nomos Solution |
|---------|----------------|
| Protocol violations | Session types enforce interaction order |
| Re-entrancy attacks | Acquire-release discipline |
| Asset duplication/loss | Linear type system |
| Out-of-gas exceptions | Automatic resource bounds |

---

## The Propositions-as-Sessions Correspondence

Nomos builds on the **Curry-Howard correspondence for concurrency** discovered by Caires & Pfenning (2010):

| Linear Logic | Session Types | Process Operation |
|--------------|---------------|-------------------|
| A ⊗ B | tensor | Send channel of type A, continue as B |
| A ⊸ B | lolli | Receive channel of type A, continue as B |
| A & B | external choice | Offer choice to client |
| A ⊕ B | internal choice | Make choice as provider |
| 1 | unit | Close channel (termination) |
| !A | exponential | Replicated/persistent service |

**Key insight**: Cut elimination in sequent calculus = Process communication in π-calculus

### Foundational Papers
- Caires & Pfenning, "Session Types as Intuitionistic Linear Propositions" (CONCUR 2010) — 441+ citations
- Wadler, "Propositions as Sessions" (ICFP 2012) — Classical version

---

## Session Type Syntax

```
A ::= +{l₁: A₁, ..., lₙ: Aₙ}     -- internal choice (provider sends label)
    | &{l₁: A₁, ..., lₙ: Aₙ}     -- external choice (provider receives label)
    | A * B                       -- tensor: send channel
    | A -o B                      -- lolli: receive channel
    | 1                           -- termination
    | |{q}> A                     -- send q potential units
    | <{q}| A                     -- receive q potential units
    | /\ A                        -- up-shift: linear → shared
    | \/ A                        -- down-shift: shared → linear
    | t ^ A                       -- send functional value
    | t -> A                      -- receive functional value
```

### Channel Types
- `$c` = Linear channel (must be used exactly once)
- `#c` = Shared channel (acquire-release discipline)

---

## Process Definition Syntax

```
proc <mode> name : (x₁: t₁), ..., ($c₁: A₁), ... |{q}- ($c: A) = P
```

Where:
- `mode` ∈ {`asset`, `contract`, `transaction`}
- `|{q}-` denotes q units of stored potential
- `$c: A` is the offered channel of type A

### Process Operations

```
P ::= $c <- f <- args ; P        -- spawn process f
    | send $c₁ $c₂ ; P           -- send channel c₂ on c₁
    | $c₂ <- recv $c₁ ; P        -- receive channel on c₁
    | $c.label ; P               -- send label on c
    | case $c (l₁ => P₁ | ...)   -- case on received label
    | close $c                    -- close channel
    | wait $c ; P                 -- wait for close
    | work {q} ; P               -- consume q gas
    | pay $c {q} ; P             -- transfer potential
    | get $c {q} ; P             -- receive potential
```

---

## Re-entrancy Prevention: Acquire-Release Discipline

### The DAO Hack (2016)

The infamous DAO attack exploited **re-entrancy**: a malicious contract called back into a withdrawal function before state was updated, draining $60M worth of ETH. This led to the Ethereum hard fork.

The pattern:
1. Attacker calls `withdraw()`
2. Contract sends ETH to attacker
3. Attacker's fallback function calls `withdraw()` again
4. Contract still thinks attacker has balance (state not updated)
5. Repeat until drained

### How Nomos Prevents Re-entrancy

**Shared session types** impose an **acquire-release discipline**:

1. Client must **acquire** shared process before interaction
2. Interaction happens on a **private linear channel**
3. Client must **release** process back to shared state
4. **Equi-synchronizing constraint**: Release type must match acquire type

```
-- Example: Auction contract type
type auction = /\ &{ bid: int -> auction,    -- during bidding
                     close: winner * 1 }      -- end auction

-- A bidder CANNOT:
-- 1. Acquire auction twice without releasing
-- 2. Release in the middle of bidding
-- 3. Re-enter during another client's session
```

### Why Acquire-Release Works

| Property | Mechanism |
|----------|-----------|
| Mutual exclusion | Only one client holds the linear channel at a time |
| State consistency | Must return to same type at release |
| No partial states | Either you have full access or none |
| Type-checked | Violations are compile errors, not runtime errors |

### Equi-synchronizing vs Subsynchronizing

The **equi-synchronizing constraint** requires releasing at exactly the same type as acquired. Later work by Sano, Balzer & Pfenning relaxes this to **subsynchronizing**, allowing phased protocols where types can evolve.

---

## Asset Tracking with Linear Types

Linear types ensure:
- Assets **cannot be duplicated** (no double-spending)
- Assets **cannot be discarded** (no accidental loss)
- Assets can only be **moved** (hence the name of Move language)

### Example: Token Type

```
type token = /\ +{ transfer: address ^ token,
                   burn: 1 }

proc asset tok : |{0}- ($t: token) = {
  $t.transfer ;          -- choose to transfer
  send $t destination ;  -- send destination address
  ...                    -- token moved, cannot use again
}
```

### Comparison with Move Language

| Feature | Nomos | Move |
|---------|-------|------|
| Linear types | Yes | Yes (resources) |
| Session types | Yes | No |
| Re-entrancy prevention | Acquire-release | No dynamic dispatch |
| Protocol enforcement | In types | In bytecode |
| Gas analysis | Automatic | Manual |
| Concurrency model | π-calculus | Sequential |

**Nomos advantage**: Protocols are in the type, not just resource safety
**Move advantage**: Simpler model, wider adoption (Sui, Aptos)

---

## Resource-Aware Types: Automatic Gas Analysis

### The Problem

In Ethereum:
- Every operation costs **gas**
- Users must pay gas upfront
- If gas runs out mid-execution → transaction fails, fee lost
- Estimating gas is difficult

### Nomos Solution: AARA

**Automatic Amortized Resource Analysis** (AARA) statically computes gas bounds:

1. Each process has **potential** (resource budget)
2. Operations consume potential according to cost model
3. Potential can be transferred via channels
4. Type system ensures potential is never negative

### Potential Annotations

```
type list{q} = +{ nil: 1,
                  cons: int ^ |{q}> list{q} }
```

The `|{q}>` annotation means: "send q potential units with this message"

### Automatic Inference

Unknown potentials are **automatically inferred** by the compiler using linear programming (Coin-Or LP solver).

```
type wallet = &{ deposit : |{*}> money -o wallet,    -- * = infer
                 withdraw : <{*}| money * wallet }   -- * = infer
```

---

## Deadlock Freedom

### The Problem with Shared Channels

Acquire-release creates potential for **deadlocks**:
- Process A acquires channel X, waits for Y
- Process B acquires channel Y, waits for X
- Circular dependency → deadlock

### Solution: Manifest Deadlock-Freedom

Balzer et al. (ESOP 2019) add **world ordering** to types:
- Each process resides at a "world" (abstract location)
- Worlds form a partial order
- Processes must acquire resources in ascending order
- This prevents cyclic dependencies

---

## Connection to Authorization Logic

Both Nomos and authorization logic come from the **same CMU/Pfenning research group**.

### Parallel Concepts

| Authorization Logic | Nomos Session Types |
|---------------------|---------------------|
| `A says φ` (principal affirmation) | Process A offers channel of type φ |
| Linear credentials (use once) | Linear channels `$c` |
| Exponential credentials (!A) | Shared channels `#c` |
| `speaks for` delegation | Channel passing |
| `controls` trust | Type-based access control |

### Key Difference

- **Authorization logic**: WHO can make assertions
- **Nomos session types**: WHAT protocol must be followed

### Potential Unification

Could a system combine both?
- Principals as process identities
- `A says φ` as "A offers a channel of type φ"
- `speaks for` as channel delegation
- Linear/exponential for credential consumption
- Session types for interaction protocols

This is an **open research direction**.

---

## Adjoint Logic Foundation

The `/\` (up) and `\/` (down) modalities in Nomos come from **adjoint logic**:

### Background

- **Benton (1994)**: Mixed linear/non-linear calculus with adjunction F ⊣ U
- **Reed (2009)**: Generalized to preorder of modes
- **Licata & Shulman (2015)**: 2-category of modes

### The Adjunction

```
       F
Linear ⟵ ⟶ Non-linear
       U

F: non-linear → linear (forget structure)
U: linear → non-linear (add exponential)
```

The `!A` modality decomposes as: `!A = F(U(A))`

### Connection to Multi-Type Display Calculus

CALC's multi-type display calculus also uses adjunctions! The structural rules come from the counit/unit of adjunctions between modes.

This suggests a **deeper connection** between:
- Authorization modalities (`[A] φ`)
- Session type modalities (`/\`, `\/`)
- Display calculus structural rules

---

## Rast: Resource-Aware Session Types

**Rast** (Das & Pfenning) extends Nomos with:

### Arithmetic Refinements
Session types can include arithmetic constraints:
```
type sorted_list[n] = +{ nil: {n = 0} 1,
                         cons: {n > 0} int ^ sorted_list[n-1] }
```

### Complexity Analysis
- **Ergometric types**: Track sequential complexity (work)
- **Temporal types**: Track parallel complexity (span)

This enables **automatic complexity bounds** on concurrent programs.

---

## Relevance to CALC

### What CALC Can Learn from Nomos

1. **Session types for proof protocols**
   - Proof search as communication protocol
   - Type = proof state transitions allowed

2. **Acquire-release for shared proofs**
   - Multiple agents working on same proof
   - Mutual exclusion for consistency

3. **Resource tracking for proof complexity**
   - Potential annotations for proof length bounds
   - Automatic complexity analysis

4. **Adjoint logic connection**
   - Nomos uses `/\` and `\/` for modality shifts
   - CALC's multi-type display calculus uses adjunctions
   - **Same mathematical structure!**

### Concrete Integration Ideas

1. **Proof channels**: A proof state could be a session type
   ```
   type proof_state = &{ apply_rule: rule -> proof_state,
                         backtrack: proof_state,
                         complete: proof_tree * 1 }
   ```

2. **Authorization + session types**: Combine principals with protocols
   ```
   [Alice] (A says φ) ≈ Alice offers channel of type φ
   ```

3. **Resource-aware proofs**: Track proof search cost
   ```
   type search{q} = |{q}> +{ found: proof, timeout: 1 }
   ```

### Open Questions for CALC

1. **Can ownership modalities be expressed as session types?**
   - `[Alice] A` ≈ "Alice offers a linear channel providing A"?

2. **How do consensus modalities fit?**
   - `[Alice ∧ Bob] A` ≈ Multi-party session types?

3. **What's the right level of integration?**
   - Full session types in CALC?
   - Just borrow concepts (acquire-release, linearity)?
   - Parallel implementation for smart contracts?

4. **Adjoint logic as unifying framework?**
   - Authorization modalities
   - Session type modalities
   - Display calculus structural rules
   - All instances of adjunctions!

---

## Implementation

- **Language**: OCaml
- **Repository**: https://github.com/ankushdas/Nomos
- **Website**: https://nomos-lang.org
- **Type checker**: Linear-time
- **Resource inference**: LP solver (Coin-Or)

### Build
```bash
opam switch create 4.10.0
opam pin add -y nomos .
make
```

### Usage
```bash
# Type check
nomos.exe -tc contract.nom

# Execute with gas tracking
nomos.exe -w send -ts sender -i input.conf -o output.conf contract.nom
```

---

## Key Papers

1. **Das et al. (2021)**: "Resource-Aware Session Types for Digital Contracts" — CSF 2021
2. **Caires & Pfenning (2010)**: "Session Types as Intuitionistic Linear Propositions" — CONCUR 2010
3. **Wadler (2012)**: "Propositions as Sessions" — ICFP 2012
4. **Balzer & Pfenning (2017)**: "Manifest Sharing with Session Types" — OOPSLA 2017
5. **Balzer et al. (2019)**: "Manifest Deadlock-Freedom for Shared Session Types" — ESOP 2019
6. **Das & Pfenning (2022)**: "Rast: A Language for Resource-Aware Session Types" — LMCS 2022
7. **Sano et al. (2021)**: "Manifestly Phased Communication via Shared Session Types" — FoSSaCS 2021

---

## Summary

Nomos demonstrates that:

1. **Linear logic → session types** is a productive Curry-Howard correspondence
2. **Re-entrancy can be prevented by types**, not just runtime checks
3. **Resource bounds can be inferred automatically**
4. **Adjoint modalities unify linear/shared** (relevant for CALC!)

The deep connection to adjoint logic and authorization logic makes Nomos highly relevant to CALC's goals of modeling ownership, consensus, and multi-principal authorization.

---

## Cross-References

- [[authorization-logic]] — "says" modality, principals
- [[multi-type-display-calculus]] — Adjunctions between modes
- [[proof-calculi-foundations]] — Sequent calculus, cut elimination
- [[bibliography]] — Full citations

---

*Last updated: 2026-01-28*
