# Nomos: Blockchain Smart Contracts with Linear Types

A comprehensive research document on Nomos, a programming language for digital contracts based on resource-aware session types.

---

## Table of Contents

1. [Overview](#overview)
2. [Theoretical Foundations](#theoretical-foundations)
3. [Key Features](#key-features)
4. [Type System](#type-system)
5. [Resource Analysis](#resource-analysis)
6. [Relationship to Linear Logic](#relationship-to-linear-logic)
7. [Implementation](#implementation)
8. [Relevance to CALC](#relevance-to-calc)
9. [Sources](#sources)

---

## Overview

**Nomos** is a domain-specific programming language for implementing smart contracts, developed at Carnegie Mellon University by Ankush Das, Stephanie Balzer, Jan Hoffmann, and Frank Pfenning.

### The Problem It Solves

Smart contracts face three critical challenges:

| Challenge | Description | Nomos Solution |
|-----------|-------------|----------------|
| **Protocol Enforcement** | Contracts must follow interaction protocols | Session types |
| **Resource Control** | Gas costs must be bounded | Resource-aware types |
| **Asset Safety** | Assets cannot be duplicated/deleted | Linear types |

### Key Insight

Nomos combines three type-theoretic techniques:
1. **Session types** — prescribe bidirectional communication protocols
2. **Linear types** — prevent asset duplication/deletion
3. **Automatic amortized resource analysis** — statically bound gas consumption

---

## Theoretical Foundations

### Session Types and Curry-Howard

Session types are in **Curry-Howard correspondence with linear logic**:

```
Linear Logic          Session Types
─────────────         ─────────────
A ⊗ B                 Send A, then behave as B
A ⊸ B                 Receive A, then behave as B
A & B                 External choice (client chooses)
A ⊕ B                 Internal choice (server chooses)
!A                    Shared/reusable channel
```

Under this correspondence:
- **Propositions** = session types (protocols)
- **Proofs** = processes (implementations)
- **Cut elimination** = communication

### Linear Logic as Resource Logic

Linear logic's key property: propositions are **resources** that must be used exactly once.

In Nomos:
- A linear asset cannot be copied (no contraction)
- A linear asset cannot be discarded (no weakening)
- This prevents the "double spending" problem in blockchain

---

## Key Features

### 1. Protocol Enforcement via Session Types

Session types describe communication protocols. A channel has a type describing what messages can be sent/received.

```
type wallet = &{ deposit : money -o wallet,
                 withdraw : money * wallet,
                 balance : int ^ wallet }
```

This says a wallet:
- Can receive a `deposit` (takes money, continues as wallet)
- Can be asked to `withdraw` (sends money and continues)
- Can report `balance` (sends int and continues)

### 2. Linear Asset Tracking

Assets are tracked linearly:

```
type money = { amount : int }

-- This would be a TYPE ERROR:
proc bad_double(m : money) : money * money =
  (m, m)  -- ERROR: can't use m twice!
```

### 3. Shared vs Linear Channels

Nomos distinguishes:
- **Linear channels** (`$c`) — must be used exactly once
- **Shared channels** (`#c`) — can be used multiple times (like `!A`)

Mode shifts move between them:
- `↑` (up) — acquire shared channel for linear use
- `↓` (down) — release linear channel back to shared

### 4. Process Modes

Processes have modes indicating their role:

| Mode | Description |
|------|-------------|
| `R` (asset) | Purely linear processes for assets/private data |
| `S` (shared) | Shareable contracts in shared phase |
| `L` (linear) | Shareable contracts in linear phase |
| `T` (transaction) | Transaction processes issued by users |

---

## Type System

### Session Type Operators

```
Type        Meaning
────        ───────
+{l : A}    Internal choice: send label l, continue as A
&{l : A}    External choice: receive label l, continue as A
A ⊗ B       Send channel of type A, continue as B
A ⊸ B       Receive channel of type A, continue as B
↑A          Acquire (shift from shared to linear)
↓A          Release (shift from linear to shared)
1           Terminate (unit)
```

### Example: Auction Contract

```
type auction = &{ bid : money -o auction,
                  close : +{ winner : money * 1,
                             no_bids : 1 } }
```

An auction:
1. Accepts bids (external choice `&`)
2. When closed, either declares winner (sends prize) or reports no bids

### Type Checking

Nomos features **linear-time type checking** — the type checker runs in O(n) where n is program size.

---

## Resource Analysis

### The Gas Problem

In Ethereum and similar blockchains:
- Every operation costs **gas**
- Users must pay gas upfront
- If gas runs out mid-execution, transaction fails and fee is lost

### Automatic Amortized Resource Analysis (AARA)

Nomos uses AARA to **statically compute gas bounds**:

1. Each process is assigned an initial **potential** (budget)
2. Operations consume potential according to a cost model
3. Potential can be transferred between processes
4. Type system ensures potential is never negative

```
|{q}> A     -- Send with potential q
<{q}| A     -- Receive with potential q
```

### Example: Resource-Annotated Type

```
type wallet = &{ deposit : |{2}> money -o wallet,
                 withdraw : <{5}| money * wallet }
```

- Depositing costs 2 gas units (sender provides)
- Withdrawing provides 5 gas units (to receiver)

### Inference

Unknown potentials marked with `*` are **automatically inferred** by the compiler using an LP solver.

---

## Relationship to Linear Logic

### The Curry-Howard Correspondence

| Linear Logic | Session Types | Process Calculus |
|--------------|---------------|------------------|
| A ⊗ B | A ⊗ B | send c (channel of A); continue as B |
| A ⊸ B | A ⊸ B | receive c (channel of A); continue as B |
| A & B | &{...} | offer choice to client |
| A ⊕ B | +{...} | make choice |
| !A | shared channel | reusable/contractible |
| 1 | close | terminate |

### Cut = Communication

In Nomos, **cut elimination corresponds to message passing**:

```
Cut rule:    Γ ⊢ A    A, Δ ⊢ C
             ─────────────────
                 Γ, Δ ⊢ C

Process:     P provides A    Q uses A
             ─────────────────────────
             P || Q  (parallel composition)
```

When P sends on A and Q receives on A, this is cut reduction.

### Linearity Ensures Safety

Because the type system is based on linear logic:
- **No duplication** — assets can't be copied (no contraction)
- **No deletion** — assets can't vanish (no weakening)
- **Protocol compliance** — communication follows session types

---

## Implementation

### Architecture

Nomos is implemented in **OCaml** (~43% of codebase).

```
nomos/           -- Core language implementation
├── type/        -- Type checking
├── resource/    -- Resource analysis (AARA)
├── exec/        -- Execution engine
└── solver/      -- LP solver interface for inference

rast/            -- Related system (arithmetic refinements)
nomos-tests/     -- Test suite (wallet examples)
```

### Build System

```bash
# Dependencies
opam install dune menhir ...

# Build
dune build

# Run
_build/default/nomos-bin/nomos.exe <file>
```

### Example: Wallet System

The test suite demonstrates:
1. Account creation with gas management
2. Multi-wallet initialization
3. Fund transfers
4. Balance queries with automatic gas deduction

---

## Relevance to CALC

### What CALC Can Learn from Nomos

| Nomos Feature | CALC Application |
|---------------|------------------|
| Session types from linear logic | Our proof search is already LL-based |
| Resource analysis | Could track quantities (not just linearity) |
| Shared/linear distinction | Like ! modality decomposition |
| Process modes | Structural vs logical connectives? |

### Key Differences

| Aspect | Nomos | CALC |
|--------|-------|------|
| **Purpose** | Type programs | Search for proofs |
| **Focus** | Runtime resource bounds | Proof construction |
| **Approach** | Type checking | Proof search (backchaining) |
| **Implementation** | Session-typed processes | Sequent calculus |

### Potential Integration

1. **Nomos as target**: Generate Nomos programs from CALC proofs?
2. **Resource annotations**: Add AARA-style potential to our sequents?
3. **Shared/linear**: Our ! handling could inform Nomos-style modes

### The Bigger Picture

Both Nomos and CALC are exploring the same Curry-Howard space:

```
        Logic                    Computation
        ─────                    ───────────
CALC:   Linear logic proofs  →   ???
Nomos:  Linear logic types   →   Session-typed processes
```

CALC focuses on the **proof search** side; Nomos focuses on the **program execution** side. They could potentially meet in the middle.

---

## Sources

### Primary Papers

- **Das et al. (2019)**: [Resource-Aware Session Types for Digital Contracts](https://arxiv.org/abs/1902.06056) — CSF 2021
- **Das et al. (2021)**: [Nomos: A Protocol-Enforcing, Asset-Tracking, and Gas-Aware Smart Contract Language](https://www.cs.cmu.edu/~janh/assets/pdf/DasHP21.pdf)
- **Das & Pfenning (2020)**: [Session Types with Arithmetic Refinements](https://arxiv.org/abs/2001.04439)

### Related Work

- **Caires & Pfenning (2010)**: Session types from intuitionistic linear logic
- **Wadler (2012)**: [Propositions as Sessions](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf) — Classical linear logic version
- **Toninho et al. (2013)**: [Linear Logic Propositions as Session Types](https://www.cs.cmu.edu/~fp/papers/mscs13.pdf)

### Implementation

- **GitHub**: https://github.com/ankushdas/Nomos
- **Ankush Das Homepage**: https://ankushdas.github.io/
- **Jan Hoffmann's Nomos Page**: https://www.cs.cmu.edu/~janh/projects/02_nomos/

## Cross-References

See also in this knowledge base:
- [[QTT]] — Quantitative type theory (different approach to resource tracking)
- [[residuation]] — Why session types work (residuation in linear logic)
- [[exponential-display-problem]] — Shared channels relate to ! decomposition
- [[bibliography]] — Full citations

---

*Last updated: 2026-01-27*
