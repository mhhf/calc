# Ownership Modalities as Session Types

This document explores whether ownership modalities (`[Alice] A`) can be expressed as session types, connecting authorization logic with the propositions-as-sessions correspondence.

---

## The Core Question

Can we express:
```
[Alice] A     -- "Alice owns/controls A"
```

In terms of session types? Specifically:
```
[Alice] A  ≈  "Alice offers a linear channel providing A"  ?
```

---

## Background: Two Correspondences

### 1. Propositions-as-Sessions (Caires-Pfenning-Wadler)

Linear logic corresponds to session-typed π-calculus:

| Linear Logic | Session Type | Process Operation |
|--------------|--------------|-------------------|
| A ⊗ B | Output | Send channel of type A, continue as B |
| A ⊸ B (= A⊥ ⅋ B) | Input | Receive channel of type A, continue as B |
| A & B | External choice | Offer choice to client |
| A ⊕ B | Internal choice | Make choice |
| 1 | Close | Terminate channel |
| !A | Server | Replicated service (multiple clients) |
| ?A | Client | Connect to server |

**Key insight**: Cut elimination = process communication.

### 2. Authorization Logic (Garg-Pfenning)

Authorization logic extends linear logic with principals:

| Authorization | Meaning |
|---------------|---------|
| `A says φ` | Principal A affirms φ |
| `A controls φ` | `(A says φ) → φ` |
| `A speaks for B` | If A says φ then B says φ |
| Linear `says` | One-time authorization (consumed) |
| `!(A says φ)` | Standing authorization (reusable) |

---

## Attempting the Correspondence

### Hypothesis A: Ownership = Channel Provision

```
[Alice] A  ≈  "Alice provides a linear channel of type A"
```

Under this reading:
- Alice is a **process** that offers a channel
- A is the **session type** of that channel
- Owning A means being able to communicate A's protocol

**Problem**: This conflates "Alice" (a principal/entity) with a process. In session types, there's no notion of "who" provides a channel — just the channel's type.

### Hypothesis B: Ownership = Named Channel

```
[Alice] A  ≈  "Channel c_Alice has type A"
```

Under this reading:
- Each principal has an associated channel
- `[Alice] A` means Alice's channel carries type A
- `[Bob] A` means Bob's channel carries type A

**Problem**: Session types don't natively have "named" channels indexed by principals. Channels are anonymous.

### Hypothesis C: Ownership = Mode in Adjoint Logic

Pruiksma & Pfenning's adjoint session types introduce **modes**:

```
Modes = { linear, affine, shared, ... }
```

Each mode has structural properties (weakening, contraction). Adjunctions mediate between modes.

**Potential mapping:**
```
[Alice]  ≈  Mode "Alice" with specific structural rules
[Alice] A  ≈  Formula A at mode "Alice"
```

Under this reading:
- Principals are modes
- Different principals have different structural rules
- Moving from `[Alice] A` to `[Bob] A` requires a mode shift (adjunction)

**This is promising!** But Pfenning's adjoint logic doesn't have principals as modes — it has structural modes (linear, affine, etc.).

---

## What Session Types DO Capture

### 1. Channel Ownership via Linearity

Session types enforce that each channel has exactly one owner (endpoint):

```
c : A      -- This process owns the "positive" endpoint
c : A⊥     -- The dual process owns the "negative" endpoint
```

Linearity ensures channels aren't duplicated or discarded.

**Connection to CALC**: Our `[Alice] coin(BTC, q)` similarly ensures Alice's coin isn't duplicated.

### 2. Ownership Transfer via Delegation

In session types, channel ownership can be transferred:

```
send c d   -- Send channel d over channel c
           -- Receiver now owns d
```

This is **delegation**: the sender gives up ownership of d.

**Connection to CALC**: This is like `[Alice] A ⊸ [Bob] A` (transfer from Alice to Bob).

### 3. Acquire-Release for Shared Resources

Nomos's shared session types use acquire-release:

```
/\ A     -- Up-shift: linear → shared
\/ A     -- Down-shift: shared → linear (acquire)
```

A client must **acquire** a shared channel before using it (getting a private linear channel), then **release** it.

**Connection to CALC**: This models "taking control" of a shared resource — like gaining ownership temporarily.

---

## What Session Types DON'T Capture

### 1. Principal Identity

Session types don't distinguish WHO owns a channel — just that someone does.

```
c : A    -- Someone has this channel
```

There's no syntax for:
```
c : A owned_by Alice    -- NOT standard session types
```

### 2. Multi-Principal Statements

Session types can't directly express:
```
[Alice ∧ Bob] A   -- Both Alice and Bob must consent
[Alice ∨ Bob] A   -- Either Alice or Bob can act
```

**Multiparty session types** have multiple participants, but participation is determined by the protocol (global type), not by ownership modalities.

### 3. Authorization / "Says"

Session types model WHAT protocol to follow, not WHO is authorized.

```
A says transfer(B, x)   -- NOT expressible in session types
```

Authorization logic's `says` modality is orthogonal to session types.

---

## Possible Synthesis: Three Approaches

### Approach 1: Principals as Process Names

```
proc Alice : ... |{q}- ($c : A) = P
proc Bob : ... |{q}- ($c : B) = Q
```

Each principal is a **named process** that offers certain session types.

**Interpretation:**
```
[Alice] A  =  proc Alice : ... |{q}- ($c : A)
```

**Limitation**: Processes are programs, not logical entities. Can't reason about them modally.

### Approach 2: Principals as Modes (Adjoint Extension)

Extend Pfenning's adjoint logic with principal-indexed modes:

```
Modes = { M_Alice, M_Bob, M_shared, ... }

Adjunctions:
  F_AB : M_Alice → M_Bob    (transfer from Alice to Bob)
  U_BA : M_Bob → M_Alice    (right adjoint)
```

**Interpretation:**
```
[Alice] A  =  A at mode M_Alice
[Bob] A    =  A at mode M_Bob

Transfer:
  F_AB([Alice] A) = [Bob] A
```

**Benefit**: Adjoint logic already handles mode shifts. This adds principal-indexed modes.

**Open question**: What are the adjunctions between principal modes? What structural rules do they have?

### Approach 3: Ownership as Channel Endpoint Assignment

Introduce a judgment assigning channel endpoints to principals:

```
Alice owns c+     -- Alice owns positive endpoint of c
Bob owns c-       -- Bob owns negative endpoint of c
```

The session type of c is then "split" between Alice and Bob:
```
c : A      (Alice's view)
c : A⊥     (Bob's view)
```

**Interpretation:**
```
[Alice] A  =  Alice owns a channel of type A (positive)
[Bob] A⊥   =  Bob has a claim on A (negative = debt)
```

**Benefit**: Connects to our debt semantics! If `A⊥` = debt, then:
- `[Alice] coin(BTC, q)` = Alice owns the positive endpoint
- `[Bob] coin(BTC, q)⊥` = Bob has a claim (negative endpoint)

Settlement = connecting the endpoints (cut/communication).

---

## Connection to MPST and Global Types

Multiparty session types (MPST) have **roles** (participants):

```
global type G =
  Alice → Bob : transfer {
    ok: Bob → Alice : ack.end,
    fail: end
  }
```

Roles in MPST are like principals! But:
- Roles are determined by the **global type** (protocol designer)
- Projection gives each role a **local type**
- There's no "ownership modality" — just protocol compliance

**Potential synthesis:**
```
[Alice] A  =  Alice's local type for resource A
```

The global type specifies how Alice's and Bob's local types interact.

---

## Comparison Table

| Feature | Authorization Logic | Session Types | Can Express? |
|---------|---------------------|---------------|--------------|
| Principal identity | `A says φ` | (no equivalent) | ❌ |
| Resource ownership | `[A] φ` | Linear channel | ✓ (partial) |
| One-time credential | Linear `says` | Linear channel | ✓ |
| Standing permission | `!(A says φ)` | `!A` (server) | ✓ |
| Delegation | `speaks for` | Channel passing | ✓ |
| Multi-sig | `A ∧ B` | (no direct equivalent) | ❌ |
| Protocol compliance | (not native) | Session types | ✓ |
| Deadlock freedom | (not native) | Cut elimination | ✓ |

---

## Conclusions

### 1. Partial Correspondence

Ownership modalities and session types have significant overlap:

| Shared Concept | Auth Logic | Session Types |
|----------------|------------|---------------|
| Linear resources | ✓ | ✓ |
| Ownership transfer | `speaks for` / transfer | Delegation |
| One-time vs reusable | Linear / exponential | Linear / `!` |

### 2. The Gap: Principal Identity

The key missing piece is **who** owns something. Session types track **that** a channel is owned (linearity) but not **by whom**.

### 3. Possible Unifications

Three approaches to bridge the gap:

| Approach | Mechanism | Difficulty |
|----------|-----------|------------|
| Principals as processes | Named processes | Low (but limited) |
| Principals as modes | Adjoint logic extension | Medium |
| Endpoint assignment | Judgment `A owns c` | Medium |

### 4. Recommendation for CALC

**Don't try to reduce ownership to session types.** Instead:

1. Keep `[Alice] A` as a primitive ownership modality
2. Use session types for **protocol** (what operations are valid)
3. Use authorization logic for **principals** (who can act)
4. Connect via: "Alice owns a channel that implements protocol P"

This parallels Nomos's design: processes have types (session types) AND identities (process names).

---

## Open Questions

### 1. Adjoint Logic with Principal Modes

Can we extend Pfenning's adjoint logic with principal-indexed modes?

```
Modes = { M_Alice, M_Bob, M_shared }
M_Alice ≤ M_shared    -- Alice's resources can be shared
```

What adjunctions make sense between principals?

### 2. Consensus as Synchronization

Could `[A ∧ B] A` (both must consent) be expressed as:
- A synchronization point in a session?
- A join in multiparty session types?

### 3. Global Types as Policies

Could authorization policies be expressed as global types?

```
Policy: Alice can transfer to Bob iff Bob acknowledges
Global type: Alice → Bob : transfer. Bob → Alice : ack
```

### 4. Channel Passing = `speaks for`?

When Alice sends a channel to Bob (delegation), does this correspond to `Alice speaks for Bob` (Bob can now act as Alice on that channel)?

---

## Summary

**Can ownership modalities be expressed as session types?**

**Partially.** The core features overlap:
- Linear resources
- Ownership transfer (delegation)
- One-time vs reusable

**But** session types lack:
- Principal identity (WHO owns)
- Multi-sig / consensus modalities
- Authorization reasoning (says, controls)

**Recommendation**: Keep them as complementary systems:
- **Session types** for protocol/communication
- **Ownership modalities** for principals/authorization
- **Adjoint logic** as potential unifying framework

---

## References

### Session Types and Linear Logic
- [Caires & Pfenning, "Session Types as Intuitionistic Linear Propositions" (CONCUR 2010)](https://link.springer.com/chapter/10.1007/978-3-642-15375-4_16)
- [Wadler, "Propositions as Sessions" (ICFP 2012)](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf)
- [Caires, Pfenning, Toninho, "Linear Logic Propositions as Session Types" (MSCS 2016)](https://www.cs.cmu.edu/~fp/papers/mscs13.pdf)

### Adjoint Logic and Session Types
- [Pruiksma & Pfenning, "A Message-Passing Interpretation of Adjoint Logic" (JLAMP 2021)](https://arxiv.org/abs/1904.01290)
- [nLab: Adjoint Logic](https://ncatlab.org/nlab/show/adjoint+logic)

### Shared Session Types
- [Balzer & Pfenning, "Manifest Sharing with Session Types" (OOPSLA 2017)](https://www.cs.cmu.edu/~fp/papers/esop19.pdf)
- [Balzer et al., "Manifest Deadlock-Freedom for Shared Session Types" (ESOP 2019)](https://link.springer.com/chapter/10.1007/978-3-030-17184-1_22)

### Authorization Logic
- [Garg et al., "A Linear Logic of Authorization and Knowledge" (ESORICS 2006)](https://www.semanticscholar.org/paper/A-Linear-Logic-of-Authorization-and-Knowledge-Garg-Bauer/8901e5201d9f1eb01864c5923ccd328c0b2d3013)
- [Abadi et al., "A Calculus for Access Control in Distributed Systems" (1993)](https://dl.acm.org/doi/10.1145/138873.138874)

### Multiparty Session Types
- [Honda et al., "Multiparty Asynchronous Session Types" (JACM 2016)](https://dl.acm.org/doi/10.1145/2827695)
- [Yoshida et al., "A Very Gentle Introduction to Multiparty Session Types"](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/)

### Related CALC Research
- [[nomos]] — Session types for smart contracts
- [[authorization-logic]] — Principals, says, speaks for
- [[linear-negation-debt]] — A⊥ as debt/obligation
- [[sketch]] — Coin ownership modeling

---

*Last updated: 2026-01-29*
