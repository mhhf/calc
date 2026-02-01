# Consensus Modalities and Multiparty Session Types

This document explores how consensus modalities (`[A ∧ B] φ` — "both A and B must consent") can be modeled using multiparty session types (MPST), and what gaps remain.

---

## The Core Question

Can we express:
```
[Alice ∧ Bob] A     -- "Both Alice and Bob must consent to A"
[k-of-n] A          -- "At least k of n principals must consent"
```

In terms of multiparty session types?

---

## Background: Composite Principals in Authorization Logic

### Conjunction of Principals

From Garg-Pfenning authorization logic:

```
(A ∧ B) says S  ≡  (A says S) ∧ (B says S)
```

Both A and B must independently affirm S. This is **unanimous consent**.

### Disjunction of Principals

```
(A ∨ B) says S  ≡  (A says S) ∨ (B says S)
```

Either A or B affirming S suffices. This is **any-of consent**.

### Speaks-For Delegation

```
A speaks for B  ≡  ∀S. (A says S) → (B says S)
```

A can act on B's behalf. Combined with conjunction:

```
(A ∧ B) speaks for C   -- Both A and B together can act as C
```

---

## Multiparty Session Types (MPST) Overview

### Key Concepts

**Global Types**: Describe the entire protocol from a bird's-eye view.

```
G = Alice → Bob : transfer {
      ok: Bob → Alice : ack.end,
      fail: end
    }
```

**Local Types**: Each participant's view, obtained by projection.

```
L_Alice = !transfer. &{ok: ?ack.end, fail: end}
L_Bob   = ?transfer. ⊕{ok: !ack.end, fail: end}
```

**Roles/Participants**: Named entities (Alice, Bob, etc.) that follow local types.

### What MPST Provides

1. **Multi-party communication**: More than two participants
2. **Global coordination**: Protocol-level view ensures compatibility
3. **Deadlock freedom**: Well-formed global types guarantee progress
4. **Projection**: Global → local types preserves correctness

---

## Additive Choice with Multiple Principals: Who Chooses?

### The Core Question

In standard linear logic:
- **& (with)**: The *consumer/client* chooses which branch
- **⊕ (plus)**: The *producer/provider* chooses which branch

But with ownership modalities `[Alice]` and `[Bob]`, we have multiple principals. **Whose perspective determines "consumer" vs "producer"?**

### Case Analysis

#### Case 1: Single Owner with Choice

```
[Alice] (A & B)    -- Alice owns, Alice chooses (internal choice)
[Alice] (A ⊕ B)    -- Alice owns, counterparty chooses (external choice)
```

With one owner, this is clear: & gives Alice the choice, ⊕ means someone else picks.

#### Case 2: Choice Across Owners

```
[Alice] A & [Bob] B    -- NOT a valid "choice" — two separate resources
```

This isn't "pick one" — it's two resources with different owners. The & would mean "I can take either Alice's A or Bob's B" — but who is "I"?

#### Case 3: Options (Financial Example)

From financial-primitives.md:
```
call_option : [Alice] (
  (cash(strike) ⊸ underlying) &    -- exercise
  1                                 -- let expire
)
```

Alice owns the option, so Alice chooses. The & gives choice to the holder.

### Connection to `A says X`

With explicit authorization logic, we can be precise:

```
Alice says (A & B)    -- Alice affirms a choice; who chooses?
```

The `says` modality is Alice's *subjective statement*. The choice inside is still relative to Alice's perspective as the affirmer.

**For multi-party choice, we need explicit consent:**

```
-- Alice offers, Bob chooses
Alice says (offer(A) ⊕ offer(B))   -- Alice provides options (external)
Bob says choose(X)                  -- Bob selects one

-- Both must agree on the same choice
(Alice says X) ⊗ (Bob says X)      -- Conjunction of consents
```

### Proposed Semantics for CALC

#### Option 1: Ownership Determines Perspective

```
[P] (A & B)    -- P chooses (internal choice for P)
[P] (A ⊕ B)    -- ¬P chooses (external choice, counterparty decides)
```

**Problem:** Who is "¬P" in multi-party settings?

#### Option 2: Session-Type Polarity (Recommended)

Use session type conventions where **polarity** is relative to a channel endpoint:

```
-- From Alice's perspective:
[Alice] (A & B)     -- Alice can choose (internal)
[Alice] (A ⊕ B)     -- Counterparty chooses (external)

-- Duality in interaction:
[Alice] (A & B) ⊗ [Bob] (A ⊕ B)   -- Alice chooses, Bob receives
```

The key: **& and ⊕ are duals**. If Alice has &, her counterparty has ⊕.

#### Option 3: Explicit Choice Attribution

Introduce a "chooser" annotation:

```
[Alice]_{Alice chooses} (A & B)     -- Explicit: Alice picks
[Alice]_{Bob chooses} (A ⊕ B)       -- Explicit: Bob picks
```

#### Option 4: Make Consent Primitive

Add explicit offer/accept connectives:

```
offer_{A→B}(X)     -- A offers X to B
accept_{B←A}(X)    -- B accepts X from A

-- Atomic swap as consent protocol:
offer_{Alice→Bob}(coin(BTC)) ⊗ offer_{Bob→Alice}(coin(ETH))
⊸
accept_{Bob←Alice}(coin(BTC)) ⊗ accept_{Alice←Bob}(coin(ETH))
```

### Connection to MPST Global Types

MPST handles "who chooses" via **global types** with explicit sender/receiver:

```
global AtomicSwap =
  Alice → Bob : offer(BTC)
  Bob → Alice : {
    accept: Alice → Bob : transfer(ETH); end,
    reject: end
  }
```

The `{ accept, reject }` is Bob's **external choice** (⊕ from Alice's view, & from Bob's view).

**Projection** gives local types:
- Alice's view: `!offer(BTC); &{ accept: ?transfer(ETH), reject: end }`
- Bob's view: `?offer(BTC); ⊕{ accept: !transfer(ETH), reject: end }`

**Key Insight:** The global type specifies who chooses at each branching point. This is more explicit than relying on & vs ⊕ alone.

### Recommendation for CALC

**Short-term:** Use the session-type duality convention:
- `[P] (A & B)` = P has internal choice (P decides)
- `[P] (A ⊕ B)` = P has external choice (counterparty decides)
- For multi-party, use MPST-style global types to specify chooser

**Medium-term:** Add explicit consent via `says`:
```
[Alice] A ⊗ (Alice says transfer(A, Bob))
⊸
[Bob] A
```

**Long-term:** Full MPST integration where:
- Global types define who chooses at each point
- Projection generates per-principal rules automatically
- Choice attribution is always explicit in the protocol

---

## The Gap: Consensus in MPST

### Problem Statement

Standard MPST has **communication** between roles but not **consensus requirements**.

```
Alice → Bob : msg      -- Alice sends to Bob (one sender, one receiver)
```

There's no native construct for:
```
Alice ∧ Bob → Carol : msg    -- Both Alice AND Bob must agree to send
```

### The "Knowledge of Choice" Problem

In MPST, when branching occurs, participants must **know** which branch was taken.

```
G = Alice → Bob : choice {
      left: ...,
      right: ...
    }
```

Alice makes the choice. Bob learns it via the message. But what about Carol who doesn't receive this message?

This is the **knowledge of choice problem**: ensuring all participants know which branch was selected.

**Connection to consensus**: If Carol needs Alice AND Bob to agree on the choice, standard MPST doesn't express this directly.

---

## Approaches to Consensus in Session Types

### Approach 1: Synchronized Branching

Require all relevant parties to synchronize before branching:

```
G = sync(Alice, Bob) : choice {
      left: ...,
      right: ...
    }
```

**Interpretation**: `sync(Alice, Bob)` means both must agree before proceeding.

**Implementation**:
- Alice sends proposal to Bob
- Bob sends confirmation back
- Only then does the branch resolve

```
G = Alice → Bob : propose_left.
    Bob → Alice : {
      agree: [left branch],
      disagree: [right branch]
    }
```

This **encodes** consensus as a protocol pattern, not a primitive.

### Approach 2: Merge Semantics

Some MPST variants support **merge** for local types:

```
L ⊔ L' = merged local type
```

Merge combines different views into a consistent protocol.

For consensus, merge ensures all parties have compatible views of the choice.

**Limitation**: Merge is about type compatibility, not runtime agreement.

### Approach 3: Choreographic Programming

Choreographic programming (Montesi, Yoshida) writes protocols as global programs:

```
def atomic_swap(Alice, Bob, assetA, assetB):
    Alice.propose(assetA) → Bob
    Bob.accept(assetB) → Alice
    sync(Alice, Bob):
        Alice.transfer(assetA) → Bob
        Bob.transfer(assetB) → Alice
```

The `sync` construct ensures both parties reach the same point before proceeding.

**Endpoint Projection**: Compiles to distributed implementation.

**Connection to CALC**: This is close to what we want — explicit synchronization points where consensus is required.

### Approach 4: Explicit Consent Channels

Introduce dedicated channels for consent:

```
G = consent_channel(Alice, Bob) as c.
    c → Carol : action.
    ...
```

The `consent_channel` construct creates a virtual party that requires both Alice and Bob to act together.

**This maps directly to composite principals**:
```
consent_channel(Alice, Bob) ≈ [Alice ∧ Bob]
```

---

## Threshold Signatures and k-of-n Consent

### The Cryptographic Approach

**K-of-n threshold schemes** (Shamir, multi-sig):
- n parties hold shares of a secret/key
- Any k of them can reconstruct/sign
- Fewer than k cannot

**In Bitcoin multi-sig**:
```
2-of-3 multi-sig: Any 2 of Alice, Bob, Carol can spend
```

### Encoding in Session Types

**Direct encoding is awkward**:

```
G = Alice → Coordinator : sign_a.
    Bob → Coordinator : sign_b.
    Carol → Coordinator : sign_c.
    Coordinator : if (count >= k) then proceed else abort
```

This requires an explicit coordinator and doesn't naturally express "k of n".

**Better approach**: Extend MPST syntax:

```
G = threshold(k, {Alice, Bob, Carol}) : action.
    ...
```

### Connection to Linear Logic

Can threshold consent be expressed in linear logic?

```
-- At least 2 of 3 must provide their share
(A_share ⊕ (B_share ⊗ C_share)) ⊕
(B_share ⊕ (A_share ⊗ C_share)) ⊕
(C_share ⊕ (A_share ⊗ B_share))
```

This is **exponentially verbose**! The additive structure (⊕, &) doesn't compactly express "k of n".

**Open question**: Is there a linear logic extension that naturally handles threshold predicates?

---

## Ludics and Orthogonality for Consensus

### Girard's Orthogonality

In Ludics, two designs D and E are **orthogonal** (D ⊥ E) if their interaction converges.

```
D ⊥ E  iff  D || E  terminates normally
```

### Consensus as Orthogonality

**Hypothesis**: Consensus between Alice and Bob can be modeled as:

```
D_Alice ⊥ D_Bob  iff  Alice and Bob can successfully interact
```

For `[A ∧ B] φ`, both must provide orthogonal designs:

```
D_Alice ⊥ D_φ  and  D_Bob ⊥ D_φ
```

**Meaning**: Both Alice and Bob have strategies that "fit" with φ.

### Multi-Party Orthogonality

Extend to n parties:

```
D_1 ⊥ D_2 ⊥ ... ⊥ D_n  iff  all designs mutually interact
```

This could model multi-party consensus: all parties' designs are pairwise (or collectively) orthogonal.

**Open question**: Does Ludics provide the right framework for this?

---

## Synthesis: Modeling [A ∧ B] in CALC

### Option 1: Encode Consensus as Protocol

Don't add `[A ∧ B]` as primitive. Instead, encode as communication pattern:

```
-- [Alice ∧ Bob] transfer(x)  becomes:
Alice says propose_transfer(x)  ⊗
Bob says accept_transfer(x)     ⊗
[Alice] x                       ⊸
[Bob] x
```

**Pros**: No new primitives needed
**Cons**: Verbose, doesn't capture the "both must consent" atomically

### Option 2: Composite Principal as Primitive

Add `[A ∧ B]` as a first-class modality:

```
[Alice ∧ Bob] coin(BTC, 1.0)    -- Joint ownership
(Alice ∧ Bob) says transfer     -- Joint authorization
```

**Inference rules**:
```
Introduction:
─────────────────────────────────────────────────
[A] φ ⊗ [B] φ  ⊢  [A ∧ B] φ

Elimination:
─────────────────────────────────────────────────
[A ∧ B] φ  ⊢  [A] φ
[A ∧ B] φ  ⊢  [B] φ

Authorization:
─────────────────────────────────────────────────
(A ∧ B) says S  ≡  (A says S) ∧ (B says S)
```

**Pros**: Clean, matches authorization logic
**Cons**: Need to ensure sound interaction with other modalities

### Option 3: Adjoint Logic with Principal Modes

Extend adjoint logic with principal-indexed modes:

```
Modes = { M_Alice, M_Bob, M_AliceAndBob, ... }

M_Alice ⊗ M_Bob → M_AliceAndBob   (tensor of modes)
```

**Pros**: Uniform framework, modes already handle structural properties
**Cons**: Non-standard extension, needs development

### Option 4: Session Types with Consent Primitives

Extend MPST syntax:

```
G = consent(Alice, Bob) : transfer.
    ...
```

This compiles to appropriate synchronization in endpoint projection.

**Connection to CALC**: The global type IS the specification, local types are what each principal sees.

---

## Comparison Table

| Approach | Expressiveness | Complexity | CALC Integration |
|----------|----------------|------------|------------------|
| Encode as protocol | Low | Low | Easy |
| Composite principal primitive | Medium | Medium | Moderate |
| Adjoint with principal modes | High | High | Research needed |
| Extended MPST | High | Medium | Research needed |
| Ludics orthogonality | High | High | Research needed |

---

## Connection to CALC's Atomic Swap

From sketch.md, our atomic swap:

```
[Alice] coin(BTC, 0.5)   ⊗   [Bob] coin(ETH, 5.0)
                         ⊸
[Bob] coin(BTC, 0.5)     ⊗   [Alice] coin(ETH, 5.0)
```

**The hidden consensus**: This rule requires BOTH Alice and Bob to consent:
- Alice consents by providing her BTC
- Bob consents by providing his ETH

But this consensus is **implicit** in the tensor (⊗) structure, not explicit.

**Making it explicit**:
```
(Alice says swap) ⊗ (Bob says swap) ⊗
[Alice] coin(BTC, 0.5) ⊗ [Bob] coin(ETH, 5.0)
⊸
[Bob] coin(BTC, 0.5) ⊗ [Alice] coin(ETH, 5.0)
```

**Or with composite principal**:
```
(Alice ∧ Bob) says swap ⊗
[Alice] coin(BTC, 0.5) ⊗ [Bob] coin(ETH, 5.0)
⊸
[Bob] coin(BTC, 0.5) ⊗ [Alice] coin(ETH, 5.0)
```

---

## Open Questions

### 1. Modal Logic of Composite Principals

What is the modal logic of `[A ∧ B]`?

```
□_{A ∧ B} φ  =?=  □_A φ ∧ □_B φ
```

Does this satisfy the K axiom? T axiom? What about `[A ∨ B]`?

### 2. Threshold Modalities

Can we define `[k-of-{A,B,C}]` cleanly?

```
[2-of-{A,B,C}] φ  ≡  ([A ∧ B] ∨ [A ∧ C] ∨ [B ∧ C]) φ
```

This explodes combinatorially. Is there a better representation?

### 3. Ludics for Multi-Party

Does Ludics' orthogonality extend naturally to 3+ parties?

```
D_A ⊥ D_B ⊥ D_C  =?=  (D_A ⊥ D_B) ⊥ D_C ?
```

Is orthogonality associative?

### 4. Global Types as Authorization Policies

Can we view MPST global types as authorization policies?

```
Global type G  ≈  Authorization policy
Projection G↾A  ≈  A's local permissions
```

### 5. Deadlock Freedom = Consensus Achievability?

MPST's deadlock freedom: well-typed processes communicate without stuck states.

**Hypothesis**: For consensus modalities, deadlock freedom corresponds to "consensus is achievable" — the protocol design guarantees that if all parties follow their local types, they will reach agreement.

---

## Research Update: Additional Questions

### Channel Passing = Speaks For?

**Analysis:**

| Session Types (Channel Delegation) | Authorization Logic (Speaks For) |
|-----------------------------------|----------------------------------|
| `send c d` — transfer channel d ownership | A speaks for B — A acts as B |
| Recipient gets authority over channel | Delegate gets authority of principal |
| Specific to one communication endpoint | General authority transfer |
| Dynamic (runtime) | Often static (policy) |

**Connection**: Channel passing IS a form of delegation. Passing channel c means "you now have authority to act on this channel" — this is analogous to "speaks for" in a specific context.

**Differences**:
- Channel delegation: ownership of **specific resource** (channel)
- Speaks-for: authority to act as **principal** (general)
- Channel delegation is **linear** (transferring, not copying)
- Speaks-for can be **persistent** (ongoing authority)

**For CALC**: Channel passing maps to ownership transfer `[Alice] A ⊸ [Bob] A`. The "speaks for" relation is complementary: `Alice speaks for Bob` means Alice's resource transfers implicitly count as Bob-authorized.

### Threshold Modalities: Compact Representation?

**The problem**: `[k-of-{A,B,C,...}] φ` expands combinatorially:
```
[2-of-{A,B,C}] φ  =  ([A∧B] ∨ [A∧C] ∨ [B∧C]) φ
```

For n principals, k-of-n has C(n,k) terms — exponential.

**Search result**: No compact modal logic representation found in literature.

**Possible approaches**:
1. **Threshold predicate**: `threshold(k, [A,B,C], φ)` — use predicate, not modality
2. **Counting quantifier**: ∃≥k x ∈ P. (x says φ) — requires counting extension
3. **Probabilistic interpretation**: "with high probability, enough agree" — lose determinism
4. **Cryptographic approach**: threshold signatures verify k-of-n, logic trusts crypto

**Recommendation for CALC**: Use explicit predicate `threshold(k, principals, φ)`. Don't try to encode as modal operator — the combinatorial explosion is fundamental.

### Global Types as Authorization Policies?

**Strong parallel found:**

| MPST Global Types | Authorization Policies |
|-------------------|----------------------|
| Specifies who sends what to whom | Specifies who can do what to what |
| Projection → local types | Policy derivation → local permissions |
| Ensures deadlock freedom | Ensures access control |
| Protocol correctness | Security property |

**Key insight from literature**:
> "The global type plays the role of a shared agreement among communication peers."

This IS like an authorization policy — a global specification of allowed interactions.

**Differences**:
- Global types focus on **message ordering** (causality, deadlock)
- Authorization focuses on **permission** (who is allowed)
- Global types → safety (protocol correctness)
- Authorization → security (access control)

**Synthesis for CALC**: Global types could serve as authorization policies for multi-party protocols. The projection operator gives each principal their local permissions. Deadlock freedom corresponds to "consensus is achievable."

---

## Recommendations for CALC

### Short-term (Current System)

1. **Encode consensus as protocol pattern** — don't add new primitives yet
2. **Use explicit `A says S` for each participant** — makes consent visible
3. **Document the "hidden consensus" in atomic swap** — make clear what's implicit
4. **Use explicit threshold predicate** — `threshold(k, principals, φ)` not modal

### Medium-term (Next Phase)

1. **Add `[A ∧ B]` as composite principal** — clean semantics from auth logic
2. **Define inference rules** — introduction, elimination, authorization
3. **Test with atomic swap** — verify it captures the intended semantics
4. **Explore global types for protocols** — authorization as global specification

### Long-term (Research)

1. **Study adjoint logic with principal modes** — could be unifying framework
2. **Explore Ludics orthogonality** — might give semantic foundation
3. **Consider MPST integration** — protocols as global types, proofs as local types
4. **Channel delegation semantics** — formalize channel passing as speaks-for

---

## Summary

**Can consensus modalities be expressed in MPST?**

**Partially.** MPST has:
- Multiple participants (roles)
- Coordination via global types
- Projection to local views

But MPST lacks:
- Native "both must consent" construct
- Threshold (k-of-n) primitives
- Authorization reasoning

**Key insight**: Consensus is **implicit in communication patterns** but not **explicit as a modality**. MPST ensures coordination happens correctly; authorization logic says **who** must consent.

**Recommendation for CALC**:
- Short-term: Encode as protocol patterns
- Medium-term: Add `[A ∧ B]` as primitive composite principal
- Long-term: Explore adjoint logic and Ludics for semantic foundations

---

## References

### Multiparty Session Types
- [Honda, Yoshida, Carbone, "Multiparty Asynchronous Session Types" (JACM 2016)](https://dl.acm.org/doi/10.1145/2827695)
- [Yoshida et al., "A Very Gentle Introduction to MPST"](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/)
- [Scalas & Yoshida, "Less is More" (POPL 2019)](https://dl.acm.org/doi/10.1145/3290343)

### Choreographic Programming
- [Montesi, "Introduction to Choreographies" (2023)](https://www.fabriziomontesi.com/files/choreographies.pdf)
- [Carbone & Montesi, "Choreographies and Session Types"](https://link.springer.com/chapter/10.1007/978-3-319-39570-8_8)

### Authorization Logic
- [Garg et al., "A Linear Logic of Authorization and Knowledge"](https://www.semanticscholar.org/paper/A-Linear-Logic-of-Authorization-and-Knowledge-Garg-Bauer/8901e5201d9f1eb01864c5923ccd328c0b2d3013)
- [Abadi et al., "A Calculus for Access Control"](https://dl.acm.org/doi/10.1145/138873.138874)

### Threshold Cryptography
- [Shamir, "How to Share a Secret" (1979)](https://dl.acm.org/doi/10.1145/359168.359176)
- [Gennaro et al., "Threshold Signatures"](https://link.springer.com/chapter/10.1007/3-540-46416-6_47)

### Related CALC Research
- [[ownership-as-session-types]] — Session types and ownership
- [[authorization-logic]] — Says, speaks for, controls
- [[linear-negation-debt]] — Debt as linear negation
- [[sketch]] — Coin ownership modeling

---

*Last updated: 2026-01-29*
