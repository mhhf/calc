---
title: "Resource Semantics: What Are Terms?"
created: 2026-02-10
modified: 2026-02-10
summary: Exploring term semantics for resource types as receipts, audit trails, or proof witnesses showing resource provenance and synthesis in linear logic.
tags: [resource-semantics, terms, proofs, Curry-Howard, provenance]
---

# Resource Semantics: What Are Terms?

If `A` is a resource type, what is the semantics of `a : A`? Can terms be 'receipts' or 'traces' showing WHERE the resource comes from / how it's synthesized?

> **See also:** [[ownership-design]] for coin ownership model, [[accounting-foundations]] for Pacioli group, [[linear-negation-debt]] for debt semantics, [[proof-calculi-foundations]] for Curry-Howard.

---

## Table of Contents

1. [The Question](#the-question)
2. [Perspectives on Term Semantics](#perspectives-on-term-semantics)
3. [Terms as Receipts / Audit Trails](#terms-as-receipts--audit-trails)
4. [Linear Logic Perspective](#linear-logic-perspective)
5. [What Terms Could Be in CALC](#what-terms-could-be-in-calc)
6. [Connection to Blockchain](#connection-to-blockchain)
7. [Open Questions](#open-questions)
8. [References](#references)

---

## The Question

In CALC, we write:
```
[Alice] coin(BTC, 0.5)    -- Alice owns 0.5 BTC
```

But what is a **proof** or **term** of this type? What information does it carry?

Curry-Howard says proofs ARE programs. So:
- A proof of `[Alice] coin(BTC, 0.5)` is a **term** `t : [Alice] coin(BTC, 0.5)`
- What IS this term `t`?
- Can `t` carry provenance information (WHERE did this coin come from)?

---

## Perspectives on Term Semantics

### 1. Proof-Irrelevant View

In classical logic and some type theories, we only care that a proof EXISTS, not WHAT it is.

```
If ⊢ A, then there's some proof p : A, but p doesn't matter
```

For accounting: "Alice has 0.5 BTC" is true or false. The proof is irrelevant.

**Problem for CALC:** We DO care about provenance! Where did the coin come from? Was it from a valid transaction?

### 2. Proof-Relevant View

In dependent type theory and linear logic, proofs ARE computationally meaningful.

```
p : [Alice] coin(BTC, 0.5)    -- p is a WITNESS for Alice's ownership
```

Different proofs can be distinguished:
- `p₁` = proof from mining
- `p₂` = proof from receiving transfer from Bob
- `p₁ ≠ p₂` even though they prove the same type

**For CALC:** This is what we want! The term carries provenance.

### 3. Realizability View

From Kleene realizability and Krivine realizability:

> "The meaning of a proposition is given by what counts as evidence for it."

A **realizer** of `A` is computational evidence that `A` holds.

For `[Alice] coin(BTC, 0.5)`:
- A realizer could be a **transaction hash** proving ownership
- Or a **merkle path** from a UTXO set
- Or a **signature chain** from coinbase

---

## Terms as Receipts / Audit Trails

### The Audit Trail Interpretation

What if terms in CALC are **audit trails**?

```
t : [Alice] coin(BTC, 0.5)
```

Where `t` encodes:
- **How** Alice got this coin (genesis, transfer, mining)
- **From whom** (if transfer)
- **When** (block height, timestamp)
- **Authorization** (signatures involved)

### The Calculus of Audited Units (CAU)

From research on audited computation:

> "The Calculus of Audited Units (CAU) extends the simply typed lambda calculus by providing audited types, inhabited by expressions carrying a **trail of their past computation history**."

Key features:
- Trails as proof terms witnessing computation history
- Runtime inspection of trails
- Applications in security, debugging, provenance

**This is exactly what we want for CALC!**

### Trails in CAU

In CAU, a term carries its computation history:

```
t : [τ]^{trail}
```

Where `trail` records how `t` was computed.

For CALC, analogously:
```
t : [Alice] coin(BTC, 0.5)   with trail = [mining(block_123) → Alice]
```

Or for a transfer:
```
t : [Bob] coin(BTC, 0.5)   with trail = [mining → Alice, transfer(sig_A) → Bob]
```

---

## Linear Logic Perspective

### Resource Semantics

In linear logic, each hypothesis is a resource consumed exactly once.

> "Unlike classical or intuitionistic logic, linear logic treats assumptions as finite resources that are consumed during proof rather than being endlessly reproducible."

**Term semantics:** A proof term records HOW resources were used.

### Phase Semantics vs Proof Semantics

Two approaches to linear logic semantics:

1. **Phase semantics:** Formula ↦ set of contexts that prove it (truth-oriented)
2. **Proof semantics:** Meaning given to proofs directly (evidence-oriented)

For CALC, we want **proof semantics** — the proof itself carries information.

### Coherence Spaces / Game Semantics

In coherence spaces (Girard):
- A proof is a **clique** in a coherence graph
- Different proofs = different cliques = distinguishable evidence

In game semantics:
- A proof is a **strategy**
- Different strategies = different ways to win = different evidence

---

## What Terms Could Be in CALC

### Option A: Transaction References

Terms are references to on-chain transactions:

```
t : [Alice] coin(BTC, 0.5)
t = TxRef(hash: "abc123", output_idx: 0)
```

Simple, concrete, but not compositional.

### Option B: Derivation Trees (Proofs as Terms)

Terms ARE proof trees:

```
t : [Alice] coin(BTC, 0.5)

t = Transfer_R(
      source: Mining_R(block: 123, coinbase_idx: 0),
      from: Alice,
      to: Alice,
      auth: Refl
    )
```

The term IS the derivation that establishes the type.

### Option C: Sequent Calculus Proof Terms

Assign proof terms to sequent rules (à la Curien):

```
Γ ⊢ A ⊗ B    becomes    Γ ⊢ (t₁ ⊗ t₂) : A ⊗ B

─────────────────────────────────────────────
  Γ, x : A, y : B ⊢ e : C
  ────────────────────────────────────── ⊗-L
  Γ, z : A ⊗ B ⊢ let (x, y) = z in e : C
```

This gives explicit terms for linear proofs.

### Option D: Trail-Annotated Terms

Combine standard λ-calculus with trails:

```
t^trail : A
```

Where `trail` is a separate data structure recording provenance.

---

## Proposal for CALC

### Term Structure

```
term ::=
  | var(x)                           -- variable reference
  | pair(t₁, t₂)                     -- tensor introduction
  | let_pair(t, x, y, e)             -- tensor elimination
  | inl(t) | inr(t)                  -- sum introduction
  | case(t, x.e₁, y.e₂)              -- sum elimination
  | lam(x, e)                        -- lollipop introduction
  | app(t₁, t₂)                      -- lollipop elimination
  | box(t)                           -- ownership introduction
  | unbox(t)                         -- ownership elimination
  | transfer(t, auth)                -- ownership transfer (with authorization)
```

### Trail Annotation

Each term carries a trail:

```
t : [Alice] coin(BTC, 0.5) @ trail

trail ::=
  | Genesis(source)                  -- created ex nihilo (mining, ICO, etc.)
  | Transfer(from, to, auth, prev)   -- transferred with authorization
  | Split(source, amounts)           -- divided into pieces
  | Merge(sources)                   -- combined pieces
```

### Example

```
-- Alice mines a coin
mine : [Alice] coin(BTC, 1.0) @ Genesis(Mining(block_123))

-- Alice transfers 0.5 to Bob
let (t₁, t₂) = split mine (0.5, 0.5) in
  transfer t₁ Alice Bob alice_sig
  : [Bob] coin(BTC, 0.5) @ Transfer(Alice, Bob, alice_sig, Split(mine, (0.5, 0.5)))
```

---

## Connection to Blockchain

### UTXO Model

In Bitcoin's UTXO model, coins have explicit provenance:
- Each UTXO references its creating transaction
- Spending reveals the full history back to coinbase

CALC terms could mirror this structure.

### Account Model

In Ethereum's account model, provenance is implicit in state:
- Balances are just numbers
- History is in transaction logs, not state

CALC could either:
- Use UTXO-style explicit provenance (richer)
- Or account-style implicit provenance (simpler)

### Smart Contract Traces

Smart contract execution produces traces. CALC terms could be:
- Trace prefixes (partial execution)
- Trace commitments (hash of full execution)
- Proof certificates (ZK proofs of valid execution)

---

## Open Questions

### 1. Granularity of Trails

How much history to keep?
- Full trace (expensive, complete)
- Hash commitment (cheap, verifiable)
- Last N steps (bounded, recent)

### 2. Trail Verification

Can trails be verified efficiently?
- Merkle proofs for inclusion
- ZK proofs for validity
- Signatures for authorization

### 3. Trail Composition

How do trails compose under ⊗, ⊸, etc.?
- Tensor: parallel trails
- Lollipop: sequential trails
- Bang: repeated trails

### 4. Privacy

Should trails be:
- Public (full transparency)
- Private (only owner sees)
- Committed (verifiable but hidden)

---

## References

### Audited Computation

- [Strongly Normalizing Audited Computation](https://www.researchgate.net/publication/317558355_Strongly_Normalizing_Audited_Computation) — CAU calculus with trails

### Proof-Theoretic Semantics

- [Stanford Encyclopedia: Proof-Theoretic Semantics](https://plato.stanford.edu/entries/proof-theoretic-semantics/)
- [A Proof-Theoretic Approach to the Semantics of Classical Linear Logic](https://arxiv.org/abs/2504.08349)

### Realizability

- [Streicher, Realizability](https://www2.mathematik.tu-darmstadt.de/~streicher/REAL/REAL.pdf)
- [Abramsky & Lenisa, Linear Realizability](https://link.springer.com/chapter/10.1007/978-3-540-74915-8_32)

### Linear Logic Semantics

- [Stanford Encyclopedia: Linear Logic](https://plato.stanford.edu/entries/logic-linear/)
- Girard, "Linear Logic" (1987)

---

*Last updated: 2026-01-29*
