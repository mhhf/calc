# Temporal Modalities for Derivatives

How to add time to linear logic for modeling financial instruments with deadlines, schedules, and expiry.

---

## 1. The Problem: Time Is Missing from ILL

CALC's ILL base has structural persistence (`!A` = "use A as many times as you want") but no temporal awareness. Financial instruments fundamentally need time:
- **Futures**: obligation at date T
- **Options**: right exercisable before expiry
- **Bonds**: payment schedule at t₁, t₂, ..., tₙ
- **Vesting**: resource available during interval [t₁, t₂]
- **HTLC**: hash-locked asset with timeout fallback

The `!` modality bundles two independent capabilities: **structural persistence** (unlimited copies) and **temporal persistence** (always available). Separating these is the key insight.

| Operator | Structural | Temporal | Combined |
|----------|-----------|----------|----------|
| `A` (linear) | Use once | Now | Use once, now |
| `□A` (always) | Use once | Any time | Use once, any time |
| `!A` (bang) | Use many | Any time | Use many, any time |
| `○A` (next) | Use once | Next step | Use once, next step |

---

## 2. Temporal Linear Logic (TLL) — Kanovich & Ito

**Paper:** Kanovich & Ito. "Temporal Linear Logic Specifications for Concurrent Processes." LICS 1997.

TLL extends ILL with two temporal operators:

| Operator | Symbol | Meaning |
|----------|--------|---------|
| Next-time | `○A` | A available exactly once at next time step |
| Always | `□A` | A available exactly once at any future time |
| Bang | `!A` | A available arbitrarily many times at any time |

`□A` gives temporal persistence (use once, at any time); `!A` adds structural persistence (use many, at any time). This separation is TLL's key contribution.

**TLLP** is a logic programming language built on TLL using Miller's uniform proofs.

### Hirai's Dissertation (JAIST, 2000)

Hirai systematically developed TLL with:
- Full sequent calculus, cut elimination, decidability results
- **Timed Petri net correspondence:** reachability in timed Petri nets ↔ provability in TLL
- Communication model distinguishing synchronous from asynchronous calculi

The Petri net connection is significant: standard LL cannot encode timed Petri nets.

### Timed Multiset Rewriting — Kanovich, Nigam, Scedrov et al.

**Paper:** Kanovich et al. "Timed Multiset Rewriting and the Verification of Time-Sensitive Distributed Systems." 2016.

Connects linear logic, multiset rewriting, and explicit time for security protocol verification. Key results:

| Problem | Complexity |
|---------|-----------|
| Realizability (Progressive Timed Systems) | PSPACE-complete |
| Survivability (PTS) | PSPACE-complete |
| Bounded-time realizability | NP-complete |

---

## 3. Next-Time (○/●) in Display Calculus

In Belnap's display calculus for tense logic Kt, temporal operators use a **unary structural connective** `*` with display postulates:

```
X ⊢ *Y          *X ⊢ Y
---------   and   ---------
*'X ⊢ Y          X ⊢ *'Y
```

where `*` and `*'` are adjoint (future/past). The next-time operator ○ is the special case where accessibility is the successor function. **○ and ● (previous) form a residuated pair**: `○A ⊢ B iff A ⊢ ●B`.

### Belnap's C1-C8

Any display calculus satisfying C1-C8 automatically has cut elimination. For tense logic Kt extended with Scott-Lemmon axioms, display calculi can be constructed satisfying all eight conditions.

### Loop-Type Sequent Calculi

For PLTL with ○ and □, loop-type sequent calculi provide backward proof-search with loop-checking for termination.

**References:**
- Belnap, "Display Logic" (1982)
- Gore, "Cut-free display calculi for nominal tense logics"
- Ciabattoni, Ramanayake, Wansing, "Hypersequent and display calculi -- a unified perspective"

---

## 4. □ vs ! — The Exponential-Modal Relationship

### The Core Question

| Property | !A (exponential) | □A (S4 box) |
|----------|------------------|-------------|
| Weakening | Yes | Yes |
| Contraction | Yes | Yes |
| Idempotent | !A ≅ !!A | □A ≅ □□A |
| Dereliction | !A ⊢ A | □A ⊢ A |
| Semantics | "available without limit" | "true at all accessible worlds" |

Both satisfy S4 axioms (T: □A → A, 4: □A → □□A). The **Girard translation** uses ! exactly where S4 uses □.

### Fukuda-Yoshimizu: The Interaction Problem (FSCD 2019)

Naive combination of ! and □ causes undesirable interaction. Their solution: a **combined modality** `!□` for intuitionistic MELL. The exponential and S4 modality cannot be independently combined — they must be fused.

### Benton's LNL Decomposition

Decompose `! = F ∘ G` where F and G form an adjunction between intuitionistic (persistent) and linear (ephemeral) categories. This extends to temporal: an adjunction between "persistent across time" and "available at one time step."

---

## 5. Temporal Type Theory and Reactive Programming

### Krishnaswami-Benton: Ultrametric Semantics (LICS 2011)

Denotational model of higher-order FRP using **ultrametric spaces and nonexpansive maps**:
- Ultrametric spaces = Cartesian closed generalization of causal stream functions
- Guarded recursive definitions naturally modeled
- "Programs that agree further into the future are closer together" — a temporal metric

### Bounded Space FRP (POPL 2012)

Krishnaswami-Benton-Hoffmann: **statically bounds dataflow graph size** using linear types. Linearly-typed tokens represent allocation rights. Supports streams-of-streams, first-class functions, higher-order operations.

### Paykin-Krishnaswami-Zdancewic: Linear Temporal Type Theory (2016)

Curry-Howard for **event-driven programming** and **linear-time temporal logic**:
- ◇A = type of **events** (something that will happen)
- □A = type of **behaviors** (continuously available)
- Linear logic captures effectful, concurrent nature
- Implementation: ◇A = ¬□¬A (events as callbacks)

A "**linear temporal linear logic**" — linear in both temporal and resource senses.

### Nakano's Later Modality (LICS 2000)

The **later modality** `▸A` guards recursive occurrences:
- ▸A = "A available one step later"
- Guarded fixed point: `fix : (▸A → A) → A`
- Guarded streams: `Str A ≅ A × ▸(Str A)` (head now, tail later)
- **Löb induction**: `(▸A → A) → A` (variant of Löb's theorem from provability logic)

### Clouston: Fitch-Style Modal Types

The **lock** operation is **left adjoint to □**:
```
lock(Γ) ⊢ A
-----------------
Γ ⊢ □A
```

Extended à la tense logic, the left adjoint gives the "previous" modality. Models: any CCC with adjunction of endofunctors `L ⊣ R`.

### Clocked Type Theory

Ticking clocks as **dependent right adjoints**: family of later modalities indexed by clocks, connecting guarded recursion to parametric polymorphism over time.

---

## 6. HyLL and Modal/Temporal Extensions

### Hybrid Linear Logic — Despeyroux, Olarte, Pimentel

**Papers:** TYPES 2013, MSCS 2019.

HyLL extends ILL with:
- **Worlds** with monoidal structure (labels for time, location)
- **Hybrid connectives:** `@_w A` (A holds at world w), `↓x.A` (bind current world)

**Key finding:** HyLL alone cannot encode full CTL. Adding μ/ν fixed points (μHyMALL) enables faithful encoding of all CTL temporal connectives.

### Adjoint Logic — Reed, Pfenning, Licata, Shulman

**Benton (1995):** LNL decomposes `! = F ∘ G` via adjunction between linear and cartesian categories.

**Reed (2009):** Generalizes to preorder of modes with adjunctions. S4 □ and lax ○ arise as specific comonad/monad instances.

**Licata & Shulman (2015):** Further generalizes to 2-category of modes with adjunctions as mode morphisms.

**For temporal modalities:** temporal operators (next, always) are specific adjunctions between "time-indexed" modes. The adjoint logic framework provides principled modality addition while preserving cut elimination.

### Kamide's Temporal Substructural Logics

Systematic body of work adding temporal operators to substructural logics:

- **TSEILL** (TCS 2006): temporal + spatial + epistemic operators over ILL, with Kripke completeness
- **TN[l]** (LLP 2009): first-order temporal non-commutative logic; **key insight:** "time can be regarded as a resource" — temporal and resource indices are interchangeable
- **Girard Translation** (MLQ 2013): embeds first-order LTL → ILTL → LLTL

---

## 7. Fixed Points Encode Temporal Operators

### The Classical Encoding

```
□A  =  ν X. A & ○X     ("A now and always next")
◇A  =  μ X. A ∨ ○X     ("A now or eventually next")
A U B = μ X. B ∨ (A & ○X)  ("B now, or A now and (A until B) next")
```

The μ-calculus is the backbone of CTL*, LTL, CTL — all embed into it.

### muMALL Connection

In muMALL (see [[muMALL-fixed-points]]):
```
!A  =  ν X. A & X    (persistent = always available, no time)
□A  =  ν X. A & ○X   (always true, stepping through time)
```

The difference is ○: an explicit time step. If ○ is the identity, □ collapses to !.

| Logic | Fixed points | Next step | Exponentials |
|-------|-------------|-----------|-------------|
| MALL | none | none | none |
| muMALL | μ, ν | none | encoded (ν X. A & X) |
| muMALL + ○ | μ, ν | yes | distinct from □ |
| LTL | implicit (□, ◇) | yes | N/A |

---

## 8. Temporal Session Types

### Das, Hoffmann, Pfenning (ICFP 2018)

Enrich session types (which correspond to ILL via Caires-Pfenning) with temporal modalities:

| Type | Meaning |
|------|---------|
| `○A` (next) | Message at next time step |
| `□A` (always) | Message at any future time |
| `◇A` (eventually) | Message at some future time |

Expresses: message rate, pipeline latency, response time, fork/join span.

Temporal modalities are a **conservative extension** — they add timing without changing the linear logic structure.

### RAST: Resource-Aware Session Types

- **Ergometric types** measure **work** = total cost (sequential metric)
- **Temporal types** measure **span** = cost with maximal parallelism (parallel metric)
- Both are conservative extensions of ILL session types

### Nomos: Session Types for Blockchain

Das, Balzer, Hoffmann, Pfenning (CSF 2021). Linear session types for smart contracts:
- Session types enforce interaction protocols
- Linear types prevent asset duplication (no double-spending)
- AARA bounds gas consumption
- Acquire-release discipline prevents re-entrancy
- Case studies: auctions, elections, currencies

### Timed MPST — Bocchi, Yang, Yoshida (CONCUR 2014)

Global types with clock constraints. Guarantees:
- Time-safety, time-error freedom, progress, liveness

Key follow-up:
- Bocchi-Lange-Yoshida, "Meeting Deadlines Together" (CONCUR 2015)
- Neykova-Bocchi-Yoshida, "Timed Runtime Monitoring" (FAC 2017)
- Bocchi et al., "Asynchronous Timed Session Types" (ESOP 2019)
- Hou-Lagaillardie-Yoshida, "Fearless Asynchronous Communications" (ECOOP 2024)

**Connection to linear logic:** Bocchi's line is operationally defined (global → local → processes), NOT Curry-Howard. Connection is indirect: binary projections correspond to linear logic propositions.

### TOAST: Timeout Patterns (LMCS 2025)

Timeouts are inherently mixed-choice: either receive within deadline, or timeout. TOAST's solution: timing constraints regulate when mixed-choice is safe. Enables Erlang-style `receive...after` patterns.

### Comparison Table

| System | Time Model | LL Basis | Resources | Timeouts |
|--------|-----------|----------|-----------|----------|
| Timed MPST (Bocchi) | Real clocks | No | No | Via global types |
| Temporal ST (Das-Pfenning) | Logical ticks | Yes (Curry-Howard) | Yes (ergometric) | Via ◇ |
| TOAST (Pears-Bocchi) | Real clocks | No | No | Explicit |
| Nomos | None | Yes (Curry-Howard) | Yes (AARA) | No |
| RAST | Logical ticks | Yes | Yes (erg + temporal) | Via ◇ |
| Graded ST (Marshall-Orchard) | Via semiring | Partial (graded !) | Yes (graded) | If time in semiring |
| Move | None | Inspired | Linear resources | No |
| Marlowe | Block time | No | Conservation proof | Built-in |

---

## 9. Financial Contract DSLs

### Peyton Jones: Composing Contracts (ICFP 2000)

Foundational combinator-based contract specification:

| Combinator | Intuition |
|---|---|
| `Zero` | Null contract |
| `One(k)` | Receive one unit of currency k |
| `Give(c)` | Flip obligations |
| `And(c1, c2)` | Both simultaneously |
| `Or(c1, c2)` | Choice of better |
| `Scale(obs, c)` | Multiply by observable |
| `When(obs, c)` | Acquire c when obs becomes true |
| `Anytime(obs, c)` | Acquire c at any time while obs holds |
| `Until(obs, c)` | c active until obs becomes true |

The temporal operators (`When`, `Anytime`, `Until`) are the non-mathematical core. Modeling:
- **Zero-coupon bond:** `When(at(T), Scale(100, One(GBP)))`
- **European option:** `When(at(expiry), Or(underlying, Zero))`
- **American option:** `Anytime(before(expiry), Or(underlying, Zero))`
- **Swap:** `And(c1, Give(c2))`

Commercialized by LexiFi (MLFi language).

### Bahr-Berthold-Elsman: Certified Contract Management (ICFP 2015)

| Primitive | Meaning |
|---|---|
| `Transfer(p1, p2, k)` | p1 transfers one unit to p2 |
| `Scale(e, c)` | Scale by expression e |
| `Translate(n, c)` | Delay by n time steps |
| `Both(c1, c2)` | Both simultaneously |
| `If(obs, n, c1, c2)` | If obs true within n steps, c1; else c2 |

The `If..within` construct models American-style exercise. Major contributions:
- **Causality type system:** future inputs cannot influence present cash flows
- **Horizon inference:** furthest time of possible cash flow
- Formalized in **Coq** with Haskell extraction

### Marlowe (Cardano)

```haskell
data Contract = Close | Pay Party Payee Token Value Contract
              | If Observation Contract Contract
              | When [Case] Timeout Contract | Let ValueId Value Contract
              | Assert Observation Contract
```

`When cases timeout cont`: wait for case to trigger; if timeout reached, fall through. Every Marlowe contract has finite lifetime. Formal proof: "money in = money out."

### Findel: Linear-Logic-Inspired (FC Workshops 2017)

Findel's `Timebound(t, c)` enforces temporal constraints for Ethereum. Semantics formalized in Coq (450 non-empty lines).

### ACTUS: Algorithmic Contract Standards

LTL for verifying financial contract traces: contracts as reactive systems, traces checked with LTL formulas. ISO collaboration (2024) for formal contract specification.

---

## 10. Metric Temporal Logic and Graded Time

### MTL: Bounded Temporal Operators

MTL extends LTL with metric constraints:
- `□[a,b] A` = A holds at all times in [a,b]
- `◇[a,b] A` = A holds at some time in [a,b]
- `A U[a,b] B` = A until B within [a,b]

(Ouaknine-Worrell): Every MTL formula decomposes into bounded and unbounded parts.

### Graded Temporal Modalities

Natural connection: `□[0,k] A` ≈ temporally graded modality where the semiring tracks time bounds. The Granule language implements graded modal types with semiring-indexed modalities.

For temporal grading: `!_[0,5] A` = "A available for the next 5 steps."

Pre-ordered semiring: `(Intervals, [0,0], +, [0,∞], ∩, ⊆)`

### Resource-Bounded Type Theory (Mück et al., 2025)

Graded feasibility modality `□_r` with abstract resource lattice:
- Uniform treatment of time, memory, gas, domain-specific costs
- Cost soundness: operational cost bounded by synthesized bound

### Graded Modal Session Types (Marshall-Orchard, PLACES 2022)

Graded modalities from BLL control non-linearity:
```
!_n A    — usable exactly n times
!_∞ A    — usable arbitrarily (standard !)
!_0 A    — discardable (weakening)
```

The grading semiring can track usage count, security levels, **time intervals**, or combinations (product semirings).

---

## 11. Separation Logic with Time

### Demri: Temporal-Separation Correspondence (TIME 2018)

The separating conjunction `*` in separation logic is structurally analogous to temporal composition:
- PITL's **chop** `;` splits an interval into sub-intervals
- Separation logic's `*` splits a heap into disjoint sub-heaps
- Both are resource-sensitive compositions with identity

### Iris and Temporal Reasoning

- **Invariants** with temporal guarantees
- **Step-indexed** reasoning (inherently temporal)
- **Later modality** `▷P` = Nakano's later applied to separation logic

---

## 12. Smart Contract Temporal Verification

### VerX (IEEE S&P 2020)

First automated verifier for **functional temporal properties** of Ethereum contracts. Evaluated on 83 temporal properties across 12 projects. Example: "once sale finalized, no more tokens minted."

### VESC (SPLASH 2024)

Structured natural language → formal LTL. Removes barrier of raw LTL formula writing.

### HTLC Typing

HTLCs combine hash lock + time lock:
```
HTLC(hash, timeout, recipient, sender) =
  if reveal(preimage) ∧ verify(hash, preimage) ∧ sig(recipient)
    → pay(recipient)
  else if time > timeout ∧ sig(sender)
    → refund(sender)
```

As linear types: the locked asset is linear (no duplication), the preimage is linear (revealing enables spending), timeout creates timed disjunction. **Typing HTLCs with timed linear types is largely unexplored.**

---

## 13. Relevance to CALC

### Financial Primitives as Temporal Linear Types

| Instrument | CALC Encoding |
|-----------|--------------|
| Future (deliver at T) | `○ⁿ A` (n next-steps) |
| European option | `○ⁿ (A & B⊥)` (choice at expiry) |
| American option | `◇[0,T] (A & B⊥)` (choice before expiry) |
| Bond | `⊗ᵢ ○ⁱ paymentᵢ` (scheduled payments) |
| Vesting | `□[t₁,t₂] A` (available during interval) |
| HTLC | `(reveal ⊗ pay) ⊕ (timeout ⊗ refund)` with timed linear disjunction |

### The Peyton Jones Mapping

| Combinator | CALC Connective |
|-----------|----------------|
| `Zero` | `1` (unit) |
| `One(k)` | `[party] coin(k, 1)` |
| `Give(c)` | Linear negation / role swap |
| `And(c1, c2)` | `c1 ⊗ c2` |
| `Or(c1, c2)` | `c1 & c2` (holder chooses) |
| `Scale(e, c)` | Graded modality `!_e c` |
| `When(obs, c)` | `□(obs ⊸ c)` or `○ⁿ c` with n from obs |
| `Anytime(obs, c)` | `◇[0,T] c` |
| `Until(obs, c)` | `□[0,T] c` with T from obs |

### Display Calculus Compatibility

Temporal operators fit naturally:
- ○/● form a residuated pair (like ⊗/⊸)
- □/◇ definable via fixed points if we have μ/ν
- Belnap's C1-C8 satisfiable for temporal extensions
- Multi-type framework (Greco-Palmigiano) can accommodate temporal types as another sort

### Architecture Sketch

```
                    muMALL + ○
                   /           \
                  /             \
        Temporal operators    Resource control
        □ = ν X. A & ○X      ! = ν X. A & X
        ◇ = μ X. A ∨ ○X      ? = μ X. A ∨ X
                  \             /
                   \           /
                    v         v
            Multi-type display calculus
            Sort 1: Linear (ephemeral, one time step)
            Sort 2: Persistent (across all time)
            Sort 3: Temporal (across specific times)
            Adjunctions: F/G between sorts
```

### Three Implementation Paths

**(a) Add ○ as primitive with residual ●**
- Minimal extension: just next/previous
- Display postulates give cut elimination
- □/◇ require separate treatment or encoding via fixed points
- Most conservative; aligns with display calculus methodology

**(b) Add μ/ν and encode temporal operators**
- muMALL already studied (see [[muMALL-fixed-points]])
- □ = ν X. A & ○X needs ○ anyway
- Most expressive; subsumes both exponentials and temporal operators
- Highest implementation complexity

**(c) Use graded ! to capture bounded time**
- `!_[a,b] A` = "A available during interval [a,b]"
- Interval semiring: `(Intervals, [0,0], +, [0,∞], ∩, ⊆)`
- Integrates with existing graded modality work
- Lightweight; no new connective syntax
- Cannot express unbounded temporal properties (no □ or ◇)

**Recommendation for CALC:** Start with (a) — add ○/● as a residuated pair. This is the minimum needed for futures/scheduling. Then extend to (b) for options/unbounded temporal properties if/when muMALL is implemented.

### Graded Temporal + Ownership Interaction

The full picture combines three modality families:
```
[Alice] !_[0,5] coin(BTC, 0.5)
```
= "Alice owns 0.5 BTC available for the next 5 steps"

The semiring must combine time bounds with ownership principals. This is an open problem connecting to multi-type display calculus.

---

## Open Questions

1. **Can ○ be given a residual in display calculus?** Yes — ● is its residual. But on bounded time (ℕ), ● is partial.

2. **Graded temporal + ownership interaction?** `[Alice] !_[0,5] token` — the semiring must combine time bounds with principals.

3. **Cyclic proofs for temporal properties?** If □A = ν X. A & ○X, then temporal invariants are greatest fixed points, verifiable by cyclic proofs.

4. **Unifying real and logical time?** Das-Pfenning's logical ticks vs Bocchi's real clocks. Multi-type framework could bridge them (different sorts).

5. **HTLC typing?** Cross-chain atomic swaps need: linear assets + hash commitments + timeouts + multi-party consent. Combines almost every CALC feature.

6. **Causality enforcement?** Bahr-Elsman's type system ensures future inputs don't affect present cash flows. Can this be expressed as a structural property in display calculus?

---

## Key References

1. Kanovich & Ito. "Temporal Linear Logic Specifications for Concurrent Processes." LICS, 1997.
2. Hirai. "Temporal Linear Logic and Its Applications." PhD thesis, JAIST, 2000.
3. Nakano. "A Modality for Recursion." LICS, 2000.
4. Peyton Jones, Eber, Seward. "Composing Contracts." ICFP, 2000.
5. Benton. "A Mixed Linear and Non-Linear Logic." 1995.
6. Martini & Masini. "A Modal View of Linear Logic." JSL, 1994.
7. Kamide. "Linear and Affine Logics with Temporal, Spatial and Epistemic Operators." TCS, 2006.
8. Kamide. "Temporal Non-Commutative Logic." LLP, 2009.
9. Reed. Adjoint logic generalization. 2009.
10. Krishnaswami & Benton. "Ultrametric Semantics of Reactive Programs." LICS, 2011.
11. Krishnaswami, Benton, Hoffmann. "Higher-Order FRP in Bounded Space." POPL, 2012.
12. Kamide. "Temporal Godel-Gentzen and Girard Translations." MLQ, 2013.
13. Despeyroux, Olarte, Pimentel. "Hybrid Linear Logic." TYPES 2013 / MSCS 2019.
14. Bocchi, Yang, Yoshida. "Timed Multiparty Session Types." CONCUR, 2014.
15. Bahr, Berthold, Elsman. "Certified Symbolic Management of Financial Multi-party Contracts." ICFP, 2015.
16. Licata & Shulman. "Adjoint Logic with a 2-Category of Modes." 2015.
17. Kanovich et al. "Timed Multiset Rewriting and Verification of TSDS." 2016.
18. Paykin, Krishnaswami, Zdancewic. "Linear Temporal Type Theory for Event-based Reactive Programming." 2016.
19. Das, Hoffmann, Pfenning. "Parallel Complexity Analysis with Temporal Session Types." ICFP, 2018.
20. Demri. "On Temporal and Separation Logics." TIME, 2018.
21. Fukuda & Yoshimizu. "A Linear-logical Reconstruction of IS4." FSCD, 2019.
22. Permenev et al. "VerX: Safety Verification of Smart Contracts." IEEE S&P, 2020.
23. Das, Pfenning. "Rast: Resource-Aware Session Types." FSCD, 2020.
24. Das, Balzer, Hoffmann, Pfenning. "Resource-Aware Session Types for Digital Contracts." CSF, 2021.
25. Marshall, Orchard. "Replicate, Reuse, Repeat." PLACES 2022 / Info&Comp, 2024.
26. de Sa, Toninho, Pfenning. "Intuitionistic Metric Temporal Logic." PPDP, 2023.
27. Hou, Lagaillardie, Yoshida. "Fearless Asynchronous Communications." ECOOP, 2024.
28. Pears, Bocchi. "Timeout Asynchronous Session Types." LMCS, 2025.
29. Mück et al. "Resource-Bounded Type Theory." arXiv, 2025.
30. Baelde & Miller. "Least and Greatest Fixed Points in Linear Logic." LPAR 2007 / TOCL, 2012.
31. Orchard et al. "Quantitative Program Reasoning with Graded Modal Types." ICFP, 2019.
32. Caires, Pfenning, Toninho. "Linear Logic Propositions as Session Types." MSCS, 2016.
