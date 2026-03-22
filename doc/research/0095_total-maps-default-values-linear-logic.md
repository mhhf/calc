---
title: "Total Maps with Default Values in Linear Logic: Object-Level Solutions"
created: 2026-03-22
modified: 2026-03-22
summary: "Deep survey of object-level (logic-internal) approaches to representing total key-value maps with default values in linear logic and its extensions, motivated by the EVM storage problem."
tags:
  - linear-logic
  - forward-chaining
  - multiset-rewriting
  - subexponentials
  - adjoint-logic
  - coinduction
  - fixed-points
  - muMALL
  - graded-types
  - separation-logic
  - lnl
  - resource-semantics
  - storage
  - default
  - affine
  - with
  - semiring
  - QTT
category: "Forward Chaining"
---

# Total Maps with Default Values in Linear Logic: Object-Level Solutions

## The Problem

In ILL forward chaining (multiset rewriting), storage is modelled as linear facts `storage(K, V)` — one per key. Read operations consume and re-produce the fact; writes consume and replace. The problem: **what if key K has no fact?** The EVM semantics says "return 0." But pure ILL has no notion of "absent key defaults to 0."

The current CALC solution is a meta-level hack: declare `[default: _ 0]` and lazily inject `storage(K, 0)` into the linear state when first accessed. This is operational, not logical — it lives outside the object logic.

We want a **clean, object-level solution**: a declaration internal to the logic itself that says "for any key K not in the store, the value is 0."

---

## Candidate Approaches

### 1. mu-MALL: Greatest Fixed Points and Coinductive Storage

**Source:** Baelde & Miller, *Least and Greatest Fixed Points in Linear Logic* (TOCL 2012). Extended by Heath & Miller, *A Proof Theory for Model Checking* (JAR 2019).

**Core idea:** mu-MALL extends MALL with least fixed point operators (µ) and greatest fixed point operators (ν). The ν operator is coinductive — its proofs may be infinite, and it represents structures that always have "more to give."

**Key insight from the Proof Theory Blog (2024):** `!A` (bang) can be encoded as `νX.(1 & A & (X ⊗ X))`, using the coinduction rule (νR). This shows that the exponential can be seen as a stream of available copies.

**Direct application:** Define storage as a greatest fixed point — a coinductive total map:

```
Map(K, V, Default) := νX. (lookup(K) ⊸ (storage(K, V) ⊗ X))
                    & (lookup(K) ⊸ (storage(K, Default) ⊗ X))
```

Or more practically: represent the infinite default-everywhere store as a coinductive stream indexed by keys:

```
DefaultStore := νX. ∀K. (storage(K, 0) & X)
```

The ν/coinduction rule (νR in Baelde's system) says: to prove `νB`, it suffices to find a coinvariant S such that `S ⊸ B[S/X]`. This allows "lazy unrolling" — proving that reading any key produces 0 by coinductive step, without ever materializing all values.

**Verdict:** Theoretically sound. Greatest fixed points genuinely represent infinite, always-available structures. The proof of a coinductive proposition is an infinite proof object (or a circular proof with a productivity check). The key question for forward chaining is **computational**: the νR rule requires finding a coinvariant, which is like supplying a loop invariant. In proof *search*, νL (left elimination of a coinductive hypothesis) unfolds one step at a time, which operationally corresponds to "look up from the infinite store, taking the current key's value."

**Problem:** Standard mu-MALL is a proof theory framework, not directly a rewriting engine. Encoding forward chaining inside nu requires circular proof search, which is complex. The ν type introduces proof obligations (productivity) absent from the current CALC engine.

---

### 2. Subexponentials (SELL): Weakening-Only Modality as "Optional Resources"

**Source:** Nigam & Miller, *Algorithmic Specifications in Linear Logic with Subexponentials* (PPDP 2009). Nigam, *On Subexponentials, Focusing and Modalities in Concurrent Systems* (TCS).

**Core idea:** SELL (Subexponential Linear Logic) adds a pre-ordered family of exponentials `!_i` (and `?_i`) where each index `i` may or may not allow contraction (C) and weakening (W). The subexponential signature is a tuple `⟨I, ≤, W, C⟩`.

**Affine subexponential:** An index `a ∈ I` with `a ∈ W, a ∉ C` gives `!_a A` the rule:
- **Weakening** (`!_a W`): `!_a A` can be dropped without use.
- **No contraction**: `!_a A` cannot be duplicated; it can be used *at most once*.
- **Dereliction** (`!_a D`): from `!_a A`, derive `A` (consuming the `!_a A`).

This is exactly the **affine modality**: resources available zero or one times.

**Direct application:** Wrap each default storage value in an affine subexponential:

```
!_a storage(K, 0)   -- for each key K
```

An affine-boxed default is: (a) available for dereliction (use once → becomes linear `storage(K,0)`); (b) discardable (weakening: if never accessed, silently dropped); (c) not duplicable (no contraction: cannot get two copies of the default).

This is **exactly the desired semantics**: inject infinitely many `!_a storage(K, 0)` for all keys, and by weakening the unused ones are automatically garbage-collected at the end of execution.

**Concretely:** The rewrite rule for "read storage K when absent":

```
!_a storage(K, 0) ⊸ (storage(K, 0) ⊗ storage_val(K, 0))
```

The dereliction of `!_a storage(K, 0)` fires, producing one linear `storage(K, 0)` plus the result. The remaining (unused) `!_a storage(K', 0)` for all other `K'` are weakened away at the end.

**Verdict:** This is the most **operationally practical** approach. The affine subexponential has direct proof rules, the forward chaining semantics is clear, and it maps neatly onto SELL's focused proof search. The "infinite injection" is handled lazily: in practice you only create `!_a storage(K, 0)` for the K actually queried, because SELL's proof search is demand-driven (backward chain to find the relevant `!_a` modality). The problem is representing "for all K" — this requires a first-order version of SELL (FELL?) or a schema declaration.

---

### 3. Adjoint Logic (Pruiksma & Pfenning, 2018): Mode-Stratified Defaults

**Source:** Pruiksma, Chargin, Pfenning & Reed, *Adjoint Logic* (2018, CMU Tech Report). Lecture notes by Pfenning (CMU 15-836, 2023).

**Core idea:** Adjoint logic unifies multiple logics with different structural properties through **modes**, each with a structural rule set `σ(m) ⊆ {W, C}`:

| Mode | W | C | Interpretation |
|------|---|---|----------------|
| L (Linear) | — | — | Exactly once |
| A (Affine) | ✓ | — | At most once |
| U (Unrestricted) | ✓ | ✓ | Any number of times |

Modal operators `↑_m^n` (up-shift from mode n to m) and `↓_m^n` (down-shift) let propositions move between modes. The preorder `m ⊑ n` means "m is at most as permissive as n."

**Direct application:** Declare default storage in affine mode A, real storage in linear mode L:

```
[mode A]  default_storage(K : key) : storage_cell(K, 0)   -- for all K
[mode L]  storage(K, V) : storage_cell(K, V)              -- one per K
```

A "read with default" rule operates in linear mode but can shift down to affine mode to obtain the default:

```
read_default(K) : ↓_A^L storage_cell(K, 0) ⊸ storage_cell(K, 0) ⊗ val(K, 0)
```

The `↓_A^L` down-shift from affine A to linear L means: "extract one linear use of the affine default." Because A has weakening, unused defaults vanish. Because A lacks contraction, only one copy per key can be extracted.

**Verdict:** Clean and principled. Adjoint logic is already identified as subsuming both LNL and SELL (Pruiksma et al. note: "Linear logic, affine logic, strict logic, normal judgmental S4, lax logic, LNL, and normal intuitionistic subexponential linear logic can all be directly embedded in adjoint logic"). The mode-based reading gives a genuine object-level account. Implementation requires multi-mode proof search, which is more complex than single-mode ILL.

---

### 4. Bunched Implications (BI): Additive Context for Defaults

**Source:** O'Hearn & Pym, *The Logic of Bunched Implications* (BSL 1999). Reynolds, *Separation Logic* (LICS 2002).

**Core idea:** BI has *two* conjunctions with equal logical status:
- **Multiplicative (separating) conjunction** `A * B`: contexts split (linear-like, resource-sensitive)
- **Additive (sharing) conjunction** `A ∧ B`: contexts shared (intuitionistic-like, allows weakening + contraction)

Contexts in BI are *bunches* — trees with nodes labeled by either `;` (additive, shareable) or `,` (multiplicative, separating).

**Direct application:** Place default storage values in the *additive* (intuitionistic) zone of the context, and actual storage values in the *multiplicative* (linear) zone:

```
Γ_add ; Δ_lin ⊢ P
```

Where `Γ_add` contains `∀K. storage_default(K, 0)` (weakening + contraction available) and `Δ_lin` contains the actual `storage(K, V)` facts (consumed linearly).

A read rule first checks `Δ_lin` for `storage(K, _)` (multiplicative); if absent, falls back to `Γ_add` for `storage_default(K, 0)` (additive). Writes go to `Δ_lin`.

**Verdict:** BI already underpins separation logic, which has been used to reason about heap-like structures. The two-zone context is natural and well-studied. The "default context" is genuinely object-level: it's a standard additive hypothesis. The difficulty is that BI's forward chaining semantics has not been developed to the degree that ILL's has — existing tools (Ceptre, CLF, etc.) work in ILL, not BI.

---

### 5. LNL (Benton's Linear/Non-Linear Adjunction): Cartesian Defaults Projected into Linear World

**Source:** Benton, *A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models* (CSL 1994). nLab: *linear-nonlinear logic*.

**Core idea:** LNL decomposes `!A` into an adjunction `F ⊣ G` between:
- `C`: a *cartesian* category (full weakening + contraction; models intuitionistic logic)
- `L`: a *symmetric monoidal closed* category (no structural rules; models linear logic)

`F : C → L` sends a cartesian type to a linear type, with `FA` carrying exactly the structural rules needed. The unit `η : Id → GF` and counit `ε : FG → Id` mediate between worlds.

**Direct application:** The default storage total function `f : Key → Val` lives in `C` (cartesian world — total, freely copyable). Project it into `L` via `F`:

```
F(default_store) : L
```

In `L`, `F(default_store)` has the structural rules inherited from `C` via `F` (specifically, `F(A)` is isomorphic to `!A` in standard presentations). The proof rule:

```
Dereliction: F(A) ⊢_L A    (consume one copy)
Weakening:   Γ ⊢_L P  →  Γ, F(A) ⊢_L P  (discard unused)
```

The total default function is `F(λK. 0)` — a cartesian function projected into linear context. Each access consumes one copy; projection from `C` can only produce a new copy if you explicitly ask (this is the `!` promotion rule).

**Verdict:** LNL makes the `!` modality a derived construct from an underlying adjunction. In terms of object-level cleanliness, this is arguably the most foundational approach: the cartesian world genuinely houses "total, freely available" data, and the adjunction functor `F` is the principled mechanism for bringing it into the linear world. Implementation in CALC would require extending the engine to handle two contexts (linear + cartesian) and the `F`/`G` shift operators.

---

### 6. The Additive "With" Connective (&): Lazy Default Choice

**Source:** Girard, *Linear Logic* (TCS 1987). Andreoli, *Logic Programming with Focusing Proofs in Linear Logic* (JLC 1992).

**Core idea:** `A & B` ("with") is the additive conjunction: the proof system provides both `A` and `B`, but the environment *chooses* which to use — only one branch is ever exploited.

**Application attempt:** Consider `∀K. (storage(K, 0) & 1)`:

- The `storage(K, 0)` branch: use this default value (consume it).
- The `1` branch (unit): discard it without producing any storage fact.

This says: "For each key K, you may either take the default storage(K,0), or discard this offer entirely."

**More directly:** In a backward-chaining proof goal `storage(K, ?V)`:
- If there exists `storage(K, V)` in the linear context: use it (multiplicative)
- Otherwise: unfold `∀K. (storage(K, 0) & 1)`, choosing the left branch to get `storage(K, 0)`

In forward chaining with the lollimon-style rules: add a persistent (unrestricted) axiom:

```
∀K V. storage_or_default(K, V) ⊸ (storage(K, V) & storage_result(K, 0))
```

**Verdict:** The `&` connective's semantics does provide "choose one branch" behavior, but it doesn't directly solve the forward chaining problem because `&` is a *choice offered by the prover to the environment*, not a conditional check. In backward proof search, the focused proof system handles `&R` by splitting goals — this doesn't help forward chaining. More importantly, `∀K. (storage(K,0) & 1)` requires the `∀K` to range over an infinite domain (all possible keys), which creates the same infinite-injection problem as the meta-level hack. The & approach is more useful in a backward-chaining context, not forward.

---

### 7. Graded Modal Types (Granule / QTT): Semiring-Based Optional Resources

**Source:** Orchard & Liepelt, *Quantitative Program Reasoning with Graded Modal Types* (ICFP 2019). Brady, *Idris 2: Quantitative Type Theory in Practice* (ECOOP 2021). Vollmer et al., *A Mixed Linear and Graded Logic: Proofs, Terms, and Models* (CSL 2025, arXiv 2024).

**Core idea:** In Quantitative Type Theory (QTT) and graded type systems, variables carry **usage grades** drawn from a semiring `(R, +, ×, 0, 1)`. The zero-one-many semiring `{0, 1, ω}` (used in Idris 2) distinguishes:

- Grade `0`: erased at runtime (irrelevant); can be weakened freely
- Grade `1`: used exactly once (linear)
- Grade `ω`: used any number of times (unrestricted)

The **interval semiring** `[0..1]` (or more generally `{0, 1}` under addition saturating at 1) directly captures "zero or one" usage — precisely affine behavior.

In the mixed linear/graded logic (mGL) of Vollmer et al., sequents have the form:

```
δ ⊙ ∆ ; Γ ⊢ A
```

where `δ` is a grade vector, `∆` is a graded context, and `Γ` is a linear context. **Weakening** is via the zero grade: `[0]A` can be discarded. **Contraction** is via semiring addition: `[r]A, [s]A` combine to `[r+s]A`.

**Direct application:** Declare defaults with grade `[0..1]` (interval semiring, or equivalently grade 0 in the 0-1-ω semiring with the interpretation "0 means present but unused"):

```
∀K : Key. [0..1] storage(K, 0)
```

This typing says: each default `storage(K, 0)` may be used zero or one times. On any execution path:
- If K is accessed and has no explicit `storage(K, V)` fact, consume the grade-1 use of `[0..1] storage(K, 0)`.
- If K is never accessed, the grade-0 case applies (free weakening).
- The grade can never become 2+ (no contraction under the `[0..1]` semiring).

**Verdict:** QTT-style graded types give the cleanest type-theoretic account. The Vollmer et al. (2025) paper directly provides the mixed linear+graded calculus. However, like adjoint logic, this requires a richer calculus than plain ILL. The semiring grade on the default hypothesis replaces the meta-level annotation with a type-level annotation — arguably the most principled type-theoretic approach available.

---

### 8. Polarized Linear Logic: Negative Types as Lazy Demand

**Source:** Girard, *On the Unity of Logic* (1993). Laurent, *Polarized Linear Logic* (2002).

**Core idea:** In polarized linear logic (LLP), formulas are either **positive** (synchronous, eager) or **negative** (asynchronous, lazy). Negative connectives (`&`, `⊤`, `⅋`, `?`, `⊸`) are invertible — their right rules decompose immediately, without choices. Positive connectives (`⊗`, `⊕`, `1`, `0`, `!`) require synchronous focusing.

**Application:** Represent the default storage as a **negative** (lazy) type. A negative formula `storage_neg(K, 0)` does not materialize until demanded — its introduction rule is invertible (always applicable without committing), and the proof engine "unfolds" it lazily when the goal requires `storage(_, _)`.

In focusing proofs: a negative formula in the context is *always available* to be unfolded. A positive literal `storage(K, V)` is consumed. So:

- Active `storage(K, V)`: positive, synchronous, consumed on use
- Default `storage_neg(K, 0)`: negative, asynchronous, always present but lazy

The key property: negative formulas in the context sit in the "stable zone" — they're never consumed and can be unfolded as many times as needed. This is exactly `?A` (why-not) or `!A` (of-course) semantics.

**Verdict:** Polarized linear logic doesn't add the structural rules we need — `?A` (negative exponential) still allows unbounded contraction. What we want is "use at most once but lazily." Negative polarity alone doesn't solve the default problem; it clarifies the proof-search dynamics, but the fundamental issue of at-most-once use requires additional structure (grading or subexponentials). Polarization is relevant for the *implementation* of any of the above approaches within the CALC focused proof search.

---

### 9. The "Why Not" (?) Modality: Duality to Bang

In classical linear logic, `?A` (why-not) is the de Morgan dual of `!A`. Where `!A` admits promotion (Γ, !A ⊢ B ↔ Γ ⊢ B with contraction+weakening for B), `?A` admits similar structural rules on the left. In ILL (without classical negation), `?A` is less studied.

**Key property:** `?A` admits weakening and contraction just like `!A`. It does *not* give us at-most-once semantics. `?A` is not what we want for defaults: `?A` is "I have infinitely many A", not "I have zero or one A".

**Verdict:** Not directly useful for the default problem. The dual `?` does not provide the "at most once" constraint.

---

### 10. Separation Logic (magic wand): Conditional Default via —*

**Source:** Reynolds, *Separation Logic* (LICS 2002). O'Hearn, *Separation Logic* (CACM 2019).

**Core idea:** The magic wand `P —* Q` ("if you give me P, I will give you Q, consuming P"). In separation logic over a *partial heap*, if key K is absent, `storage(K, ?)` is simply undefined — no value exists.

The "total heap" approach makes heaps total functions from addresses to values (possibly with a distinguished "uninitialized" value). Yang's work shows that total vs partial heap semantics are isomorphic up to explicit initialization tracking.

**Application attempt:** Define a total storage proposition:

```
TotalStorage := ∀K. (storage(K, ?) -* storage_answer(K))
```

Where `storage_answer(K)` resolves to `V` if `storage(K,V)` is present, or `0` if absent. The problem: the magic wand `P -* Q` in separation logic has *decidability issues* (Brotherston et al. show it quickly leads to undecidability). Furthermore, `—*` in linear logic is just `⊸` — the linear implication. So `storage(K, ?) —* storage_answer(K)` is just a loli/rule, not a default specification.

**Verdict:** Separation logic over total heaps handles the "default value" case by having all keys present (with a sentinel for "uninitialized"). This is isomorphic to the meta-level injection hack: you pre-populate the "heap" with zeros. No fundamental gain. The magic wand does not help because it's just implication, not a conditional presence check.

---

### 11. First-Order Quantification + Bang: The `!∀K. storage(K, 0)` Approach

In plain ILL with first-order quantifiers, the cleanest internal declaration is:

```
!∀K : Key. (storage(K, 0) & 1)
```

Or equivalently as a persistent (unrestricted) rule schema:

```
Γ, !∀K. storage(K, 0) ⊢_ILL P
```

The `!∀K` says: for any key K, a `storage(K, 0)` fact is always available (contraction) and discardable (weakening). However, this has a **double-use problem**: `!` with contraction allows extracting *multiple* copies of `storage(K, 0)` for the same K, leading to multiplicities > 1 which break the single-copy invariant of storage facts.

To fix this: `storage(K, 0) & 1` (additive with unit) means "use it or discard it" — but still allows contraction via `!` to get multiple copies of `(storage(K,0) & 1)`.

The only way to prevent duplication while allowing discarding in pure ILL is to combine `!` with the `& 1` form *and* add a side condition (meta-level again) that each key's default is used at most once — or move to a richer calculus.

**Verdict:** This approach fails in pure ILL because `!` provides both weakening *and* contraction. To get weakening-only, you need affine subexponentials (approach 2), adjoint logic (approach 3), or graded modalities (approach 7).

---

### 12. Dependent Linear Types + Irrelevance

**Source:** McBride, *Idris 2: Quantitative Type Theory in Practice*. Atkey, *Syntax and Semantics of Quantitative Type Theory* (LICS 2018). Wood & Atkey, *A Linear Algebra Approach to Linear Metatheory* (2022).

**Core idea:** In dependent type theories with usage grades (QTT), a grade-0 variable is computationally *irrelevant* — present in the type but erased from terms. In a dependent linear type system:

```
(K : Key)[0] → storage(K, 0)   -- the K is irrelevant at grade 0
```

"Irrelevance" here means: the *index* K is not used to compute a term, it's only used for typing. An irrelevant hypothesis can be freely weakened (never consumed) or specialized (instantiated).

**For defaults:** If the default `storage(K, 0)` has its key K at grade 0 (irrelevant), then: (a) the fact can be weakened (K is not actually used to run code, only to type the fact); (b) the fact itself still needs a usage grade. Grade `[1]storage(K, 0)` with grade-0 index K would mean "use this storage fact exactly once, but the key K is erased." This doesn't quite capture "for all keys, use at most once."

**Verdict:** Dependent irrelevance applies to *indices* (keys), not to the facts themselves. It doesn't directly solve the at-most-once problem for individual key slots. Combined with the interval semiring (approach 7), it could express "for all keys K (irrelevantly indexed), a `[0..1]`-graded `storage(K, 0)` fact".

---

## Synthesis and Ranking

The following ranks the candidates by (a) theoretical cleanliness, (b) proximity to CALC's existing architecture, (c) practicality for forward-chaining multiset rewriting:

| Approach | Theory | Object-Level? | Practical for FC? | Notes |
|---|---|---|---|---|
| **Affine subexponentials (SELL)** | SELL | ✓ | Best | Weakening-only `!_a`: directly encodable in focused proof search. Most practical extension. |
| **Adjoint logic (modes)** | Adjoint Logic | ✓ | Good | Subsumes SELL; affine mode is the right level. Multi-mode engine needed. |
| **Graded types ([0..1] semiring)** | mGL / QTT | ✓ | Good | Cleanest type-theoretic formulation; needs semiring-aware engine. |
| **LNL adjunction** | LNL | ✓ | Moderate | `F(default)` is principled; needs two-context engine. |
| **BI logic (additive context)** | BI | ✓ | Moderate | Two-zone context; semantically natural but BI engine unavailable. |
| **mu-MALL (ν fixed points)** | mu-MALL | ✓ | Hard | Correct but needs circular/coinductive proof search. |
| **& additive choice** | ILL | ✓ | Partial | Works backward, not forward; `∀K` over infinite domain is problematic. |
| **Polarized LL (negative types)** | PLL | ✓ | Auxiliary | Clarifies dynamics but doesn't add structural rules. |
| **? why-not modality** | CLL | ✗ | No | Contraction + weakening — too strong. |
| **Dependent irrelevance** | QTT | Partial | Auxiliary | Handles key indices but not value slots. |
| **Separation logic —*** | SL | Partial | No | Isomorphic to meta-level injection. |
| **Pure ILL `!∀K`** | ILL | ✗ | No | Contraction breaks single-copy invariant. |

---

## The Cleanest Object-Level Solution

**Affine subexponential** is the most directly implementable clean solution:

Define a subexponential signature `⟨{lin, aff}, ≤, W={aff}, C={}⟩` with `aff ≤ lin`. The default storage declaration becomes:

```
!_aff (∀K : Key. storage(K, 0))
```

Or in a first-order SELL, as a *schema* (rule template):

```
Default[K] :  !_aff storage(K, 0)
```

This is object-level: it's a formula in SELL, not a meta-level annotation. The structural rules are built into the logic:
- **Weakening for `!_aff`**: Unused `!_aff storage(K, 0)` facts are silently discarded at end of derivation.
- **Dereliction for `!_aff`**: Consuming `!_aff storage(K, 0)` yields one linear `storage(K, 0)`.
- **No contraction for `!_aff`**: Cannot extract two copies of `storage(K, 0)` from one `!_aff storage(K, 0)`.

In the **focused proof system** for SELL, the `!_aff` modality sits in the negative (asynchronous) zone — it can be unfolded lazily during left-asynchronous phase, which corresponds to "check if default is needed" in forward chaining.

The forward chaining rule for "read with default" becomes logically:

```
!_aff storage(K, 0) ⊗ !∀K'. storage(K', _) ⊸ ...  [existing facts take priority]
```

with a priority ordering: linear `storage(K, V)` facts (consumed-reproduced in reads) take precedence over the affine `!_aff storage(K, 0)` defaults. This priority is naturally encoded by the subexponential preorder.

---

## Key References

- Baelde & Miller, *Least and Greatest Fixed Points in Linear Logic*, TOCL 2012. [arXiv:0910.3383](https://arxiv.org/abs/0910.3383)
- Nigam & Miller, *Algorithmic Specifications in Linear Logic with Subexponentials*, PPDP 2009. [PDF](https://www.lix.polytechnique.fr/~dale/papers/ppdp09.pdf)
- Nigam, *On Subexponentials, Focusing and Modalities in Concurrent Systems*, TCS. [PDF](http://nigam.info/docs/tcs-sellU.pdf)
- Pruiksma, Chargin, Pfenning & Reed, *Adjoint Logic*, CMU 2018. [PDF](https://www.cs.cmu.edu/~fp/papers/adjoint18b.pdf)
- Benton, *A Mixed Linear and Non-Linear Logic*, CSL 1994. [SpringerLink](https://link.springer.com/chapter/10.1007/BFb0022251)
- O'Hearn & Pym, *The Logic of Bunched Implications*, BSL 1999. [CambridgeCore](https://www.cambridge.org/core/journals/bulletin-of-symbolic-logic/article/abs/logic-of-bunched-implications/74E6C2D31AED03DAD066432061BF6B78)
- Vollmer, Marshall, Eades & Orchard, *A Mixed Linear and Graded Logic*, CSL 2025. [arXiv:2401.17199](https://arxiv.org/abs/2401.17199)
- Orchard & Liepelt, *Quantitative Program Reasoning with Graded Modal Types*, ICFP 2019. [PDF](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf)
- Heath & Miller, *A Proof Theory for Model Checking*, JAR 2019. [HAL](https://inria.hal.science/hal-01814006/document)
- Proof Theory Blog, *Exponentials vs Fixed Points in Linear Logic*, 2024. [Link](https://prooftheory.blog/2024/06/27/exponentials-vs-fixed-points-in-linear-logic/)
- Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS 2018. [PDF](https://bentnib.org/quantitative-type-theory.pdf)
- Brady, *Idris 2: Quantitative Type Theory in Practice*, ECOOP 2021. [arXiv:2104.00480](https://arxiv.org/abs/2104.00480)
