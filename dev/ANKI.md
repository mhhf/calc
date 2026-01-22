# ANKI.md

Flashcard-style definitions for key concepts. Format: **Term** → Definition

---

## Proof Theory Terminology

**Proof calculus / Proof system**
→ Synonymous. A formal system for constructing proofs (axioms + inference rules). Examples: sequent calculus, natural deduction, Hilbert systems.

**Proof formalism**
→ The "shape" or "syntax" of judgments that the proof system manipulates. Defines what objects you write down and manipulate during proof construction.
- Sequents: `Γ ⊢ Δ`
- Hypersequents: `Γ₁ ⊢ Δ₁ | Γ₂ ⊢ Δ₂ | ...`
- Nested sequents: `Γ ⊢ Δ, [Γ' ⊢ Δ']`
- Display structures: `X ; Y ⊢ Z` with structural connectives
- Labelled sequents: `w:A, wRv, v:B ⊢ w:C` with explicit worlds/labels

**Proof search strategy**
→ How you search for proofs. Orthogonal to the formalism - you can apply different strategies to the same formalism.
- Focusing: alternating invertible/non-invertible phases
- Tableaux: tree-based refutation
- Resolution: clause-based contradiction finding

**Proof representation**
→ How you represent completed proofs. May differ from how you search.
- Trees: standard derivation trees
- Proof nets: graphs that quotient away "bureaucracy"
- Lambda terms: via Curry-Howard

**Canonical proof**
→ A unique representative for each equivalence class of "essentially same" proofs. Two proofs are "essentially same" if they differ only in irrelevant details (rule order, associativity, etc.).

---

## Linear Logic Connectives

**Tensor (⊗)**
→ Multiplicative conjunction. "I have both A AND B simultaneously, as separate resources."

**Par (⅋)**
→ Multiplicative disjunction. De Morgan dual of tensor: `A ⅋ B = (A⊥ ⊗ B⊥)⊥`. Hard to interpret as resources; better understood via game semantics or as "entangled disjunction."

**With (&)**
→ Additive conjunction. "I can choose to use A OR to use B, but not both."

**Plus (⊕)**
→ Additive disjunction. "Either A or B is available, but I don't control which."

**Lollipop (⊸)**
→ Linear implication. "Consuming A produces B." Defined as `A ⊸ B = A⊥ ⅋ B`.

**Bang (!)**
→ Exponential "of course". Allows unlimited use (contraction/weakening). "As many copies of A as needed."

**Why Not (?)**
→ Exponential dual of bang. `?A = (!A⊥)⊥`. Allows structural rules on the left.

---

## Polarity

**Positive connectives**
→ ⊗, ⊕, !, 1, 0, atoms. Rules are invertible on the LEFT, non-invertible on the RIGHT.

**Negative connectives**
→ ⅋, &, ?, ⊥, ⊤, ⊸. Rules are invertible on the RIGHT, non-invertible on the LEFT.

**Focusing**
→ Proof search strategy based on polarity. Alternate between:
1. **Async phase**: eagerly apply invertible rules (no backtracking needed)
2. **Sync phase**: choose a formula, apply non-invertible rules until done

---

## Display Calculus

**Display calculus**
→ Proof formalism introduced by Belnap (1982). Uses structural connectives that mirror logical connectives, plus display postulates to shuffle structures around.

**Display property**
→ Any formula occurrence can be "displayed" (made the sole occupant of one side of the turnstile) using only display postulates.

**Display postulate**
→ A rule that rearranges structures without changing provability. Example: `X ; Y ⊢ Z ↔ X ⊢ Y > Z` (residuation).

**Structural connective**
→ A connective at the structure level (not formula level) that mirrors a logical connective. E.g., `;` mirrors ⊗, `>` mirrors ⊸.

**Belnap's conditions (C1-C8)**
→ Eight syntactic conditions. If a display calculus satisfies them, cut elimination is guaranteed.

---

## Residuation

**Residuation**
→ An adjunction/Galois connection between connectives. For tensor: `A ⊗ B ⊢ C` iff `A ⊢ B ⊸ C` iff `B ⊢ A −○ C`.

**Left residual**
→ Given `A ⊗ B ⊢ C`, the left residual `B ⊸ C` is what A must imply.

**Right residual**
→ Given `A ⊗ B ⊢ C`, the right residual `A −○ C` is what B must imply.

---

## Other Proof Formalisms

**Hypersequent**
→ A multiset of sequents: `Γ₁ ⊢ Δ₁ | Γ₂ ⊢ Δ₂ | ...`. Read as "at least one component is provable."

**Nested sequent**
→ Sequents containing sequents recursively (tree structure). More expressive than hypersequents.

**Labelled sequent**
→ Sequents with explicit labels (worlds) and accessibility relations. Most expressive, but "external" (encodes semantics).

**Deep inference**
→ Rules can apply anywhere inside a structure, not just at the root. Eliminates need for display postulates.

**Proof net**
→ Graphical proof representation. Quotients away "bureaucratic" differences between sequent proofs. Cut elimination is local graph rewriting.

---

## Hierarchy of Expressiveness

**Less expressive → More expressive:**
Standard sequent < Hypersequent < Nested sequent < Display calculus ≈ Labelled sequent

**Trade-off:** More expressive = can handle more logics, but harder to prove meta-properties and may lose subformula property or internality.

---

*Last updated: 2026-01-21*
