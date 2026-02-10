---
title: "Residuation: A Knowledge Base"
created: 2026-02-10
modified: 2026-02-10
summary: Comprehensive reference on residuation in residuated lattices connecting to Galois connections, display postulates, and logical connectives lacking residuals.
tags: [residuation, Galois-connection, display-calculus, residuated-lattices, adjunction]
---

# Residuation: A Knowledge Base

Comprehensive reference on residuation, its role in logic, and why it matters for display calculus.

> **See also:** [[display-calculus]] for display postulates, [[exponential-display-problem]] for why ! lacks residuals, [[QnA]] for tutorial questions, [[adjunctions-and-adjoint-logic]] for categorical perspective.

---

## Table of Contents

1. [Definition](#definition)
2. [Examples](#examples)
3. [Residuation in Linear Logic](#residuation-in-linear-logic)
4. [Left vs Right Residuals](#left-vs-right-residuals)
5. [When Commutativity Holds](#when-commutativity-holds)
6. [Connection to Galois Connections](#connection-to-galois-connections)
7. [Connection to Display Calculus](#connection-to-display-calculus)
8. [What Doesn't Have Residuals](#what-doesnt-have-residuals)

---

## Definition

### Algebraic Definition

In a **residuated lattice**, a binary operation `•` has **left and right residuals** `\` and `/` satisfying:

```
x • y ≤ z   iff   y ≤ x \ z   iff   x ≤ z / y
```

**Intuition:** The residuals are "division" operations that undo the effect of `•`.

### Logical Definition

A binary connective ⊗ is **residuated** if there exist connectives → and ← such that:

```
A ⊗ B ⊢ C   iff   A ⊢ B → C   iff   B ⊢ A ← C
```

**Intuition:** The implications "undo" the conjunction.

### Why "Residuation"?

The term comes from algebra. If `•` is multiplication, the residual `x \ z` is like "z divided by x" — what you multiply x by to get (at most) z.

---

## Examples

### Example 1: Classical Implication

In classical/intuitionistic logic:

```
A ∧ B ⊢ C   iff   A ⊢ B → C
```

Conjunction (∧) is residuated by implication (→).

**Proof:**
- (→) If A ∧ B ⊢ C, then assume A. From B, we get A ∧ B, hence C. So A ⊢ B → C.
- (←) If A ⊢ B → C, and we have A ∧ B, we have A and B. From A we get B → C. From B we get C.

### Example 2: Linear Logic Tensor

In linear logic:

```
A ⊗ B ⊢ C   iff   A ⊢ B ⊸ C
```

Tensor (⊗) is residuated by linear implication (⊸).

### Example 3: Relation Composition

In relation algebra, composition (;) is residuated:

```
R ; S ⊆ T   iff   R ⊆ T / S   iff   S ⊆ R \ T
```

Where `/` and `\` are "residual relations."

### Example 4: Lambek Calculus

In Lambek calculus (for natural language):

```
A • B ⊢ C   iff   A ⊢ C / B   iff   B ⊢ A \ C
```

The "slash" connectives are implications:
- `C / B` = "something that, followed by B, gives C"
- `A \ C` = "something that, preceded by A, gives C"

---

## Residuation in Linear Logic

### The Main Residuation

```
A ⊗ B ⊢ C   iff   A ⊢ B ⊸ C
```

This is the heart of linear logic's structure!

### Alternative Notation

The linear implication ⊸ is sometimes written in two forms:

- `A ⊸ B` (standard lolli)
- `B ○─ A` or `A -o B` (reverse lolli, sometimes used)

**In commutative linear logic, these are the same:**

```
A ⊸ B = A⊥ ⅋ B
```

### Definition via Negation

In classical linear logic:

```
A ⊸ B  :=  A⊥ ⅋ B
```

This shows that ⊸ is definable, not primitive.

### Why Only One Lolli?

**Your question:** In LL, isn't ⊸ == -o since tensor is commutative?

**Answer:** YES! In **commutative** linear logic, the left and right residuals coincide:

```
A ⊗ B ⊢ C
    iff (by residuation)
A ⊢ B ⊸ C
    iff (by commutativity of ⊗)
B ⊗ A ⊢ C
    iff (by residuation)
B ⊢ A ⊸ C
```

So `A ⊸ C` and `C ○─ A` (if we had both) would be inter-derivable.

**Standard LL uses only one symbol (⊸) because ⊗ is commutative.**

---

## Left vs Right Residuals

### When They Differ

In **non-commutative** logics, left and right residuals are DIFFERENT:

```
A • B ⊢ C   iff   A ⊢ C / B   iff   B ⊢ A \ C
```

- `C / B` is the **right residual**: "C divided by B on the right"
- `A \ C` is the **left residual**: "C divided by A on the left"

### Intuition via Time

From the Stanford Encyclopedia (Substructural Logics):

> "When the monoid is not commutative, the intuitive meaning can be understood as having a temporal quality:
> - `x • y` means 'x and then y'
> - `x \ y` means 'had x (in the past) then y (now)'
> - `y / x` means 'if-ever x (in the future) then y (at that time)'"

### Lambek Calculus Example

In linguistic analysis:

- `S / NP` = "something that needs an NP to its right to form a sentence" (verb phrase)
- `NP \ S` = "something that needs an NP to its left to form a sentence" (rare in English)

---

## When Commutativity Holds

### Commutative Case

If `•` is **commutative** (A • B = B • A), then:

```
A ⊢ B → C   iff   B ⊢ A → C
```

The left and right residuals **coincide** — there's only one implication.

### Examples of Commutative Residuation

| Logic | Operation | Residual |
|-------|-----------|----------|
| Classical | ∧ (commutative) | → (one implication) |
| Linear Logic | ⊗ (commutative) | ⊸ (one lolli) |
| Boolean Algebra | ∧ (commutative) | → (material implication) |

### Examples of Non-Commutative Residuation

| Logic | Operation | Left Residual | Right Residual |
|-------|-----------|---------------|----------------|
| Lambek | • (sequence) | \ | / |
| Ordered LL | ⊗ (ordered) | ⊸ᴸ | ⊸ᴿ |
| Relation Algebra | ; (composition) | \ | / |

---

## Connection to Galois Connections

### Definition of Galois Connection

A **Galois connection** between posets (A, ≤) and (B, ≤) consists of:

- f : A → B (lower adjoint)
- g : B → A (upper adjoint)

such that:

```
f(a) ≤ b   iff   a ≤ g(b)
```

### Residuation AS Galois Connection

For each fixed `a`, residuation gives a Galois connection:

```
f(b) = a • b          (tensor with a)
g(c) = a \ c          (residual by a)

a • b ≤ c   iff   b ≤ a \ c
```

So residuation IS a family of Galois connections, one for each element!

### Why This Matters

Galois connections preserve structure. If residuation holds, then:

- `•` preserves joins in each argument: a • (b ∨ c) = (a • b) ∨ (a • c)
- The residuals preserve meets: a \ (b ∧ c) = (a \ b) ∧ (a \ c)

This structural preservation is why residuation enables display postulates.

---

## Connection to Display Calculus

### The Core Insight

Display postulates ARE residuation at the structural level:

**Logical residuation:**
```
A ⊗ B ⊢ C   iff   A ⊢ B ⊸ C
```

**Structural residuation:**
```
X , Y ⊢ Z   iff   X ⊢ Y > Z
```

Where:
- `,` is the structural comma (counterpart of ⊗)
- `>` is the structural implication (counterpart of ⊸)

### Display Postulates = Residuation Rules

The display postulates let you "shuffle" structures:

```
X , Y ⊢ Z          Z ⊢ X ; Y
──────────── (DP)  ──────────── (DP')
X ⊢ Y > Z          Z < X ⊢ Y
```

These are exactly the residuation laws!

### Why Residuation Enables Display

If ⊗ is residuated by ⊸, then for ANY structure `X , Y ⊢ Z`:

1. You can move Y to the right: `X ⊢ Y > Z`
2. From there, you can move X: `I ⊢ X > (Y > Z)`

So you can **display** any part on either side!

### When Display Fails

If a connective is NOT residuated (like !), you CAN'T move it freely. The display postulate would be:

```
!X , Y ⊢ Z
──────────── (would-be DP)
!X ⊢ Y > Z
```

But this is **unsound** because ! has special properties (contraction, weakening) that shouldn't transfer to `Y > Z`.

---

## What Doesn't Have Residuals

### The Exponential ! (Bang)

**Claim:** The bang (!) is not residuated.

**Why?** If ! were residuated, we'd have some operation `?` such that:

```
!A ⊗ B ⊢ C   iff   !A ⊢ B ⊸ C   iff   B ⊢ ?(!A ⊸ C)   (hypothetical)
```

But ! allows **contraction**:

```
!A ⊢ !A ⊗ !A   (we can duplicate !A)
```

If we could move !A across freely via residuation, we'd get:

```
!A ⊗ !A ⊗ B ⊢ C   (use contraction on the left)
!A ⊢ (!A ⊗ B) ⊸ C   (move one !A right... but which one?)
```

The duplication on one side doesn't match the structure on the other!

**The real issue:** ! is a **comonad**, not a residuated operation. Comonads have:
- Counit: !A → A
- Comultiplication: !A → !!A

These don't fit the residuation pattern.

### Negation (in some logics)

Classical negation swaps sides:

```
A ⊢ B   iff   ¬B ⊢ ¬A
```

This is a **Galois connection** but **contravariant** (reverses order). It's not residuation in the standard sense.

Display calculus handles this with **structural negation** (*):

```
X ⊢ Y   iff   *Y ⊢ *X
```

### Fixpoint Operators

μX.φ(X) and νX.φ(X) don't have residuals because they're defined **recursively**, not **algebraically**.

---

## Summary Table

| Connective | Residuated? | By What? | Notes |
|------------|-------------|----------|-------|
| ⊗ (tensor) | ✅ Yes | ⊸ (lolli) | Core of linear logic |
| ∧ (classical and) | ✅ Yes | → (implication) | Standard logic |
| ⅋ (par) | ✅ Yes | ⊸ (via duality) | A ⅋ B = (A⊥ ⊗ B⊥)⊥ |
| & (with) | ✅ Yes | Itself (in a sense) | Additive, different structure |
| ! (bang) | ❌ No | — | Comonad, not residuated |
| ? (why-not) | ❌ No | — | Monad, not residuated |
| ¬ (negation) | ⚠️ Special | — | Contravariant Galois |
| μ, ν (fixpoints) | ❌ No | — | Recursive definition |

---

## Sources

- [Residuated lattice - Wikipedia](https://en.wikipedia.org/wiki/Residuated_lattice)
- [Substructural Logics (Stanford Encyclopedia)](https://plato.stanford.edu/entries/logic-substructural/)
- [Galois connection - Wikipedia](https://en.wikipedia.org/wiki/Galois_connection)
- [A Survey of Residuated Lattices (Jipsen & Tsinakis)](https://www1.chapman.edu/~jipsen/reslat/rljt020206.pdf)
- [Linear Logic (Stanford Encyclopedia)](https://plato.stanford.edu/entries/logic-linear/)

## Cross-References

See also in this knowledge base:
- [[exponential-display-problem]] — Why ! lacks residuals and the solution
- [[QnA]] — Q&A on residuation and structural connectives
- [[display-calculus]] — How residuation enables display postulates
- [[ANKI]] — Flashcards on residuation

---

*Last updated: 2026-01-27*
