---
title: "Least Fixed Points: Induction"
part: 6
partTitle: Induction and Coinduction
chapter: 22
summary: A least fixed point μX.F is data built from a base case up — a number, a list, a tree. This chapter adds μ to the logic as a connective with an unfold rule, and shows how inductive types and finite recursion become proofs.
---

Everything in the book so far has been *finite and flat*. A sequent has a
fixed set of resources; a proof tree has a fixed shape. But real data is
**recursive**: a number is zero, or one more than a number. A list is empty,
or an item followed by a list. A tree is a leaf, or a branch holding trees.

Plain linear logic cannot say "or one more than a *number*" — it has no way to
refer to the thing it is defining. This chapter adds that missing power with a
single connective, the **least fixed point** `μ`. It opens a new part of the
book: reasoning about data that recurses, and proofs that do too.

## The shape of recursion

Look at the definition of a natural number:

> A `Nat` is either **zero**, or the **successor** of a `Nat`.

The word `Nat` appears on both sides. If we write the two cases with the
connectives you already know — `I` for the zero case (a unit, no data) and `⊕`
for the choice between them — we get an equation:

$$\mathrm{Nat} \;=\; I \oplus \mathrm{Nat}.$$

This is a **fixed-point equation**: `Nat` is a solution `X` of `X = I ⊕ X`.
Writing the right-hand side as a function of `X`, call it $F(X) = I \oplus X$,
we want an `X` with $X = F(X)$ — a *fixed point* of `F`.

There can be more than one solution. The **least** one contains only the
values you can build in *finitely* many steps: zero, the successor of zero, the
successor of that, and so on. Nothing infinite sneaks in. That least solution
is what we write `μX.F`:

$$\mathrm{Nat} \;:=\; \mu X.\,(I \oplus X).$$

Read `μX.` as "the smallest `X` such that `X` equals the body." The body is
`I ⊕ X`, and inside it, `X` refers back to the whole `μX.(I ⊕ X)`.

## Writing μ in CALC

In source you write a least fixed point as `mu X. F`, where `X` is the
recursion variable and `F` is the body:

```
mu X. (I + X)              % Nat: zero (I) or successor (X)
mu X. (I + (a * X))        % List of a: empty (I) or an a then a list
mu X. (a & X)              % a stream of a's you may stop reading at any point
```

`μ` is a binder, just like `∃` and `∀` from earlier chapters: `X` is bound
inside the body. It is a **positive** connective — like `⊗`, `⊕`, and `!`, it
describes something you *build*.

```{quiz, id=ch22-q1}
Q: A binary tree with values of type `a` at its leaves is either a single leaf holding an `a`, or a branch holding two subtrees. Which fixed point captures it?
- [x] `mu X. (a + (X * X))` — a leaf (`a`) or a branch pairing two subtrees (`X * X`).
- [ ] `mu X. (a & (X * X))` — the `&` would let you pick just one side.
- [ ] `nu X. (a + (X * X))` — `nu` allows infinite trees; a finite tree is a *least* fixed point.
- [ ] `a * X * X` — this never bottoms out; there is no base case.
explanation: A finite tree is built from the base case (a leaf) upward in finitely many steps — a least fixed point μ. The body offers a choice (⊕) between a leaf `a` and a branch that pairs (⊗) two recursive subtrees.
```

## The unfold rule

How do you prove something *about* a `μ` type, or prove that a value *has* one?
You **unfold** it. The defining equation `μX.F = F[μX.F/X]` (substitute the
whole fixed point back in for `X`) is the celebrated **Knaster–Tarski**
identity, and it is exactly the inference rule.

On the right (building a value), unfolding needs focus — you are making a
choice about how to construct:

$$
\frac{\Gamma \;;\; \Delta \vdash F[\mu X.F / X]}
     {\Gamma \;;\; \Delta \vdash \mu X.F}\;\mu R
$$

On the left (using a value), unfolding is invertible — a `μ` hypothesis can
always be safely opened:

$$
\frac{\Gamma \;;\; \Delta,\; F[\mu X.F / X] \vdash C}
     {\Gamma \;;\; \Delta,\; \mu X.F \vdash C}\;\mu L
$$

There is no fresh variable and no guessing: the premise is the body with the
*whole* fixed point plugged back in. Because the substitution is completely
determined, the trusted kernel re-derives it exactly — an unfolding cannot be
forged.

## Proving zero is a Nat

Let us build the simplest value: zero. The goal is `⊢ μX.(I ⊕ X)`. There is no
data, so the linear context is empty.

1. **μR** unfolds the goal to `⊢ I ⊕ (μX.(I ⊕ X))`.
2. **⊕R₁** picks the left case (zero): `⊢ I`.
3. **1R** closes it.

Three steps, and zero is proven to inhabit `Nat`. The successor of zero would
add one `μR`/`⊕R₂` pair on top before reaching `I` — each extra step is one
more `succ`.

## Using a μ on the left: induction in miniature

The real power of `μ` is on the *left*. Because `μL` is invertible, a recursive
hypothesis can always be unfolded and case-analyzed. Take
`μX.(a & X) ⊢ a` — "from a value that always offers an `a` (and a way to
continue), extract one `a`":

1. **μL** unfolds the hypothesis to `a & (μX.(a & X)) ⊢ a`.
2. **with_l₁** keeps the left component of the `&`: `a ⊢ a`.
3. **id** closes it.

After the unfold, what remains is an ordinary ILL sequent — the `&` you learned
in Chapter 4. The recursion added nothing new to *this* step; it just handed
you the unfolded body. Prove that ordinary landing sequent live (the recursive
part is already gone — `c` here stands for the leftover `μ` hypothesis you
chose not to use):

```{prove}
goal: a & c |- a
title: The landing sequent after one μL unfold
hint: The hypothesis is an additive pair. Use with_l1 to keep its left half, then close with id.
id: ch22-with-l1
rules: id, with_l1, with_l2
```

That is the pattern for **induction**: unfold the recursive hypothesis, handle
the base case directly, and handle the step case by using the (smaller)
recursive occurrence the unfold exposed. Because `μ` is the *least* fixed point,
every value is finite, so this process always bottoms out.

```{quiz, id=ch22-q2}
Q: Why is unfolding a `μ` hypothesis on the left (`μL`) invertible — safe to apply eagerly — while unfolding on the right (`μR`) needs focus?
- [x] Opening a value you *have* loses no information (you can always see its structure), but building a value you must *produce* is a committed choice about which case to construct.
- [ ] `μL` is invertible only for `Nat`, not for other μ types.
- [ ] `μR` is actually invertible too; the distinction is cosmetic.
- [ ] Left rules are always invertible and right rules never are.
explanation: Invertibility is about whether a rule can be applied without cutting off proofs. Decomposing a hypothesis (`μL`) is always safe — the unfolded form carries the same information. Constructing a goal (`μR`, then picking ⊕R₁ vs ⊕R₂) is a genuine choice that focusing must manage. This mirrors the polarity story from Chapter 6: positive connectives are eager on the left, deliberate on the right.
```

## What μ gives, and what it does not

`μ` gives you **inductive data** — numbers, lists, finite trees — and **finite
recursion** over it by repeated unfolding. Every value bottoms out at a base
case, so proofs that decompose a `μ` hypothesis terminate.

What `μ` deliberately does *not* give you, on its own, is *infinite* data or
proofs that run forever. A value that never reaches a base case — an endless
stream, a signal that is always available — is not a least fixed point at all.
It is a **greatest** fixed point, and reasoning about it needs a genuinely new
kind of proof: one that closes a loop. That is the subject of the next chapter.

```{exercise, title=One, two, three}
Using only `mu X. (I + X)` for `Nat`, write out (on paper) the sequence of
rules that proves `⊢ mu X. (I + X)` represents the number **two** (the
successor of the successor of zero). How many `μR` unfolds does it take, and
which `⊕` injection ends the proof?
```

```{solution}
Two is `succ (succ zero)`, so you unfold three times, taking the successor
branch twice and the zero branch once:

1. `μR`, then `⊕R₂` (successor) → goal becomes `⊢ μX.(I ⊕ X)` again;
2. `μR`, then `⊕R₂` (successor) → goal becomes `⊢ μX.(I ⊕ X)` again;
3. `μR`, then `⊕R₁` (zero) → `⊢ I`, closed by `1R`.

Three `μR` unfolds in total: two successors and the final zero. Each `⊕R₂` is
"add one"; the single `⊕R₁` is "stop at zero." The number *is* the shape of its
proof.
```

## What you learned

- A **fixed-point equation** `X = F(X)` can have many solutions; the **least**
  one, written `μX.F`, contains exactly the values built from a base case in
  finitely many steps.
- Inductive types are least fixed points: `Nat = μX.(I ⊕ X)`,
  `List(a) = μX.(I ⊕ (a ⊗ X))`, finite trees `μX.(a ⊕ (X ⊗ X))`.
- In source, `mu X. F` is a positive binder connective (like `∃`).
- The **unfold rule** is the Knaster–Tarski identity `μX.F = F[μX.F/X]`: `μR`
  (focus, building) and `μL` (invertible, using) both replace the fixed point
  with its body, the whole fixed point plugged back in for `X`.
- **Induction** is `μL` plus finite descent: unfold the hypothesis, discharge
  the base case, use the smaller recursive occurrence for the step case.
- `μ` gives finite, well-founded data. Infinite data — streams and signals —
  needs the *greatest* fixed point `ν` and the looping proofs of the next
  chapter.

## Going deeper

- [[theory/0042_cyclic-proofs-fixed-points|THY_0042: fixed points and cyclic proofs]] — the full treatment of μ/ν as declared connectives, the `@binding unfold` mode that makes unfolding kernel-checkable, and the cyclic-proof system for the coinductive half.
- [[def/0005_internal-vs-external-choice|internal vs external choice]] — the `⊕`/`&` distinction that appears inside almost every fixed-point body.
- [[documentation/architecture|the prover architecture]] — where the fixed-point calculus `fill` sits, firewalled from production ILL so the EVM proof path carries no recursion machinery.
