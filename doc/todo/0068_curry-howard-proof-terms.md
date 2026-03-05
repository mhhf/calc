---
title: "Curry-Howard Proof Terms for ILL"
created: 2026-03-05
modified: 2026-03-05
summary: "Assign proof terms to all ILL connectives via the Curry-Howard correspondence. Two-layer design: Layer 1 generic terms derived from rule descriptors (rule name = constructor), Layer 2 optional interpretation maps (lambda, session types, etc.). Subsumes TODO_0067."
tags: [proof-theory, clf, linear-logic, curry-howard, lax-monad, architecture, verification, soundness, logical-framework]
type: design
cluster: Theory
status: planning
priority: 9
depends_on: []
required_by: [TODO_0045, TODO_0008]
starred: true
---

# Curry-Howard Proof Terms for ILL

## 1. Goal

Assign proof terms to every ILL derivation. A derivation of sequent `Γ; Δ ⊢ A` produces a term `t` such that `t : A`. The term is the computational content of the proof — it records *how* A was proved, not just *that* it was proved.

This is the standard Curry-Howard correspondence applied to CALC's intuitionistic linear logic with lax monad.

**What this gives us:**
- Proofs are first-class data (content-addressed in Store, serializable, composable)
- Type-checking a term against a type = verifying a proof (de Bruijn criterion)
- Forward execution produces monadic let-bindings (CLF proof terms)
- The monad_r trust gap closes: `{E} : {S}` is verified by type-checking E
- Experimentable: Layer 1 generic terms derived free from descriptors, Layer 2 interpretation maps give different computational readings (lambda, sessions, plans) without changing the engine

**What this subsumes:**
- TODO_0067 (proof certificates) — proof terms ARE certificates, but better: they compose, have computational meaning, and follow naturally from the logic instead of being bolted on

### 1.1 Two-Layer Architecture: Generic Terms + Interpretation

Proof terms follow a two-layer design inspired by LF/Twelf (Harper-Honsell-Plotkin 1993):

**Layer 1 — Generic terms (derived automatically from rule descriptors):**

The rule name IS the proof term constructor. No manual term definitions needed. The descriptor fields (`side`, `premises`, `binding`, `contextSplit`, `copyContext`) mechanically determine each constructor's arity and binding structure:

```
genericTerm(rule) = rule_name(principal?, binding₁.subproof₁, ...)
```

Examples:
```
tensor_l descriptor: { side:'l', premises:[{linear:[0,1]}] }
→ tensor_l(z, x₀.x₁.u₀)

loli_r descriptor: { side:'r', premises:[{linear:[0], succedent:1}] }
→ loli_r(x₀.u₀)

with_r descriptor: { side:'r', copyContext:true, premises:[{succedent:0},{succedent:1}] }
→ with_r(u₀, u₁)
```

This is exactly what LF does: one constructor per inference rule, adequacy guaranteed (bijection between proofs and well-typed terms). The existing `ProofTree` (with `rule` name + `premises`) is already 90% of a generic term — it just needs binding annotations, which the descriptor provides.

**Layer 2 — Interpretation maps (optional, swappable):**

A fold/catamorphism over generic terms that assigns computational meaning:

```
Layer 1 (generic):     tensor_l(z, x.y.u)
                            ↓  "lambda" interpretation
Layer 2a:              let (x, y) = z in [[u]]
                            ↓  "session-type" interpretation
Layer 2b:              z?(x).z?(y).[[u]]
                            ↓  "planning" interpretation
Layer 2c:              decompose(z, x, y); [[u]]
```

This is the "zoo of term assignments" (Martens 2014): same logic, different computational readings.

**Why NOT define terms in `.calc`/`.rules`:** The generic approach avoids needing new Store tags, new parser declarations, or new `.calc` entries for proof terms. Generic terms reuse existing infrastructure (ProofTree, rule names, descriptors). Layer 2 interpretations are post-processing, not part of the proof engine.

### 1.2 `.term` Files — Interpretation Maps

Layer 2 interpretations are defined in `.term` files. Each `.term` file maps generic constructors to notation in a target language via pattern-based rendering templates:

```
% ill-lambda.term
@name "lambda-calculus".

tensor_r(u₀, u₁)              => (u₀, u₁).
tensor_l(z, x₀.x₁.u₀)        => let (x₀, x₁) = z in u₀.
loli_r(x₀.u₀)                 => λx₀. u₀.
loli_l(z, u₀, x₁.u₁)         => z u₀; x₁. u₁.
with_r(u₀, u₁)                => ⟨u₀, u₁⟩.
with_l1(z, x₀.u₀)             => let x₀ = fst z in u₀.
with_l2(z, x₁.u₀)             => let x₁ = snd z in u₀.
oplus_r1(u₀)                  => inl u₀.
oplus_r2(u₀)                  => inr u₀.
oplus_l(z, x₀.u₀, x₁.u₁)    => case z of inl x₀ ⇒ u₀ | inr x₁ ⇒ u₁.
one_r                          => ().
one_l(z, u₀)                  => let () = z in u₀.
bang_r(u₀)                     => !u₀.
bang_l(z, y₀.u₀)              => let !y₀ = z in u₀.
monad_r(u₀)                   => {u₀}.
monad_l(z, x₀.u₀)            => let {x₀} = z in u₀.
```

A different `.term` file for the same logic:

```
% ill-session.term
@name "session-types".

tensor_r(u₀, u₁)              => send u₀; u₁.
tensor_l(z, x₀.x₁.u₀)        => (x₀, x₁) ← recv z; u₀.
loli_r(x₀.u₀)                 => x₀ ← accept; u₀.
with_r(u₀, u₁)                => offer { left: u₀, right: u₁ }.
oplus_r1(u₀)                  => select left; u₀.
oplus_l(z, x₀.u₀, x₁.u₁)    => branch z { left: x₀.u₀, right: x₁.u₁ }.
bang_r(u₀)                     => accept!; u₀.
monad_r(u₀)                   => spawn u₀.
```

**Loading pipeline:**

```
.calc → .rules → proof search → ProofTree
                                     ↓
                               extractTerm()  [automatic from descriptors]
                                     ↓
                               Generic proof term
                                     ↓
                  .term file → renderTerm()
                                     ↓
                               Rendered specific term
```

```javascript
// Calculus object includes interpretations:
calc.interpretations = {
  'lambda-calculus': loadTermFile('ill-lambda.term'),
  'session-types':   loadTermFile('ill-session.term'),
};

// Rendering:
const generic = extractTerm(proofTree, calc);
const rendered = renderTerm(generic, calc.interpretations['lambda-calculus']);
// → "λx. let (y, z) = x in (z, y)"
```

`.term` files are **optional**. Without one, generic terms render as-is: `tensor_l(z, x₀.x₁.u₀)`. Multiple `.term` files = different views of the same proof. Rules not mentioned in a `.term` file fall back to generic rendering.

**What `.term` is NOT (yet):** A rendering specification, not a full target language type system. Does not define reduction rules or type-checking for the target language. Could be extended later (e.g., `.theory` files with beta-reduction for the lambda interpretation).

### 1.3 Role Removal

The existing `deriveRoles()` function (`lib/calculus/builders.js`) maps `(category, arity, polarity) → semantic role name`. This indirection is used in `bridge.js` (rightFocus) and `compile.js` (flattenTensor, expandChoiceItem, etc.) to identify connective behavior.

Roles should be removed: they are redundant middleware. The same information is available directly from the connective's descriptor annotations. Replace `tag === roles.product` with a direct lookup of the connective's `(category, arity, polarity)` triple:

```javascript
// Before (roles):
if (tag === roles.product) { ... }

// After (direct descriptor properties):
const info = calc.connectiveInfo[tag];
if (info?.category === 'multiplicative' && info?.polarity === 'positive' && info?.arity === 2) { ... }

// Or with a precomputed lookup:
if (calc.isProduct(tag)) { ... }
```

The `connectiveInfo` table is already computable from `.calc` annotations — it's what `deriveRoles` reads from. Precompute boolean lookup tables (e.g., `isProduct[tagId]`, `isUnit[tagId]`) at calculus load time for O(1) hot-path checks. Same performance, no semantic naming layer.

---

## 2. The Term Language

Dual-context judgment (DILL, Barber-Plotkin 1996):

```
Γ; Δ ⊢ t : A
```

- `Γ` = cartesian context (weakening + contraction), variables usable many times
- `Δ` = linear context, each variable used exactly once

### 2.1 Multiplicatives

**Tensor (`A ⊗ B`):**
```
Γ; Δ₁ ⊢ t₁ : A    Γ; Δ₂ ⊢ t₂ : B
───────────────────────────────────── ⊗R
   Γ; Δ₁, Δ₂ ⊢ (t₁, t₂) : A ⊗ B

Γ; Δ₁ ⊢ t : A ⊗ B    Γ; Δ₂, x:A, y:B ⊢ u : C
────────────────────────────────────────────────── ⊗L
   Γ; Δ₁, Δ₂ ⊢ let (x, y) = t in u : C
```

**One (`1`):**
```
──────────────── 1R          Γ; Δ₁ ⊢ t : 1    Γ; Δ₂ ⊢ u : C
Γ; · ⊢ () : 1               ─────────────────────────────────── 1L
                              Γ; Δ₁, Δ₂ ⊢ let () = t in u : C
```

**Loli (`A ⊸ B`):**
```
Γ; Δ, x:A ⊢ t : B                     Γ; Δ₁ ⊢ t : A ⊸ B    Γ; Δ₂ ⊢ u : A
───────────────────── ⊸R               ─────────────────────────────────────── ⊸L
Γ; Δ ⊢ λx. t : A ⊸ B                   Γ; Δ₁, Δ₂ ⊢ t u : B
```

### 2.2 Additives

**With (`A & B`):**
```
Γ; Δ ⊢ t₁ : A    Γ; Δ ⊢ t₂ : B
────────────────────────────────── &R     (same Δ for both!)
  Γ; Δ ⊢ ⟨t₁, t₂⟩ : A & B

fst t : A    snd t : B                   (from t : A & B)
```

**Oplus (`A ⊕ B`):**
```
  Γ; Δ ⊢ t : A                            Γ; Δ ⊢ t : B
────────────────────── ⊕R₁              ────────────────────── ⊕R₂
Γ; Δ ⊢ inl t : A ⊕ B                   Γ; Δ ⊢ inr t : A ⊕ B

Γ; Δ₁ ⊢ t : A ⊕ B    Γ; Δ₂, x:A ⊢ u₁ : C    Γ; Δ₂, y:B ⊢ u₂ : C
───────────────────────────────────────────────────────────────────────── ⊕L
       Γ; Δ₁, Δ₂ ⊢ case t of inl x ⇒ u₁ | inr y ⇒ u₂ : C
```

**Zero (`0`):**
```
No introduction.

Γ; Δ ⊢ t : 0
──────────────── 0L
Γ; Δ ⊢ abort t : C
```

### 2.3 Exponential

**Bang (`!A`):**
```
Γ; · ⊢ t : A
─────────────── !R    (empty linear context)
Γ; · ⊢ !t : !A

Γ; Δ₁ ⊢ t : !A    Γ, x:A; Δ₂ ⊢ u : C
──────────────────────────────────────── !L    (x moves to cartesian)
   Γ; Δ₁, Δ₂ ⊢ let !x = t in u : C
```

### 2.4 Lax Monad

**Monad (`{A}`):**
```
Γ; Δ ⊢_lax t : A
────────────────────── {A}R
Γ; Δ ⊢ {t} : {A}

Γ; Δ₁ ⊢ t : {A}    Γ; Δ₂, x:A ⊢_lax u : C
─────────────────────────────────────────────── {A}L
     Γ; Δ₁, Δ₂ ⊢_lax let {x} = t in u : C
```

The `⊢_lax` judgment is **sticky**: once entered, you cannot return to `⊢`. This is the type-theoretic expression of the mode switch — backward proving enters `⊢_lax` via `monad_r`, and the forward engine operates entirely within `⊢_lax`.

Via Moggi's computational monad: `{t}` = `return t`, `let {x} = t in u` = `bind t (λx. u)`.

Via Pfenning-Davies (2001): `⊢` = "A is true", `⊢_lax` = "A is achievable (through computation)".

### 2.5 Quantifiers

**Universal (`∀x.A`):**
```
Γ; Δ ⊢ t : A[y/x]                          (y fresh — eigenvariable)
──────────────────── ∀R
Γ; Δ ⊢ Λy.t : ∀x.A

Γ; Δ, u:A[s/x] ⊢ t : C
──────────────────────── ∀L                  (instantiate with term s)
Γ; Δ, u:∀x.A ⊢ t : C
```

Note on ∀L: The principal formula `∀x.A` is on the LEFT (antecedent) and is deconstructed to `A[s/x]`. The proof term `t` in the conclusion is the same as in the premise — the rule just substitutes `u` for the instantiated hypothesis. In the generic term view: `forall_l(u, s, t)` where `u` is the principal, `s` is the witness term, `t` is the continuation proof. Spined notation (RES_0086): `u[s] · t`.

**Existential (`∃x.A`):**
```
Γ; Δ ⊢ t : A[s/x]
──────────────────────── ∃R                  (witness s + proof t)
Γ; Δ ⊢ pack(s, t) : ∃x.A

Γ; Δ, y:A[a/x] ⊢ t : C                     (a fresh — eigenvariable)
──────────────────────── ∃L
Γ; Δ, u:∃x.A ⊢ t : C
```

Note on ∃L: The principal formula `∃x.A` is on the LEFT and is deconstructed by opening the existential with fresh eigenvariable `a`. In the generic term view: `exists_l(u, a.t)`.

**Reading direction:** Sequent calculus rules are read bottom→top for proof search. The conclusion (bottom) ALWAYS has the complex connective. The premise (top) has simpler sub-formulas. Reading bottom→top, you DECONSTRUCT. Reading top→bottom (proof construction), you INTRODUCE. Both perspectives describe the same rule.

In CLF: ∃ is synchronous (inside the monad `{S}`), while ∀ (as `Π`) is asynchronous. Implementation deferred until quantifiers appear in forward programs. See TODO_0011 for the dependent case (`Πx:A.B`).

### 2.6 Identity and Cut

```
──────────── id               Γ; Δ₁ ⊢ t : A    Γ; Δ₂, x:A ⊢ u : C
Γ; x:A ⊢ x : A               ──────────────────────────────────────── cut
                                Γ; Δ₁, Δ₂ ⊢ u[t/x] : C
```

### 2.7 Term Grammar Summary

```
t ::= x                                    variable
    | (t₁, t₂)                             tensor intro
    | let (x, y) = t in u                   tensor elim
    | ()                                    one intro
    | let () = t in u                       one elim
    | λx. t                                 loli intro
    | t u                                   loli elim
    | ⟨t₁, t₂⟩                             with intro
    | fst t | snd t                         with elim
    | inl t | inr t                         oplus intro
    | case t of inl x ⇒ u₁ | inr y ⇒ u₂   oplus elim
    | abort t                               zero elim
    | !t                                    bang intro
    | let !x = t in u                       bang elim
    | {e}                                   monad intro
    | let {x} = t in e                      monad elim (inside ⊢_lax)
    | Λx. t                                 forall-right (eigenvariable abstraction)
    | u[s]                                   forall-left (instantiation of hypothesis)
    | pack(s, t)                             exists-right (witness + proof)
    | unpack u as (x, y) in t               exists-left (open existential)
```

---

## 3. Proof Terms in CALC's Two Modes

### 3.1 Backward Prover → Natural Deduction Terms

The backward prover (L2-L3) already builds proof trees. Each rule application maps to a generic proof term constructor (Layer 1). The right column shows the lambda interpretation (Layer 2, from `.term` file):

| Rule name | Generic term | Lambda view |
|---|---|---|
| `id` | `id(x)` | `x` |
| `tensor_r` | `tensor_r(u₀, u₁)` | `(u₀, u₁)` |
| `tensor_l` | `tensor_l(z, x₀.x₁.u₀)` | `let (x₀, x₁) = z in u₀` |
| `loli_r` | `loli_r(x₀.u₀)` | `λx₀. u₀` |
| `loli_l` | `loli_l(z, u₀, x₁.u₁)` | `z u₀` (+ continuation) |
| `with_r` | `with_r(u₀, u₁)` | `⟨u₀, u₁⟩` |
| `with_l1` / `with_l2` | `with_l1(z, x₀.u₀)` | `fst z` / `snd z` |
| `oplus_r1` / `oplus_r2` | `oplus_r1(u₀)` | `inl u₀` / `inr u₀` |
| `oplus_l` | `oplus_l(z, x₀.u₀, x₁.u₁)` | `case z of ...` |
| `zero_l` | `zero_l(z)` | `abort z` |
| `one_r` | `one_r()` | `()` |
| `one_l` | `one_l(z, u₀)` | `let () = z in u₀` |
| `bang_r` | `bang_r(u₀)` | `!u₀` |
| `bang_l` | `bang_l(z, y₀.u₀)` | `let !y₀ = z in u₀` |
| `copy` | `copy(z, y₀.u₀)` | = `bang_l` (moves `!A` to Γ) |
| `monad_r` | `monad_r(evidence)` | `{e}` (delegates to forward engine) |
| `monad_l` | `monad_l(z, x₀.u₀)` | `let {x₀} = z in u₀` |

### 3.2 Forward Engine → Monadic Let-Bindings (CLF)

Each forward step IS a monadic let-binding. A forward rule `r : A₁ ⊗ A₂ ⊗ !P ⊸ {B₁ ⊗ B₂}` applied with θ produces:

```
let {(b₁, b₂)} = r (a₁, a₂, !p) in ...continuation...
```

This is exactly CLF's monadic expression (Watkins et al. 2004):
```
E ::= let {p} = R in E    -- forward step
    | M                    -- return (quiescence)
```

A full forward trace is a nested sequence of let-bindings:
```
let {(b₁, b₂)} = r₁ (a₁, a₂) in
let {c}         = r₂ (b₁, b₃) in
(c, b₂)                              -- final state = return value
```

**Loli continuations:** When state contains `f : A ⊸ {B}` and `a : A`, `matchFirstLoli` fires. This is loli elimination (function application): `f a : {B}`. In the monadic setting: `let {p} = (f a) in ...`. Same shape as any rule application — the loli IS the rule being applied.

### 3.3 rightFocus → Synchronous Decomposition Term

After quiescence, `rightFocus` decomposes the succedent against residual state. This produces a term built from tensor/one/bang/id constructors:

```
rightFocus(state, A ⊗ B) = (rightFocus(Δ₁, A), rightFocus(Δ₂, B))
rightFocus(·, 1)          = ()
rightFocus(state, !A)     = !(id_persistent(A))
rightFocus(state, atom)   = id_linear(atom)
```

### 3.4 Explore Tree and Proof Terms

Non-fork nodes map straightforwardly to proof term structure:

| Node type | Term fragment |
|---|---|
| `leaf` | Return value: rightFocus decomposition term |
| `branch` child | `let {p} = r args in ...child_term...` |
| `bound` | `⊥` (incomplete — no term) |
| `cycle` | Back-edge reference (coinductive — future work, TODO_0009) |
| `memo` | Pointer to previously computed term |

### 3.5 OPEN QUESTION: Oplus Forks and Proof Terms

**This is an unresolved research question that needs dedicated investigation before implementation.**

When a rule produces `A ⊕ B`, the explore tree forks via `expandConsequentChoices`. How should this fork relate to proof terms?

**Option A — One proof term with case splits:**

The explore tree maps to a SINGLE proof term. Each fork becomes an oplus_l (case) constructor:

```
let {x} = evm_eq(args) in           -- x : S₁ ⊕ S₂
  case x of
    inl a ⇒ ...continuation₁...     -- eq branch
    inr b ⇒ ...continuation₂...     -- neq branch
```

Nested forks = nested cases. The explore tree IS the term structure. One proof term captures all possible executions.

**Option B — N proof terms, one per path:**

Each root-to-leaf path through the explore tree is a SEPARATE proof term. Forks are meta-level (the explorer branching), not object-level (no case in the term). k nested binary forks → up to 2^k proof terms.

```
Path 1: let {s} = evm_eq(args) in ...T₁...    (inl world)
Path 2: let {s} = evm_eq(args) in ...T₂...    (inr world)
```

**Key considerations:**

1. **CLF excludes oplus from the monad** (`{S}` uses `∃, ⊗, 1, !` — no `⊕`). This is deliberate: CLF uses committed-choice semantics. Case analysis (requiring both branches) contradicts committed choice.

2. **CALC's explore IS exhaustive.** It explores both branches, unlike CLF's committed choice. So Option A (case splits) is proof-theoretically valid for CALC — the explore tree corresponds to a derivation that includes both cases.

3. **Typing of the result.** With Option A, the proof term has type `{C}` where C is the overall goal. The case split is well-typed: `x : A ⊕ B`, each branch proves C. With Option B, each path's term independently has type `{C}`.

4. **Dead branches.** Option A: dead branches need a term — either `abort` (if we treat UNSAT as 0-introduction) or some special `⊥` marker. Option B: dead paths just have no term. See §3.6.

5. **Practical use.** For symbolic execution (CALC's main use), are users more interested in "one big term showing all branches" (Option A) or "a list of individual execution traces" (Option B)? For verification, Option A is natural (prove a property holds in all branches). For debugging, Option B is natural (inspect one path).

6. **Relationship to .term interpretations.** Option A places `case` inside the monadic term. Different .term files would render it differently (lambda: `case`, session: `branch`, etc.). Option B has no case construct at all — the fork only exists in the explore tree metadata.

**This needs standalone research:** How do other exhaustive exploration systems (model checkers, symbolic executors, game trees) handle proof term extraction at branch points? Is there a standard approach? Does the choice affect what properties we can prove about explore trees (TODO_0045)?

### 3.6 Dead Branches

Dead ≠ zero (additive unit). Dead means the constraint solver proved UNSAT (no derivation exists), not that `0` was introduced. A `0L` rule produces `abort t`, but dead branches have no derivation at all — no proof was possible. Open question: could dead branches carry refutation witnesses? What is the proof-theoretic status of constraint solver UNSAT? Tied to the oplus question (§3.5) — with Option A, dead branches need terms; with Option B, they don't.

---

## 4. Type Checker (Trusted Kernel Extension)

A small, independent module that verifies `t : A`. This is the de Bruijn criterion applied via Curry-Howard: the prover (untrusted, complex) produces terms, the checker (trusted, small) validates them.

### 4.1 Interface

```javascript
// lib/prover/check-term.js (~150 LOC, trusted)
function checkTerm(gamma, delta, term, type) → { valid: boolean, error?: string }
```

Input: contexts, term, expected type — all as expanded term objects (not Store hashes). Store stays outside the trust boundary (same principle as TODO_0067 §4).

### 4.2 What It Checks

For each term constructor, one clause:

| Term | Check |
|---|---|
| `x` | `x ∈ Δ` with type A, or `x ∈ Γ` |
| `(t₁, t₂) : A ⊗ B` | Split Δ into Δ₁, Δ₂; check `t₁ : A` with Δ₁, `t₂ : B` with Δ₂ |
| `let (x,y) = t in u` | Check `t : A ⊗ B`, check `u : C` with Δ extended by x:A, y:B |
| `λx. t : A ⊸ B` | Check `t : B` with Δ extended by x:A |
| `t u : B` | Check `t : A ⊸ B`, check `u : A` |
| `{e} : {A}` | Check `e : A` in lax mode |
| `let {x} = t in e` | Check `t : {A}`, check `e : C` with Δ extended by x:A (lax mode) |
| ... | (one clause per constructor) |

The checker is ~150 LOC: structural recursion on the term, one case per constructor. No search, no backtracking, no unification. Deterministic, total, O(|term|).

**Context splitting is deterministic.** For tensor `(t₁, t₂) : A ⊗ B`, the checker must split Δ into Δ₁ and Δ₂. In general this is exponential (searching for the right split). But the term *determines* the split: track which variables each sub-term uses. Each variable used exactly once (linearity). No search needed — the checker just walks the term and partitions variables as it goes.

### 4.3 Trust Boundary

| Trusted | Size | Role |
|---|---|---|
| `kernel.js` (existing) | 205 LOC | Backward proof step verification |
| `check-term.js` (new) | ~150 LOC | Forward proof term type-checking |
| Term equality + substitution | ~25 LOC | Shared utilities |
| **Total** | **~380 LOC** | |

Everything else (Store, forward engine, backward prover, FFI, strategy) is untrusted.

---

## 5. Implementation

### Phase 1: Generic Term Extraction (~50 LOC)

No new `.calc` declarations needed. Generic proof terms are derived directly from rule descriptors.

New module `lib/prover/generic-term.js`:

```javascript
function genericTermShape(rule) {
  const d = rule.descriptor;
  const args = [];
  if (d.side === 'l') args.push('z');  // principal consumed from antecedent
  d.premises.forEach((p, i) => {
    const bindings = [
      ...(p.linear || []).map(idx => `x${idx}`),
      ...(p.cartesian || []).map(idx => `y${idx}`)
    ];
    const sub = `u${i}`;
    args.push(bindings.length ? `${bindings.join('.')}.${sub}` : sub);
  });
  return { constructor: rule.name, args };
}
```

Generic terms are lightweight JS objects: `{ type: 'tensor_l', principal: hash, premises: [{ bindings: [...], body: subterm }] }`. No Store tags consumed, no FactSet impact, no binary cache invalidation.

Variables use de Bruijn indices (via existing `bound(n)` nodes) for binding positions. The descriptor's `premises[i].linear` array maps directly to binding indices.

**What about Store/content-addressing?** Generic terms live OUTSIDE the Store. They annotate proofs, not participate in forward execution. If Layer 2 interpretations ever need Store representation (e.g., for dependent types where terms appear inside formulas), Store tags can be added then. But Layer 1 doesn't need them.

### Phase 2: Backward Term Builder (~80 LOC)

Extend `lib/prover/generic-term.js` (untrusted). Given a completed ProofTree, extract the corresponding generic proof term:

```javascript
function extractTerm(proofTree, calculus) → genericTerm
```

Post-hoc extraction: the prover builds the proof tree as now, then `extractTerm` walks it and constructs a generic term using `genericTermShape` for binding structure. No changes to the prover itself. Returns a lightweight JS object tree, not Store hashes.

### Phase 3: Forward Term Builder (~60 LOC)

Extend `forward.run()` and `explore()` to optionally record monadic terms. Opt-in via `{ terms: true }`:

```javascript
// forward.js — when terms enabled
trace.push({ rule, theta, consumed, produced, termHash });

// At quiescence: rightFocus produces decomposition term
const rfTerm = buildRightFocusTerm(residualState, succedent);
```

Function pointer swap at entry (same pattern as TODO_0067): no branches in the hot path when terms are disabled.

### Phase 4: Type Checker (~150 LOC)

New module `lib/prover/check-term.js` (trusted). Works on generic term objects, no Store dependency:

```javascript
function checkTerm(gamma, delta, term, type, calculus) {
  const rule = calculus.rules[term.type];
  const d = rule.descriptor;
  // Generic checking: use descriptor to verify context handling,
  // binding structure, and premise types
  // One case per (side, contextSplit, copyContext) combination
}
```

The checker is descriptor-driven, not per-constructor. A new connective with standard descriptor fields is automatically checkable. Only ~5 structural cases needed (right-split, right-copy, right-empty, left-split, left-single) rather than one case per connective.

### Phase 5: Bridge Integration (~30 LOC)

Wire `monad_r` to produce and verify terms:

```javascript
// bridge.js — executeModeSwitch
if (opts.terms) {
  const monadicTerm = buildMonadicTerm(trace, rfTerm);
  // Type-check: monadicTerm : innerSuccedent
  const check = checkTerm(gamma, delta, expand(monadicTerm), expand(innerSucc));
  evidence = { term: monadicTerm, verified: check.valid };
}
```

Kernel verification for monad_r changes from `{ valid: true, unverified: 'modeSwitch' }` to `{ valid: true }` when term verification succeeds.

### Phase 6: Tests (~80 LOC)

- Term construction: each connective → correct term shape
- Type checking: valid terms accepted, invalid rejected
- Round-trip: backward proof → extract term → type-check → valid
- Forward trace → monadic term → type-check → valid
- Tampered terms rejected (wrong variable, missing resource, type mismatch)
- Zero-overhead: `{ terms: false }` matches baseline performance

---

## 6. Relationship to Other TODOs

| TODO | Relationship |
|---|---|
| **TODO_0067** (proof certificates) | **Subsumed.** Proof terms are strictly more useful than ad-hoc certificates. Terms compose, have computational meaning, and follow standard theory. 0067 demoted to priority 3. |
| **TODO_0045** (execution tree judgment) | **Consumer.** The tree `T` in `Σ; Δ ⊢_fwd T : A` is now a tree of monadic proof terms. |
| **TODO_0008** (metaproofs) | **Consumer.** Invariant witnesses become typed proof terms. Counterexample traces are well-typed monadic expressions. |
| **TODO_0011** (CLF dependent types) | **Orthogonal.** Dependent types add `Πx:A.B` — proof terms depend on values. This TODO handles the non-dependent base case. |
| **TODO_0009** (induction/coinduction) | **Future extension.** Fixed-point terms (μ/ν constructors) and cyclic proof terms extend this term language. |
| **TODO_0066** (modular architecture) | **Aligns.** The architecture's hook points (certificateHook in explore, evidence in monad_r) are where terms get recorded. |
| **TODO_0064** (higher-order extensions) | **Axis 1, Level 0→1.** This is the first step on the term-level type discipline axis. |

---

## 7. Key Design Decisions

**Post-hoc extraction, not inline construction.** The backward prover builds proof trees as it does now. Terms are extracted from completed trees. This avoids threading term-building through the search loop. The forward engine records traces (it already does); terms are built from traces. Clean separation: search is search, terms are terms.

**Opt-in, zero overhead when off.** Same function-pointer-swap pattern as the existing `provePersistentWithFFI` / `provePersistentNaive` dispatch. No `if (terms)` in hot loops.

**Store-free checker.** The type checker works on expanded ASTs, not hashes. Store is untrusted infrastructure. The checker is a pure function: `(contexts, term, type) → valid/invalid`.

**No definitional equality (yet).** CLF identifies monadic expressions up to reordering of independent let-bindings. CALC doesn't need this — the forward engine commits to a specific execution order. If needed later (e.g., for confluence proofs), commuting conversions can be added to the checker.

**FFI as axiom (configurable).** Two modes for persistent goals when terms are enabled:
1. **FFI axiom mode** (default, fast): FFI results produce axiom terms `ffi("plus", [3, 2, 5])`. The type checker validates by re-computing. Preserves FFI performance.
2. **Clause resolution mode** (strict): FFI disabled, clause resolution produces full proof subtrees. Slower (~10-20× for arithmetic-heavy programs) but terms are self-contained.

Configurable alongside other profile settings (e.g., `{ terms: true, ffiAxioms: true }`). Same function-pointer-swap dispatch as existing FFI opt-in.

---

## 8. Theory Compliance

### 8.1 Soundness

If `checkTerm(Γ, Δ, t, A)` returns valid, then `Γ; Δ ⊢ t : A` is a valid ILL+lax derivation. Proof: each case of the checker corresponds to exactly one ILL inference rule. The checker is a direct implementation of the typing rules in §2.

### 8.2 Adequacy

The term assignment is **adequate** in the LF sense (Harper-Honsell-Plotkin 1993): there is a compositional bijection between ILL proofs and well-typed terms of the corresponding type.

- **Faithfulness (injectivity):** Different proofs produce different terms (each rule application produces a distinct constructor).
- **Fullness (surjectivity):** Every well-typed term corresponds to a proof (the checker validates exactly the derivable judgments).
- **Compositionality:** Term construction commutes with substitution: `extractTerm(D[s/x]) = extractTerm(D)[extractTerm(s)/x]`.

### 8.3 Canonical Forms

Generic proof terms (Layer 1) are lightweight JS objects. If needed, they can be content-addressed via Store (Layer 2 may require this for dependent types). The current system doesn't need beta-reduction because terms are constructed in normal form (post-hoc extraction from cut-free proofs).

---

## 9. Future Optimizations

Captured here for later exploration, not part of initial implementation.

1. **Streaming term construction:** Build terms during DFS exploration, undo with the Arena alongside state undo. Avoids post-hoc tree walk. Only worth it if extraction becomes a bottleneck.

2. **Term sharing:** If two explore paths produce identical sub-proof terms, share them. Content-addressing (Store) gives this for free. Reduces memory for trees with many isomorphic subtrees.

3. **Incremental checking:** Type-check terms as they're built (each monadic let-binding). Catches errors early, before full tree extraction completes.

4. **FFI axiom compilation:** Pre-generate checker code per FFI operation, so `ffi("plus", [a,b,c])` validates in O(1) (just recompute and compare) rather than going through generic checker dispatch.

5. **Zig-friendly flat arena:** Proof terms as `struct ProofTerm { tag: u8, arity: u8, children: [4]u32 }` in a bump arena. ~10 bytes per node. Cache-friendly, zero allocation, trivially serializable. The JS implementation can use `Uint8Array` + `Uint32Array` SoA to match.

6. **Lazy extraction:** For very large explore trees (10K+ nodes), extract terms only for paths the user inspects, not the full tree.

7. **Store tag capacity:** Currently `tags = new Uint8Array(capacity)` limits tag values to 0-255. If Layer 2 interpretations ever need Store-resident terms (e.g., dependent types), upgrading to `Uint16Array` (65536 tags) is a one-line change. `STRING_CHILD_TAGS`/`BIGINT_CHILD_TAGS` lookup tables would grow from 256B to 64KB (still trivial). PRED_BOUNDARY (currently 28) is unrelated — it separates built-in tags from dynamic predicates. The generic Layer 1 approach avoids this concern entirely by keeping terms outside the Store.

---

## 10. References

### Foundational
- Barber & Plotkin (1996) — "Dual Intuitionistic Linear Logic" (DILL). Dual-context judgment `Γ; Δ ⊢ M : A`
- Benton (1995) — "A Mixed Linear and Non-Linear Logic" (LNL). Adjoint decomposition `!A = G(F(A))`
- Bierman, Benton, de Paiva, Hyland (1992) — "Term Assignments for ILL". First complete term assignment
- Girard (1987) — "Linear Logic" TCS 50(1). The logic itself

### CLF and Logical Frameworks
- Watkins, Cervesato, Pfenning, Walker (2004) — "CLF: A Concurrent Logical Framework". Monadic proof terms `let {p} = R in E`
- Cervesato & Pfenning (2002) — "A Linear Logical Framework" (LLF). `λΠ⊸&⊤`
- Harper, Honsell & Plotkin (1993) — "A Framework for Defining Logics" (LF). Canonical forms, adequacy

### Lax Monad
- Pfenning & Davies (2001) — "A Judgmental Reconstruction of Modal Logic". Lax modality as `⊢_lax`, terms = Moggi's monad
- Moggi (1991) — "Notions of Computation and Monads". Computational monad = `{A}`
- Fairtlough & Mendler (1997) — "Propositional Lax Logic"

### Session Types & Term Zoos
- Caires & Pfenning (2010) — "Session Types as Intuitionistic Linear Propositions". Proofs = processes
- Wadler (2014) — "Propositions as Sessions". Classical variant
- Martens (2014) — "Zoo of Term Assignments for Linear Sequent Calculus". Same logic, different computational meanings (lambda terms, processes, plans)

### Internal
- [TODO_0045](0045_execution-tree-judgment.md) — Execution tree judgment (consumer of proof terms)
- [TODO_0067](0067_proof-certificates.md) — Proof certificates (subsumed, priority 3)
- [TODO_0011](0011_clf-dependent-types.md) — CLF dependent types (orthogonal extension)
- [TODO_0064](0064_higher-order-extensions-overview.md) — Higher-order extensions (Axis 1)
- [RES_0052](../research/0052_clf-lax-monad-deep-study.md) — CLF lax monad deep study
- [RES_0038](../research/0038_resource-term-semantics.md) — Resource term semantics
- [RES_0077](../research/0077_modular-proof-kernel-architectures.md) — Proof kernel architectures
- [RES_0086](../research/0086_quantifier-proof-terms.md) — Quantifier proof terms survey
- `doc/documentation/lax-monad.md` — Mode switch & connective roles
