---
title: "Stickiness Enforcement in Lax/Monadic Logics: A Cross-System Survey"
created: 2026-03-04
modified: 2026-03-04
summary: "How five systems (Pfenning-Davies, CLF, Celf, LolliMon, adjoint logic) enforce the property that monadic elimination stays in the monadic fragment, and where this should live in CALC."
tags: [lax-monad, clf, Celf, adjoint-logic, focusing, polarity, proof-search, stickiness, proof-theory, linear-logic]
category: "Proof Theory"
---

# Stickiness Enforcement in Lax/Monadic Logics

## The Question

In lax logic / CLF / adjoint logic, the monad `{A}` has a **stickiness** property: once you open (eliminate) a monadic value, you cannot use the result to prove a non-monadic goal. The result stays "inside" the monad. How is this enforced?

Four candidate mechanisms:
- **(a) Side-condition:** monad_l has a precondition checking that the succedent is monadic
- **(b) Judgment bifurcation:** two judgments (`A true` vs `A lax`), monad_l only exists in `lax`
- **(c) Type discipline:** monad_l's conclusion is always typed `C lax`, blocking `C true` conclusions
- **(d) Syntactic stratification:** terms vs expressions are distinct syntactic categories

**Answer: all four, at different levels.** The systems agree on the deep structure but implement it via different mechanisms depending on their formalism.

---

## 1. Pfenning-Davies 2001 (Natural Deduction)

**Mechanism: (b) judgment bifurcation + (c) type discipline.**

Two judgments:
```
A true    — A is provable
A lax     — A is achievable (possibly via computation)
```

Three rules govern the circle (lax) modality:

```
  Gamma |- A lax
  ────────────────── circR (introduction)
  Gamma |- ○A true

  hyp(○A) :: (hyp(A) -> lax C)
  ──────────────────────────────── circL (elimination)
  hyp(○A) -> lax C

  true A -> lax A                    laxR (subsumption)
```

**Where stickiness lives:**
- `circL` produces `lax C`, never `true C`. This is hardcoded in the type of the rule.
- `laxR` goes from `true` to `lax` (subsumption), but there is **no rule** `lax A -> true A`.
- Once you enter `lax` (via `circL`), all subsequent conclusions must be `lax`.

In the Twelf encoding, this is enforced by LF's type system: `circL` has return type `lax A`, and no Twelf signature provides `lax A -> true A`.

**Verdict:** Stickiness is (b)+(c). The bifurcated judgment structure prevents escape, and the types of the rules enforce it.

---

## 2. CLF (Watkins et al. 2002/2004)

**Mechanism: (d) syntactic stratification.**

CLF splits its syntax into four layers:

```
Types:        A ::= P | A -o B | A & B | T | {S}
Sync types:   S ::= P | S₁ * S₂ | 1 | !A | exists x.S
Objects:      N ::= ... | {E}          (normal objects)
Expressions:  E ::= let {p} = R in E | M   (monadic expressions)
Monadic obj:  M ::= <N₁, N₂> | <> | !N | <N, x.M>
```

**Where stickiness lives:**
- Objects N and expressions E are **distinct syntactic categories**.
- `{E}` is the only way to embed an expression E into an object N.
- `let {p} = R in E` can only appear inside an expression E, which can only appear inside `{E}`.
- There is no way to write a `let` outside of `{...}` — the grammar forbids it.

The typing judgment for expressions `Gamma; Delta |- E :: S` is separate from the judgment for objects `Gamma; Delta |- N <= A`. An expression can only be checked against a synchronous type S inside a monadic wrapper.

**The key rule** (informally):
```
  Gamma; Delta |- N => {S}     Gamma; Delta', p:S |- E :: T
  ───────────────────────────────────────────────────────────── let
  Gamma; Delta, Delta' |- (let {p} = N in E) :: T
```

The conclusion is `E :: T` (an expression at synchronous type), not `N <= A` (an object at async type). You can only get back to an object via `{E}`, which wraps the entire expression.

**Verdict:** Stickiness is (d). The syntactic stratification makes it literally impossible to write a monadic elimination outside of a monadic expression. No side-condition needed — the grammar handles it.

---

## 3. Celf (Schack-Nielsen & Schurmann 2008)

**Mechanism: (a) side-condition via dual proof search functions.**

Celf implements CLF's type theory in SML. The proof search engine has **two separate left-focus functions**:

```sml
(* For atomic (non-monadic) goals *)
fun leftFocus (ctx, hyp, succedent, sc) =
  case hyp of
    TLPi (p, S, A) => (* recurse *)
  | AddProd (A, B)  => (* branch *)
  | TMonad S        => raise Fail "monads forbidden here"  (* !! *)
  | TAtomic _       => (* unify with succedent *)

(* For monadic goals *)
fun monLeftFocus (ctx, hyp, succedent, sc) =
  case hyp of
    TLPi (p, S, A) => (* recurse into monLeftFocus *)
  | AddProd (A, B)  => (* branch *)
  | TMonad sty      => sc (Nil', sty, ctx)   (* succeed: extract S *)
  | TAtomic _       => raise Fail "wrong hypothesis"
```

And `solve'` dispatches between them:

```sml
fun solve' (ctx, ty, sc) =
  case ty of
    TLPi ...     => (* recurse *)
  | AddProd ...  => (* recurse *)
  | TMonad S     => forwardChain (ctx, S, sc)   (* monadic goal *)
  | TAtomic _    => matchAtom (ctx, ty, sc)      (* atomic goal *)
```

**Where stickiness lives:**
- `leftFocus` **raises an error** on `TMonad` — you cannot focus on a monadic hypothesis when pursuing a non-monadic goal.
- `monLeftFocus` **succeeds** on `TMonad` — you can only eliminate a monadic hypothesis when pursuing a monadic goal.
- `solve'` dispatches to `forwardChain` (which uses `monLeftFocus`) only when the succedent is `TMonad S`.

This is mechanism (a): a runtime check (actually a static dispatch) ensures monad_l applies only when the succedent is monadic. The check is the **pattern match** in `leftFocus` vs `monLeftFocus`.

**Verdict:** Stickiness is (a), implemented as dual functions rather than an explicit side-condition predicate. The goal type determines which function runs, and `leftFocus` structurally refuses monadic hypotheses.

---

## 4. LolliMon (Lopez et al. 2005)

**Mechanism: (a) side-condition via syntactic pattern match on goal.**

LolliMon's proof search engine (in OCaml) pattern-matches on the goal:

```ocaml
fun solve ... gl kf ks =
  case gl of
  | Const "{}" 0 [goal] =>
      (* *** begin code for monadic goal *** *)
      forward (ctx, goal, ...)
  | ... (* other connectives: backward chaining *)
```

**Where stickiness lives:**
- The `Const "{}" 0 [goal]` case triggers forward chaining.
- Forward chaining uses `breakdown` and `allMon ctx` to process monadic clauses.
- Outside this case, `{}` constructs are never processed — the backward engine ignores them.
- There is no way for forward-chaining results to "leak" back into backward goals because the `solve` function's return continuation only fires within the `{}` case.

**Verdict:** Stickiness is (a). The top-level pattern match on the goal type is the enforcement point. Forward chaining is syntactically confined to the `Const "{}" ...` branch.

---

## 5. Adjoint Logic (Pruiksma et al. 2018, 2024)

**Mechanism: (b) mode-indexed judgments + structural presuppositions.**

Adjoint logic generalizes the picture. Instead of two judgments, there is one judgment parameterized by a **mode** m:

```
Gamma |-_m C_m
```

with a presupposition: every antecedent A_k in Gamma must satisfy `k >= m` (mode compatibility).

Shift rules:

```
  Gamma |- A_k                            k >= r    Gamma, A_k |- C_r
  ─────────────────── upR                 ──────────────────────────── upL
  Gamma |- (up_k^m A)_m                   Gamma, (up_k^m A)_m |- C_r

  Gamma' >= n    Gamma' |- A_n            Gamma, A_n |- C_r
  ──────────────────────────── downR      ────────────────────── downL
  Gamma_W, Gamma' |- (down_m^n A)_m      Gamma, (down_m^n A)_m |- C_r
```

The lax monad is `○A = up(down(A))`, composing two shifts. Bang is `!A = down(up(A))`.

**Where stickiness lives:**
- The **presupposition** on sequents: in `Gamma |-_m C_m`, all antecedents must have mode `>= m`.
- When `upL` fires on `up_k^m A`, it exposes `A_k` at mode k. If `k < m` (which is required by `up`'s presupposition `m >= k`), then `A_k` can only be used in goals at mode `<= k`.
- The mode ordering `m >= k` is baked into the shift's type. You cannot use a low-mode hypothesis for a high-mode goal.

For the lax monad specifically: `○A = up_L^B(down_B^L(A))` where L = linear mode, B = backward mode.
- `upL` on `○A` in the context exposes `down_B^L(A)` at mode B.
- At mode B, the goal must be mode `<= B`. But the overall proof is at mode L.
- You must wrap back via `upR` to return to mode L — producing `up_L^B(...)`, i.e., another `○` type.

**Verdict:** Stickiness is (b). The mode-indexed judgment structure enforces it. No side-condition is needed — the presupposition `k >= m` on antecedents structurally prevents using monadic content for non-monadic goals. This is the most general mechanism: it parameterizes over the mode lattice rather than hardcoding "true vs lax."

---

## 6. Summary Table

| System | Level | Mechanism | Where enforced |
|---|---|---|---|
| Pfenning-Davies | Judgment | Bifurcated judgments `true`/`lax` | Type of `circL` rule |
| CLF | Syntax | Stratified grammar (objects vs expressions) | Grammar productions |
| Celf | Implementation | Dual focus functions (`leftFocus` vs `monLeftFocus`) | Pattern match on goal type |
| LolliMon | Implementation | Top-level pattern match on `Const "{}" ...` | `solve` function dispatch |
| Adjoint logic | Judgment | Mode-indexed judgments with presupposition | Mode ordering `k >= m` |

All systems agree: **stickiness is structural, not a side-condition.** The mechanisms differ in where the structure lives:
- **Theory level:** judgments or types (Pfenning-Davies, adjoint logic)
- **Grammar level:** syntactic categories (CLF)
- **Implementation level:** separate code paths (Celf, LolliMon)

---

## 7. Implications for CALC

CALC's backward prover is a **focused proof search engine** with three phases: inversion (Phase 1), focus choice (Phase 2), decomposition (Phase 3). The key question: where should stickiness live?

### 7.1 Option 1: Side-condition in `chooseFocus` (Celf-style)

Add a check in `chooseFocus` or `applyAndRecurse`: when the succedent is `monad(S)`, allow focusing on `monad(X)` hypotheses. When the succedent is NOT monadic, skip `monad(X)` hypotheses.

```javascript
// In chooseFocus:
if (tag === 'monad' && !isMonadicGoal(seq.succedent)) continue;
```

**Pro:** Minimal code change (~5 LOC). Directly mirrors Celf.
**Con:** Scattered side-condition. Easy to forget in new code paths. Not captured in the rule descriptor.

### 7.2 Option 2: Descriptor-level enforcement (rule-interpreter)

Add a `requiresMonadicSuccedent: true` flag to monad_l's descriptor. The rule-interpreter checks this before generating premises.

```javascript
monad_l: {
  connective: 'monad',
  side: 'l',
  arity: 1,
  requiresMonadicSuccedent: true,  // <-- stickiness
  premises: [{ linear: [0] }]
}
```

Then in `applyRule` or `buildMakePremises`:
```javascript
if (spec.requiresMonadicSuccedent && Store.tag(seq.succedent) !== Store.TAG.monad) {
  return { success: false };
}
```

**Pro:** Stickiness is declared in the descriptor, visible to all consumers. Self-documenting. Can be precomputed in `ill.json`.
**Con:** Adds a new descriptor field. Not purely compositional (mixes connective semantics with goal context).

### 7.3 Option 3: Mode-indexed judgments (adjoint-style)

Extend sequents with a mode tag: `{ contexts, succedent, mode: 'true' | 'lax' }`. When `circL` fires, the mode switches to `lax`. In mode `lax`, only monadic conclusions are allowed.

**Pro:** Most principled. Directly mirrors the theory. Generalizes to N modes.
**Con:** Significant refactor. Every function touching sequents must handle modes. Over-engineered for the 2-mode case.

### 7.4 Recommendation

**Option 2 (descriptor flag) is the right choice for CALC.**

Rationale:
1. CALC's architecture is **descriptor-driven**. The rule-interpreter reads descriptors to produce premises. Polarity, invertibility, context flow — all live in descriptors. Stickiness should too.
2. The flag is **declarative**. It says WHAT the constraint is, not HOW to check it. If CALC later moves to mode-indexed judgments (Phase 3 / adjoint generalization), the flag can be derived from the mode theory instead of being manually specified.
3. It mirrors the **existing `discardsContext` flag** — another descriptor-level property that affects rule applicability rather than premise generation.
4. The check is **centralized** in `applyRule` or the generic prover, not scattered across focusing logic.

**Where exactly:** The check belongs in `generic.js:applyRule()`, since that is where all rule applicability is decided. `chooseFocus` should NOT filter by succedent type — it should present monad_l as a focus choice, and `applyRule` should reject it when the succedent is wrong. This keeps the separation clean: `chooseFocus` = "what CAN we focus on?", `applyRule` = "does this rule application succeed?"

Actually, for efficiency, filtering in `chooseFocus` is acceptable: Celf does it this way (separate functions). But the canonical constraint should be recorded in the descriptor regardless.

---

## References

- Pfenning, Davies. [A Judgmental Reconstruction of Modal Logic](https://doi.org/10.1017/S0960129501003322). MSCS 11(4), 2001.
- Watkins, Cervesato, Pfenning, Walker. [CLF: A Concurrent Logical Framework](https://www.cs.cmu.edu/~fp/papers/clf04.pdf). 2004.
- Schack-Nielsen, Schurmann. [Celf](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28). IJCAR 2008. [Source](https://github.com/clf/celf).
- Lopez, Pfenning, Polakow, Watkins. [LolliMon](https://www.cs.cmu.edu/~fp/public/papers/mcllp05.pdf). PPDP 2005. [Source](https://github.com/clf/lollimon).
- Pruiksma, Chargin, Pfenning, Reed. [Adjoint Logic](https://www.cs.cmu.edu/~fp/papers/adjoint18b.pdf). 2018.
- Pruiksma, Pfenning. [Adjoint Natural Deduction](https://arxiv.org/html/2402.01428). FSCD 2024.
- Twelf. [Lax Logic Formalization](https://twelf.org/wiki/lax-logic/).
- Fairtlough, Mendler. Propositional Lax Logic. I&C 137(1), 1997.
- RES_0052 — CLF Lax Monad deep study.
- RES_0081 — CLF Type Stratification and Definitional Equality.
- TODO_0006 — Lax Monad Integration.
- TODO_0066 Phase 2 — Explicit Lax Monad specification.
