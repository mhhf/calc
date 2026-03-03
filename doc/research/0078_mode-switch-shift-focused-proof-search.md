---
title: "Mode-Switch / Shift Rules in Focused Proof Search"
created: 2026-03-03
modified: 2026-03-03
summary: "How shift/monad/stage rules trigger mode changes in focused proof search across adjoint logic, CLF/Celf, LolliMon, and Ceptre"
tags: [focusing, linear-logic, clf, Celf, lollimon, Ceptre, adjoint-logic, forward-chaining, backward-chaining, polarity, proof-search, monad, lax-monad]
category: "Related Paradigms"
---

# Mode-Switch / Shift Rules in Focused Proof Search

## 1. Adjoint Logic (Pruiksma et al. 2018): Shift Rules

In adjoint logic, modes of truth (m, k, ...) are organized in a preorder,
each with structural properties from {W, C}. Shifts mediate between modes:

- **Up-shift** `↑^k_m A_m`: lifts from mode m to mode k (requires m <= k)
- **Down-shift** `↓^k_m A_k`: lowers from mode k to mode m (requires m <= k)

### Sequent rules (from ADJ^E, explicit structural rules)

```
        Gamma |- A_m    [Gamma |- m]
  ↑R:  ──────────────────────────────
          Gamma |- (↑^k_m A)_k

        Gamma, x:A_m |- C_k
  ↑L:  ──────────────────────────────
        Gamma, x:(↑^k_m A)_k |- C_k


          Gamma |- A_k    [Gamma |- m]
  ↓R:  ──────────────────────────────
          Gamma |- (↓^k_m A)_m

        Gamma, x:A_k |- C_m
  ↓L:  ──────────────────────────────
        Gamma, x:(↓^k_m A)_m |- C_m
```

### Polarity and Focusing

In the focused system (ADJ^F):

- **↑ is negative** (asynchronous): ↑R is *invertible* -- applied eagerly in
  the inversion phase. ↑L is non-invertible (requires focus).
- **↓ is positive** (synchronous): ↓L is *invertible* -- applied eagerly.
  ↓R is non-invertible (requires focus).

This matches the standard polarity pattern: shifts are *not* special-cased
in focusing. They behave exactly like any connective with known polarity.
The shift merely changes the mode annotation on the sequent, which alters
what structural rules (weakening/contraction) are available.

Shifts are treated as **regular connective rules** in the focused calculus.
They have the same structure as tensor, loli, etc. -- they just happen to
change the mode subscript. A descriptor could represent them naturally.

### Key Insight

Shifts do NOT change the proof search *strategy* (forward vs backward).
They change the *structural discipline* (what resources are available).
The focusing discipline handles them uniformly via polarity.

## 2. CLF/Celf: Monad Introduction `{}I`

In CLF, the monadic type `{S}` wraps synchronous types (tensor, one, bang,
exists) inside an asynchronous shell. The key: `{S}` is the *only*
asynchronous (negative) type whose right rule triggers forward chaining.

### The Rule in Celf's OpSem.sml

The `solve'` function dispatches on the goal type:

```sml
(* solve' : ... -> unit *)
(* Right Inversion : Gamma;Delta => A *)
and solve' (ctx, ty, sc) = case Util.typePrjAbbrev ty of
    TLPi (p, S, A) => ...          (* backward: recurse *)
  | AddProd (A, B) => ...          (* backward: split *)
  | TMonad S => forwardChain (...)  (* *** MODE SWITCH *** *)
  | P as TAtomic _ => matchAtom ...  (* backward: focus on hyp *)
```

The switch is a **hardcoded pattern match** on `TMonad`. When
backward-chaining proof search encounters a goal of type `{S}`, it calls
`forwardChain` instead of continuing backward search.

### How forwardChain Works

```sml
and forwardChain' (fcLim, (l, ctx), S, sc) =
  (* 1. Find monadic hypotheses (HdMonad heads) *)
  (* 2. Try monLeftFocus on each: committed choice *)
  (* 3. If found: bind result, recurse into forward chain *)
  (* 4. If none: fall through to rightFocus (construct monad) *)
```

The forward chainer uses `monLeftFocus` (distinct from `leftFocus`) which
decomposes hypotheses until it reaches `TMonad sty`, returning the sync
type. Crucially, `forwardChain` uses **committed choice** (no backtracking
on forward steps), while backward chaining uses full backtracking.

### Judgment Separation

- Outside monad: `solve` (right inversion, backward chaining with backtracking)
- Inside monad: `forwardChain` (forward chaining with committed choice)
- The `rightFocus` function handles sync type decomposition (tensor, bang, etc.)
- `monLeftFocus` vs `leftFocus`: two distinct left-focusing functions for
  the two modes

### Is `{S}` a Regular Connective?

No. `{S}` is **special-cased**. It has its own AST constructor (`TMonad`),
its own dispatch branch, and triggers an entirely different search procedure.
It is not handled through a generic connective mechanism.

The signature table also treats it specially: hypotheses are classified as
either `HdAtom a` (for atomic goals) or `HdMonad` (for monadic heads).
`getCandMonad()` retrieves all monadic candidates separately from atomic ones.

## 3. LolliMon: Detecting the Forward/Backward Switch

In LolliMon (OCaml, `tfplus.ml`), the backward chainer is a single
`solve` function that pattern-matches on the goal connective. The monadic
goal `{S}` is represented as `Const "{}" 0 [goal]`.

### The Switch Point

```ocaml
(* In solve, line 316 *)
(targ as Const "{}" 0 [goal]) ->
    (* ... setup ... *)
    let rec forward al ar dl dr s d goal again addedFrms clauses banned kf ks =
    match clauses with
      [] ->
        if again then
          forward ... (permute (allMon ctx)) ...
        else
          solve al ar dl dr s d goal (ffail kf) (ks addedFrms)
    | [(a',gl',tKnd)::cls] ->
        (* try clause, committed choice on success *)
```

The switch IS triggered by matching `{S}` as a connective in the goal.
`"{}"` is a constant like `","` (tensor) or `"-o"` (loli). The `solve`
function has cases for `","`, `"!"`, `"-o"`, `"&"`, `";"`, etc., and
`"{}"` is just another case -- but its handler enters an entirely
different code path (the `forward` inner function).

### Mechanism Details

1. `solve` sees `Const "{}" 0 [goal]` in the goal position
2. It collects all monadic clauses via `allMon ctx` (clauses whose head
   matches `"{}"`)
3. It enters the `forward` loop which tries clauses with committed choice
4. Each successful clause fires `breakdown` which adds conclusions to ctx
5. When no more clauses fire (`again = false`), it solves the inner goal
   via backward chaining: `solve ... goal ...`
6. Clauses are residuated specially: `"{}"` headed clauses are unordered

### Key Detail

`"{}"` is treated as a **connective** syntactically (it is a `Const` like
any other connective). But its handling in `solve` is hardcoded --
the forward-chaining loop is bespoke code, not a generic connective handler.

## 4. Descriptor-Based Mode-Switching: Clean Theory

Given CALC's descriptor-based rule system where rules are data:

```js
{ connective: 'tensor', side: 'r', arity: 2,
  copyContext: false, contextSplit: 'lr', ... }
```

How would you represent "when you see this connective, switch execution mode"?

### Option A: Polarity-Driven (Adjoint Logic Style)

Assign polarity to connectives. The focusing discipline already determines
which rules are applied eagerly (invertible/async) vs require choice
(sync/focus). A mode-switch connective is just a connective whose **right
rule is invertible** and whose handler changes the strategy:

```js
{ connective: 'monad', side: 'r', arity: 1,
  invertible: true,
  executionMode: 'forward'  // <-- new descriptor field
}
```

The prover's inversion phase checks `executionMode` and delegates to a
different search procedure. This is essentially what Celf does, but with
the `TMonad` case replaced by a data-driven check.

### Option B: Strategy Tag in Descriptor

Add a `strategy` field to rule descriptors:

```js
{ connective: 'monad', side: 'r', arity: 1,
  strategy: 'forward-chain',  // or 'backward-chain' (default)
  committed: true,             // committed choice vs backtracking
  premiseMode: 'synchronous'   // inner type discipline
}
```

When the rule interpreter encounters this descriptor, it dispatches to
the appropriate strategy layer instead of the default prover.

### Option C: Judgment-Level Switch (CLF Style)

Define distinct judgment forms and let the connective's descriptor specify
which judgment the premise lives in:

```js
// The monad right-rule: conclusion is async, premise is sync
{ connective: 'monad', side: 'r', arity: 1,
  premiseJudgment: 'synchronous',  // different judgment form
  conclusionJudgment: 'asynchronous'
}

// The let-binding rule (monad left): decomposes in forward mode
{ connective: 'monad', side: 'l', arity: 2,
  premiseJudgment: ['synchronous', 'asynchronous'],
  committed: true  // no backtracking on first premise
}
```

### Recommendation for CALC

The cleanest approach is **Option A**: extend the descriptor with an
`executionMode` field. The focused proof search already has the concept
of phases (inversion vs focus). The monad right-rule is invertible, so
it fires eagerly in the inversion phase. The only new thing is that
instead of generating premises for the same prover, it delegates to
the forward engine.

This keeps the descriptor system uniform -- the rule interpreter reads
data and dispatches. The *only* hardcoded part is the mapping from
`executionMode: 'forward'` to the actual forward-chaining implementation,
which is unavoidable since forward chaining is a fundamentally different
algorithm.

## 5. Ceptre: Stage Transitions

Ceptre is a pure forward-chaining linear logic language. It does not have
backward chaining at all. Stages provide a different kind of mode switch:
grouping rules into phases that execute to quiescence.

### Stage Declaration Syntax

```ceptre
stage roll = {
  roll1 : die -o roll h1.
  roll2 : die -o roll h2.
}

stage produce = {
  process_roll : roll H * produces H R -o mete R Is.
  mete/nil : mete R nil -o ().
}
```

### Stage Transition Mechanism

Stage transitions are **rules at the outer level**:

```ceptre
roll_to_prod : qui * stage roll -o stage produce.
```

The `qui` token is a special predicate that is **injected into the context
by the runtime** when a stage reaches quiescence (no more rules apply).
Stage transitions are then just forward rules that consume `qui` and a
`stage X` fact and produce a `stage Y` fact.

### Implementation (exec.sml + ceptre.sml)

```sml
(* The qui fact is inserted by the runtime *)
val qui = (Ceptre.Lin, "qui", [])

fun quiesce take_transition fastctx steps =
  let
    val (fastctx, var) = CoreEngine.insert fastctx qui
  in
    case CoreEngine.possible_steps "outer_level" fastctx of
      [] => (fastctx, rev steps)  (* globally quiescent *)
    | L => pick Random L ...      (* fire an outer-level rule *)
  end
```

Stage transitions are compiled to regular forward rules via `stageRuleToRule`:

```sml
fun stageRuleToRule {name, pivars, pre_stage, lhs, post_stage, rhs} =
  let
    val lhs = (unaryPred "stage" pre_stage)::lhs
    val rhs = (unaryPred "stage" post_stage)::rhs
  in
    {name=name, pivars=pivars, lhs=lhs, rhs=rhs}
  end
```

And the outer level is compiled to a stage containing these rules:

```sml
fun progToRulesets ({stages, links, init_stage, init_state}) =
  let
    val outer_level_rules = map stageRuleToRule links
    val outer_level = {name="outer_level", nondet=Random, body=outer_level_rules}
  in
    (outer_level::stages, ...)
  end
```

### Is It Hardcoded?

**Hybrid.** The stage transition *rules* are user-defined data (just forward
rules with `stage X` predicates). But the *quiescence detection* and
*qui injection* are hardcoded in the runtime. The two-level structure
(inner stage + outer level) is also hardcoded. So:

- Stage rules themselves: **data** (descriptors)
- Quiescence detection: **hardcoded** runtime behavior
- `qui` injection: **hardcoded** runtime behavior
- Two-level dispatch: **hardcoded** architecture

## Summary Table

| System | Switch Trigger | Mechanism | Hardcoded? |
|--------|---------------|-----------|------------|
| Adjoint Logic | Shift connective | Regular rule, changes mode annotation | No -- fully generic via polarity |
| CLF/Celf | `TMonad` type | Pattern match in `solve'` dispatches to `forwardChain` | Yes -- bespoke AST variant + handler |
| LolliMon | `"{}"` connective | Pattern match in `solve` enters `forward` loop | Yes -- bespoke case in solve |
| Ceptre | Quiescence + `qui` | Runtime injects `qui`, outer-level rules fire | Hybrid -- rules are data, detection is hardcoded |

## Key Theoretical Insight

The mode switch in focused proof search is fundamentally about **polarity**.
In Andreoli's focusing, negative connectives (loli, with) are invertible
and handled eagerly; positive connectives (tensor, oplus) require choice.
The monad `{S}` adds a third behavior: an invertible connective whose
premise lives in a *different search discipline*.

In adjoint logic, this is cleanest: shifts are just connectives with known
polarity that change the mode index. No special-casing needed.

In CLF/Celf/LolliMon, the monad is special because it changes not just
the structural discipline but the *search algorithm* (committed choice
vs backtracking). This operational distinction cannot be captured by
polarity alone -- it requires an explicit execution-mode annotation.

For CALC's descriptor system, the recommendation is: add an
`executionMode` field to descriptors. The focusing discipline handles
*when* the rule fires (inversion phase, since it is invertible). The
`executionMode` field handles *how* the premise is searched (forward
engine vs backward prover).
