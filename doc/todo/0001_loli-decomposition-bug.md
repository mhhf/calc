---
title: "Unsound Loli Decomposition in Forward Engine"
created: 2026-02-17
modified: 2026-02-19
summary: "expandItem unsoundly decomposes guarded loli continuations — transforms conditionals into unconditional assertions, corrupting dead ⊕ branches"
tags: [forward-engine, loli, soundness, CLF, expandItem]
type: bug
cluster: Symexec
status: subsumed
priority: 10
depends_on: []
required_by: []
subsumed_by: TODO_0041
---

# Unsound Loli Decomposition in Forward Engine

**Status:** This TODO is subsumed by [TODO_0041](0041_unified-rule-matching.md), which addresses the root architectural issue (two separate rule systems) that causes this soundness bug. All detailed analysis from this document has been ported to TODO_0041.

**See also:** `doc/research/forward-chaining.md` (theory), `doc/documentation/forward-chaining-engine.md` (implementation)

## The Problem

Our EVM rules use **guarded loli continuations** inside ⊕ forks to model conditional branching:

```ill
evm/iszero:
  pc PC * code PC 0x15 * ... * stack SH V
  -o {
    pc PC' * gas GAS' * code PC 0x15 * sh (s SH) *
    ((!eq V 0 -o { stack SH 1 }) +      ← branch A: if V==0, push 1
     (!neq V 0 -o { stack SH 0 }))      ← branch B: if V≠0, push 0
  }.
```

When this rule fires, the consequent (inside `{...}`) produces shared facts (`pc PC'`, `gas GAS'`, etc.) and a `⊕` (plus) that forks the execution tree into two branches. Each branch is a **loli continuation** with a **bang guard**: `!eq V 0 ⊸ {stack SH 1}` means "IF eq(V,0) can be proved, THEN produce `stack SH 1`."

The guard `!eq V 0` is persistent (bang-wrapped) — it needs to be **proved** via backward chaining or FFI, not just found in the state. This is the theory: a loli in the state is a dormant rule that fires when its trigger becomes available. For a persistent trigger like `!P`, "available" means "provable."

## What Goes Wrong

`expandItem` in `compile.js:150-159` decomposes `!P ⊸ {Q}` into `{ linear: [Q], persistent: [!P] }`:

```javascript
// compile.js:150-159
if (t === 'loli') {
  if (Store.tag(c0) === 'bang' && Store.tag(c1) === 'monad') {
    return bodyAlts.map(a => ({
      linear: a.linear,                  // Q's body — added unconditionally!
      persistent: [c0, ...a.persistent]  // !P — asserted as fact without proving!
    }));
  }
}
```

This transforms a **conditional** ("if P then Q") into an **unconditional** assertion ("Q AND !P"). It applies modus ponens without checking the premise. Both ⊕ branches get their bodies and guards unconditionally, so:

- Branch A gets: `stack SH 1` + `!eq(V,0)` — even when V≠0
- Branch B gets: `stack SH 0` + `!neq(V,0)` — even when V=0

Dead branches run with **corrupted state** (wrong stack values, false persistent facts), producing invalid execution traces instead of becoming stuck leaves. The bug existed before ⊕ (old `evm/eq` with `&` had the same decomposition), but ⊕ on iszero/jumpi amplified it from ~2 false branches to 2^N (263 → 13109 nodes in multisig benchmark).

## Why `expandItem` Does This

`_tryFireLoli` (forward.js:602-649) handles loli continuations in the state, but only supports **linear** triggers — it matches trigger hashes against `state.linear`. A bang trigger like `!eq(V,0)` needs backward proving, which `_tryFireLoli` doesn't do. So `expandItem` was made to eagerly decompose the loli as a **workaround** to avoid the firing mechanism entirely — and the workaround is unsound.

## Why CLF Avoids This Problem Entirely

CLF restricts what can appear inside the monad `{C}` to: atoms, `⊗`, `1`, `!`, `∃`. **No lolis allowed.** This is deliberate — lolis inside the monad create "dormant rules" that need a firing mechanism (matching trigger, proving guard, scheduling). CLF's monadic semantics are simpler: everything in `{C}` immediately decomposes into state updates. The monadic let `{A} ⊗ (A ⊸ {B}) ⊸ {B}` provides sequencing at the **rule level** (between separate forward rules), not inside a single consequent.

Our EVM rules violate this restriction by putting lolis inside `{...}`. This is an extension of CLF, not standard CLF.

## `expandItem` Is Correct for Everything Except Lolis

The `{ linear, persistent }` decomposition is the right model for CLF's allowed monadic connectives:

| Connective | Decomposition | Correct? |
|---|---|---|
| `atom` | `{ linear: [atom] }` | ✓ atom becomes a linear fact |
| `A ⊗ B` | cross product of A, B | ✓ tensor distributes |
| `!A` | `{ persistent: [A] }` | ✓ bang becomes persistent |
| `1` | `{ }` (empty) | ✓ one = no resource |
| `A & B` / `A ⊕ B` | alternatives of A, B | ✓ fork the execution tree |
| `A ⊸ B` | **BUG** | ✗ should stay as linear fact, fire later |

If we remove the loli case, `expandItem` becomes exactly CLF's monadic decomposition — correct by construction.

## `_tryFireLoli` Is Theoretically a Rule Application

`_tryFireLoli` is not ad-hoc — it's an implementation of the loli-left rule applied to facts in the state. A `loli(trigger, body)` in `state.linear` is a fact of type `A ⊸ B`. When `A` appears in the state (or can be proved), the loli-left rule fires: consume the loli, consume A (or mark the proof as used), produce B. `_tryFireLoli` implements this for **linear** triggers. The missing piece is handling **persistent** (bang) triggers.

## TODO_0001.Stage_1 — Extend `_tryFireLoli` for bang triggers (correctness)

The minimal fix:
1. **Remove** the loli case from `expandItem` (lines 150-159). Lolis become linear facts in the state, handled by `_tryFireLoli`.
2. **Extend** `_tryFireLoli` to detect bang triggers (`Store.tag(trigger) === 'bang'`).
3. For bang triggers: call `tryFFIDirect(unwrapped_trigger)` or fall back to backward proving.
4. If guard proves true → fire: consume loli, produce body.
5. If guard fails → loli stays dormant, branch becomes a stuck leaf (correct behavior — no corruption).

This is a small code change (~15 LOC) and makes the engine correct for our EVM rules.

## TODO_0001.Stage_2 — Eager guard pruning at ⊕ fork time (performance)

Before creating a ⊕ branch, check if its loli guard is decidable (all arguments ground) and false. Skip dead branches at fork time rather than exploring them to quiescence. This is focusing — resolving synchronous choices eagerly when decidable. Reduces 13109 nodes back to ~63.

Note: Stage 2 is an **optimization** that depends on Stage 1 being correct. It should not be conflated with the correctness fix.

## TODO_0001.Stage_3 — Theory cleanup

See [TODO_0027](0027_clf-theory-questions.md) — exported as standalone research task (Q1-Q5, layer separation, expandItem derivation).

## Alternative: Rewrite EVM rules to avoid lolis in consequents

Instead of `(!eq V 0 -o { stack SH 1 }) + (!neq V 0 -o { stack SH 0 })`, use two separate rules with persistent antecedents:

```ill
evm/iszero_true:  ... * !eq V 0  -o { ... * stack SH 1 }.
evm/iszero_false: ... * !neq V 0 -o { ... * stack SH 0 }.
```

This is always correct (guards are checked by `tryMatch` as persistent antecedents). But it duplicates the shared antecedent (`pc * code * gas * sh * stack`) across rules, inflating the rule count. It also loses the explicit ⊕ structure that connects the two branches.

## Tradeoffs

| Approach | Correctness | Code change | Rule count | Theory |
|---|---|---|---|---|
| Extend `_tryFireLoli` | ✓ (after fix) | ~15 LOC | Same | Extends CLF (lolis in monad) |
| Split into separate rules | ✓ (by construction) | ~0 LOC engine | 2× branching rules | CLF-compliant |
| Stage 2 pruning (on top of either) | ✓ + fast | ~30 LOC | Same | Focusing optimization |

**Recommendation:** Fix `_tryFireLoli` (Stage 1). This preserves the expressive ⊕-with-loli-guard pattern, and the fix is small. Add Stage 2 for performance. Consider rule splitting later if we want strict CLF compliance.

## Why `!P -o {Q}` and Not `!P -o Q`? The Inner Monad

The EVM rules write `!eq V 0 -o { stack SH 1 }` with braces around the body, even though we're already inside the outer monad of the rule. Is the inner `{...}` necessary? What happens without it?

### What the parser produces

The parser (`convert.js:101-107`) distinguishes the two forms:

| Syntax | AST | Monad-wrapped? |
|---|---|---|
| `!P -o { Q }` | `loli(bang(P), monad(Q))` | Yes |
| `!P -o Q` | `loli(bang(P), Q)` | No |

The check is `node.text.includes('{')` — if braces are present, the body is wrapped in `monad()`.

### How `expandItem` reacts to each form

`expandItem` (compile.js:150-159) checks **both** the trigger and the body:

```javascript
if (Store.tag(c0) === 'bang' && Store.tag(c1) === 'monad') {
  // decompose — THIS IS THE BUG
}
```

- **With inner monad** (`!P -o {Q}`): Both conditions pass → `expandItem` eagerly decomposes → **BUG** (unconditional assertion).
- **Without inner monad** (`!P -o Q`): `Store.tag(c1) === 'monad'` fails → falls through to the default `return [{ linear: [h], persistent: [] }]` → loli stays as a linear fact in the state. **No bug.**

So removing the inner braces would accidentally avoid the bug — but not by fixing it. The loli would survive `expandItem` and land in `state.linear` as a dormant continuation.

### But `_tryFireLoli` can't fire it either

`_tryFireLoli` (forward.js:602-649) handles lolis in the state, but only with **linear** triggers:

```javascript
// Ground path: looks for trigger hash in state.linear
if (!state.linear[trigger] || state.linear[trigger] <= 0) return null;
```

The trigger `bang(eq(V, 0))` is not in `state.linear` (it's a persistent proposition that needs backward proving). So `_tryFireLoli` returns null → the loli never fires → the body (`stack SH 1`) is never produced → branch is stuck.

| Form | expandItem | _tryFireLoli | Result |
|---|---|---|---|
| `!P -o { Q }` | Decomposes (BUG) | Not reached | Corrupted state |
| `!P -o Q` | Passes through | Can't handle bang trigger | Permanently stuck |

Both forms are broken. The first is **dangerously** wrong (corruption, false branches). The second is **safely** wrong (stuck leaf, no corruption). Neither produces correct behavior.

### The inner monad is syntactic, not semantic

In CLF, `{A}` is the lax modality — it wraps the forward-chaining fragment. Nesting `{...}` inside an already-open monad would mean a second round of forward execution (monadic let). Our engine doesn't implement multi-round monadic semantics — `expandItem` just strips the monad and decomposes the body. The inner `{...}` functions as a **signal to `expandItem`** that this body should be decomposed into state updates, not as a semantic distinction.

But lolis inside monads are already non-standard (CLF forbids them — see "Why CLF Avoids This Problem Entirely" above). So the question of whether the inner loli body is `{Q}` or `Q` is a syntactic detail of our extension, not a CLF-theoretic question.

### After Stage 1, either form works

Stage 1 extends `_tryFireLoli` for bang triggers: detect `Store.tag(trigger) === 'bang'`, call `tryFFIDirect` to prove the guard. With this fix:

- Lolis survive `expandItem` (because the loli case is removed)
- `_tryFireLoli` detects the bang trigger and proves it
- Guard succeeds → fire loli, produce body (correct)
- Guard fails → loli stays dormant, branch stuck (correct)

After Stage 1, both `!P -o {Q}` and `!P -o Q` work correctly. `_tryFireLoli` already handles both: `const bodyInner = Store.tag(body) === 'monad' ? Store.child(body, 0) : body` (forward.js:605). The inner monad becomes irrelevant — keep it or drop it, behavior is the same.

**Recommendation:** After Stage 1, drop the inner monad. Write `!eq V 0 -o stack SH 1` instead of `!eq V 0 -o { stack SH 1 }`. The simpler form is clearer, and the inner braces served no semantic purpose — they only existed because `expandItem` needed them as a decomposition signal, which is the very code path we're removing.

## Phase 4 Status: ⊕ Implemented, Bug Found
- [x] Analysis: ⊕ is the correct connective (not &) for decidable case splits
- [x] B1 independence: Problem B is independent of Problem A
- [x] Add `plus` (⊕) connective to `ill.calc` + rules to `ill.rules`
- [x] Grammar: `expr_plus` in tree-sitter, `convert.js`, `cst-to-ast.js`
- [x] Forward engine: `expandItem` treats `plus` like `with` (fork)
- [x] Focusing: ⊕ positive, ⊕L invertible, regex updated for numbered right rules
- [x] EVM rules rewritten: evm/eq (& → +), evm/iszero + evm/jumpi (merged with +)
- [x] Tests: 513 pass (397 core + 116 engine)
- [ ] **BUG: expandItem loli decomposition is unsound** — see above
- [ ] Stage 1: Extend `_tryFireLoli` for bang triggers, remove loli case from `expandItem`
- [ ] Stage 2: Eager guard pruning at ⊕ fork time
- [ ] Decide: keep loli-in-monad extension or split into separate rules?
