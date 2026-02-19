---
title: "Unified Rule Matching — Compiled Rules and Loli Continuations"
created: 2026-02-18
modified: 2026-02-19
summary: "The engine has two separate rule-firing mechanisms that should be one — compiled rules (full optimization pipeline) vs loli continuations (ad-hoc fallback). This causes a priority bug in exhaustive exploration and duplicates the forward/backward boundary."
tags: [architecture, forward-engine, loli, matching, soundness]
type: design
status: planning
priority: 10
depends_on: []
required_by: [TODO_0002, TODO_0006, TODO_0010]
subsumes: [TODO_0001]
---

# Unified Rule Matching

## The Problem: Two Rule Systems

The forward engine fires rules through two completely separate mechanisms:

**System A — Compiled rules** (main pipeline):
- Static, loaded from `.ill` at startup
- Full compilation: de Bruijn slots, discriminator, strategy stack, compiled substitution
- Matched by `tryMatch()` (delta bypass, secondary index, general matching)
- Phase 2 proves persistent antecedents (FFI → state lookup → backward chaining)
- Persistent — never consumed

**System B — Loli continuations** (`_tryFireLoli`):
- Dynamic, created at runtime by rule consequents
- No compilation, no indexing, no optimization
- Ad-hoc matching: fresh `collectMetavars()` + `matchIndexed()` per attempt
- Only linear trigger matching (no persistent proving — the TODO_0001 bug)
- Linear — consumed on firing

In the theory, both are the same thing: a rule with antecedents (linear: find in state, persistent: prove) and a consequent (facts to produce). The only structural difference is persistence:
- `!(A ⊸ B)` = persistent rule (compiled, never consumed)
- `A ⊸ B` in state = linear rule (one-shot, consumed)

Both should go through the same matching pipeline.

## The Priority Bug

`findAllMatches` (symexec.js:611):
```javascript
if (matches.length === 0) {
  const loliMatches = findAllLoliMatches(state);
```

Loli matches are only considered when NO compiled rule matches. For exhaustive exploration this is wrong — both should compete as equal candidates.

Example: state has `pc(5), code(5, 0x01), ..., loli(trigger, body)` where trigger is present. Both the ADD rule and the loli can fire. The explorer should branch on both. Instead, only the ADD rule is considered.

This is currently masked because EVM loli triggers (`unblockConcatMemory Z`) are only produced by helper rules that run while opcode rules can't fire. Correctness depends on program shape, not engine semantics.

## The Causal Chain

```
Monad is hollow (no staging semantics) — see TODO_0006
    ↓
Can't express "prove guard, then produce" inside monadic consequent
    ↓
expandItem eagerly decomposes loli-in-monad (workaround)
    ↓
_tryFireLoli exists as separate ad-hoc system — see TODO_0001
    ↓
Two separate rule systems with different capabilities
    ↓
Priority bug: lolis only fire as fallback
```

## Duplicated Forward/Backward Boundary

The engine implements the forward/backward boundary twice:

1. `tryMatch` Phase 2: proves persistent antecedents via FFI → state lookup → backward chaining
2. `_tryFireLoli`: matches triggers against `state.linear` only (can't prove persistent triggers)

A unified system would have one forward/backward boundary. Every rule — compiled or loli — goes through the same antecedent matching: linear patterns against state, persistent patterns proved.

## Design

### This TODO (subsumes TODO_0001)

Unify compiled rules and loli continuations into one matching pipeline. This fixes both the soundness bug (TODO_0001) and the priority bug in one shot. `_tryFireLoli` is deleted entirely.

1. Remove the loli case from `expandItem` (compile.js:150-159). Lolis become linear facts in the state.
2. In `findAllMatches`, scan `state.linear` for loli facts alongside compiled rule matching.
3. For each loli `trigger ⊸ body`: split trigger via `flattenTensor` into linear/persistent antecedents, split body via `flattenTensor(unwrapMonad(body))` into consequent.
4. Run through `tryMatch` logic (same Phase 1 linear matching + Phase 2 persistent proving). Bang triggers get persistent proving for free.
5. If matched: consume the loli from state + consume linear antecedents + produce consequent.
6. Loli candidates and compiled rules compete as equals — no priority ordering.
7. Delete `_tryFireLoli`, `findLoliMatch`, `findAllLoliMatches`, `applyLoliMatch`.

Open questions:
- Compile lolis on creation (amortize cost) or interpret each time (simpler)?
- How to index lolis in the strategy stack? (They're dynamic, so fingerprint layer won't claim them — fall through to disc-tree or predicate filter)
- Performance: how many lolis are typically in state? (Currently: 0-1 for EVM. If always few, compilation overhead isn't worth it.)

### Future — Monadic staging (TODO_0006)

Give the monad operational semantics. Makes lolis-in-monads unnecessary — guards go in rule antecedents, staging goes through monadic let. Essentially: Ceptre stages.

## What CLF/Ceptre Got Right

- **CLF** forbids lolis inside the monad — forces all guards into the rule's antecedent. No `expandItem` hack needed.
- **Ceptre** has stages — structured quiescence where rule subsets run in phases. The SHA3 pattern (start helpers → iterate → fire continuation) is ad-hoc staging.
- **CLF** allows `∃x.C` in the monad — existential quantification creates fresh names. We have no existential; every consequent variable must be bound by the antecedent.

## Detailed Analysis (from TODO_0001)

### The Soundness Bug in `expandItem`

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

When this rule fires, the consequent produces shared facts and a `⊕` that forks into two branches. Each branch is a **loli continuation** with a **bang guard**: `!eq V 0 ⊸ {stack SH 1}` means "IF eq(V,0) can be proved, THEN produce `stack SH 1`."

The guard `!eq V 0` is persistent (bang-wrapped) — it needs to be **proved** via backward chaining or FFI, not just found in the state.

### What Goes Wrong

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

### Why `expandItem` Does This

`_tryFireLoli` (forward.js:602-649) handles loli continuations in the state, but only supports **linear** triggers — it matches trigger hashes against `state.linear`. A bang trigger like `!eq(V,0)` needs backward proving, which `_tryFireLoli` doesn't do. So `expandItem` was made to eagerly decompose the loli as a **workaround** to avoid the firing mechanism entirely — and the workaround is unsound.

### Why CLF Avoids This Problem Entirely

CLF restricts what can appear inside the monad `{C}` to: atoms, `⊗`, `1`, `!`, `∃`. **No lolis allowed.** This is deliberate — lolis inside the monad create "dormant rules" that need a firing mechanism (matching trigger, proving guard, scheduling). CLF's monadic semantics are simpler: everything in `{C}` immediately decomposes into state updates. The monadic let `{A} ⊗ (A ⊸ {B}) ⊸ {B}` provides sequencing at the **rule level** (between separate forward rules), not inside a single consequent.

Our EVM rules violate this restriction by putting lolis inside `{...}`. This is an extension of CLF, not standard CLF.

### `expandItem` Is Correct for Everything Except Lolis

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

### `_tryFireLoli` Is Theoretically a Rule Application

`_tryFireLoli` is not ad-hoc — it's an implementation of the loli-left rule applied to facts in the state. A `loli(trigger, body)` in `state.linear` is a fact of type `A ⊸ B`. When `A` appears in the state (or can be proved), the loli-left rule fires: consume the loli, consume A (or mark the proof as used), produce B. `_tryFireLoli` implements this for **linear** triggers. The missing piece is handling **persistent** (bang) triggers.

### The Inner Monad Question: `!P ⊸ {Q}` vs `!P ⊸ Q`

The EVM rules write `!eq V 0 -o { stack SH 1 }` with braces around the body, even though we're already inside the outer monad of the rule. Is the inner `{...}` necessary?

#### What the parser produces

The parser (`convert.js:101-107`) distinguishes the two forms:

| Syntax | AST | Monad-wrapped? |
|---|---|---|
| `!P -o { Q }` | `loli(bang(P), monad(Q))` | Yes |
| `!P -o Q` | `loli(bang(P), Q)` | No |

The check is `node.text.includes('{')` — if braces are present, the body is wrapped in `monad()`.

#### How `expandItem` reacts to each form

`expandItem` checks **both** the trigger and the body:

```javascript
if (Store.tag(c0) === 'bang' && Store.tag(c1) === 'monad') {
  // decompose — THIS IS THE BUG
}
```

- **With inner monad** (`!P -o {Q}`): Both conditions pass → `expandItem` eagerly decomposes → **BUG** (unconditional assertion).
- **Without inner monad** (`!P -o Q`): `Store.tag(c1) === 'monad'` fails → falls through to default → loli stays as a linear fact in the state. **No bug.**

So removing the inner braces would accidentally avoid the bug — but not by fixing it. The loli would survive `expandItem` and land in `state.linear` as a dormant continuation.

#### But `_tryFireLoli` can't fire it either

`_tryFireLoli` only handles **linear** triggers:

```javascript
// Ground path: looks for trigger hash in state.linear
if (!state.linear[trigger] || state.linear[trigger] <= 0) return null;
```

The trigger `bang(eq(V, 0))` is not in `state.linear` (it's a persistent proposition that needs backward proving). So `_tryFireLoli` returns null → the loli never fires → branch is stuck.

| Form | expandItem | _tryFireLoli | Result |
|---|---|---|---|
| `!P -o { Q }` | Decomposes (BUG) | Not reached | Corrupted state |
| `!P -o Q` | Passes through | Can't handle bang trigger | Permanently stuck |

Both forms are broken. The first is **dangerously** wrong (corruption, false branches). The second is **safely** wrong (stuck leaf, no corruption). Neither produces correct behavior.

#### The inner monad is syntactic, not semantic

In CLF, `{A}` is the lax modality — it wraps the forward-chaining fragment. Nesting `{...}` inside an already-open monad would mean a second round of forward execution (monadic let). Our engine doesn't implement multi-round monadic semantics — `expandItem` just strips the monad and decomposes the body. The inner `{...}` functions as a **signal to `expandItem`** that this body should be decomposed into state updates, not as a semantic distinction.

But lolis inside monads are already non-standard (CLF forbids them). So the question of whether the inner loli body is `{Q}` or `Q` is a syntactic detail of our extension, not a CLF-theoretic question.

#### After the fix, either form works

With unified rule matching, lolis survive `expandItem` (the loli case is removed) and go through the same matching pipeline as compiled rules. Bang triggers get persistent proving for free. `_tryFireLoli` already handles both forms: `const bodyInner = Store.tag(body) === 'monad' ? Store.child(body, 0) : body` (forward.js:605).

After the fix, both `!P -o {Q}` and `!P -o Q` work correctly. The inner monad becomes irrelevant.

**Recommendation:** After the fix, drop the inner monad. Write `!eq V 0 -o stack SH 1` instead of `!eq V 0 -o { stack SH 1 }`. The simpler form is clearer, and the inner braces served no semantic purpose — they only existed because `expandItem` needed them as a decomposition signal, which is the code path we're removing.

### Alternative: Rewrite EVM rules to avoid lolis in consequents

Instead of `(!eq V 0 -o { stack SH 1 }) + (!neq V 0 -o { stack SH 0 })`, use two separate rules with persistent antecedents:

```ill
evm/iszero_true:  ... * !eq V 0  -o { ... * stack SH 1 }.
evm/iszero_false: ... * !neq V 0 -o { ... * stack SH 0 }.
```

This is always correct (guards are checked by `tryMatch` as persistent antecedents). But it duplicates the shared antecedent (`pc * code * gas * sh * stack`) across rules, inflating the rule count. It also loses the explicit ⊕ structure that connects the two branches.

### Tradeoffs

| Approach | Correctness | Code change | Rule count | Theory |
|---|---|---|---|---|
| Unified rule matching | ✓ (after fix) | ~50 LOC | Same | Extends CLF (lolis in monad) |
| Split into separate rules | ✓ (by construction) | ~0 LOC engine | 2× branching rules | CLF-compliant |
| Eager pruning (on top of unified) | ✓ + fast | +30 LOC | Same | Focusing optimization |

**Recommendation:** Unified rule matching. This preserves the expressive ⊕-with-loli-guard pattern, and the fix addresses both soundness and architectural issues. Add eager pruning for performance. Consider rule splitting later if we want strict CLF compliance.

## References

- `doc/research/forward-chaining.md` §6 (lolis as continuations)
- `doc/documentation/forward-chaining-engine.md` §5.3, §7
- [TODO_0001](0001_loli-decomposition-bug.md) — the immediate soundness fix
- [TODO_0006](0006_lax-monad-integration.md) — monad operational semantics
- [TODO_0010](0010_ceptre-stages.md) — Ceptre stages (depends on monad)
- [TODO_0027](0027_clf-theory-questions.md) — Q3 (what is `_tryFireLoli` theoretically?)
