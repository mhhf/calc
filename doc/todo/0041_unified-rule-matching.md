---
title: "Unified Rule Matching — Compiled Rules and Loli Continuations"
created: 2026-02-18
modified: 2026-02-20
summary: "Unify compiled rules and loli continuations into one matching pipeline with a shared persistent-proving helper. Fixes the expandItem soundness bug and the priority bug in exhaustive exploration."
tags: [architecture, forward-engine, loli, matching, soundness]
type: design
cluster: Symexec
status: done
priority: 10
depends_on: []
required_by: [TODO_0002, TODO_0006, TODO_0010, TODO_0042, TODO_0045]
subsumes: [TODO_0001]
---

# Unified Rule Matching

## Problem

The forward engine has two separate rule-firing mechanisms for what is theoretically the same operation:

| | Compiled rules | Loli continuations |
|---|---|---|
| Source | Static, from `.ill` at startup | Dynamic, from rule consequents at runtime |
| Matching | `tryMatch()`: full pipeline with Phase 1 (linear) + Phase 2 (persistent proving) | `_tryFireLoli()`: linear trigger only, no persistent proving |
| Persistence | `!(A ⊸ {B})` — never consumed | `A ⊸ {B}` in state — consumed on firing |
| Optimization | de Bruijn slots, discriminator, strategy stack, compiled substitution | None |

In ILL, both are the same: a rule with antecedents and a consequent. The only structural difference is persistence. Both should use one matching pipeline.

### Bug 1: Unsound `expandItem` decomposition

`expandItem` (compile.js:150-159) transforms conditional `!P ⊸ {Q}` into unconditional `Q AND !P`:

```javascript
if (Store.tag(c0) === 'bang' && Store.tag(c1) === 'monad') {
  return bodyAlts.map(a => ({
    linear: a.linear,                  // Q — added unconditionally
    persistent: [c0, ...a.persistent]  // !P — asserted without proving
  }));
}
```

This exists because `_tryFireLoli` can't prove persistent triggers, so `expandItem` eagerly decomposes as a workaround. The workaround applies modus ponens without checking the premise. Both ⊕ branches get bodies and guards unconditionally — dead branches run with corrupted state (wrong stack values, false persistent facts).

### Bug 2: Priority ordering in exhaustive exploration

`findAllMatches` (symexec.js:611) only considers lolis when NO compiled rule matches:

```javascript
if (matches.length === 0) {
  const loliMatches = findAllLoliMatches(state);
```

For exhaustive exploration, both should compete as equal candidates. Currently masked because EVM loli triggers only appear when opcode rules can't fire.

### Duplicated forward/backward boundary

The engine implements persistent proving twice:
1. `tryMatch` Phase 2: FFI → state lookup → backward chaining
2. `_tryFireLoli`: linear matching only (can't prove persistent triggers)

## Theoretical Safety: Why Lolis in Consequents Are Sound

A loli produced by a rule consequent is LINEAR — it lives in `state.linear`, fires once, is consumed. The concern that `!A ⊸ B` could behave like `!(A ⊸ B)` (persistent, infinite firing) is prevented by ILL's promotion rule:

```
!Γ; · ⊢ A
────────── !R (bang_r)
!Γ; · ⊢ !A
```

bang_r requires the linear context to be **empty**. The formula `!A ⊸ B` is in the linear context (it's `loli(bang(A), B)`, not `bang(loli(A, B))`), so promotion is blocked. You cannot derive `!(A ⊸ B)` from `!A ⊸ B` in ILL — the linear/persistent distinction is structurally enforced.

In our implementation: lolis go in `state.linear[hash] = 1`, consumed on firing (decremented to 0). No code path migrates facts from `state.linear` to `state.persistent`.

CLF forbids lolis in the monad for **operational simplicity** (dormant rules need matching/scheduling infrastructure), not for soundness. Our extension provides this infrastructure via unified rule matching.

## Design (Option B: Extract Shared Proving)

The theoretical identity — compiled rules and loli continuations are both rule applications — should be explicit in code. Extract the persistent proving logic from `tryMatch` into a shared helper, then use it for both.

### Steps

**1. Extract `provePersistentGoals` from `tryMatch` (forward.js Phase 2)**

Factor out the persistent proving loop (~40 lines) into a standalone function:
```
provePersistentGoals(patterns, theta, slots, state, calc) → boolean
```
This runs the same pipeline for any rule: FFI direct → state lookup → backward chaining. Both `tryMatch` (for compiled rules) and the new loli matcher call it.

**2. Remove loli case from `expandItem` (compile.js:150-159)**

Delete the `if (t === 'loli') { ... }` block. Lolis fall through to default, becoming linear facts in state. `expandItem` becomes exactly CLF's monadic decomposition — correct by construction for all connectives.

**3. Write `matchLoli(h, state, calc)` in forward.js**

For each `loli(trigger, body)` in `state.linear`:
1. `flattenTensor(trigger)` → `{ linear: [...], persistent: [...] }`
2. `flattenTensor(unwrapMonad(body))` → consequent
3. Collect metavars, assign slots (same de Bruijn scheme as compiled rules)
4. Phase 1: match linear trigger patterns against `state.linear`
5. Phase 2: `provePersistentGoals(persistent, theta, slots, state, calc)`
6. If matched: return `{ consumed: {loli + linear triggers}, produced: consequent, theta, slots }`

**4. Unify in `findAllMatches` (symexec.js)**

Scan `state.linear` for loli facts alongside compiled rule matching. No priority ordering — both compete as equals. Loli matches wrapped as synthetic rules (existing pattern, symexec.js:614-628).

**5. Unify in `run` (forward.js)**

Try compiled rules first (committed choice), then lolis. For committed choice the ordering is pragmatic, not a correctness issue.

**6. Delete old loli functions**

Remove: `_tryFireLoli`, `findLoliMatch`, `findAllLoliMatches`, `applyLoliMatch`.

### After the fix

| Loli pattern | Trigger handling | Example |
|---|---|---|
| `!guard -o {body}` in `+` | Persistent proving via `provePersistentGoals` | iszero, eq, jumpi |
| `linear_trigger -o {body}` | Linear matching against state | calldatacopy (`unblock`) |
| `param(X) -o {body}` | Parameterized linear matching | SHA3 (`unblockConcatMemory Z`) |
| Mixed `A * !B -o {body}` | Phase 1 linear + Phase 2 persistent | (future) |

All forms work through one pipeline. Dead branches become stuck leaves (correct) instead of running with corrupted state (current bug).

`expandConsequentChoices` should be applied to loli consequents too (for `+`/`&` in loli bodies, even though EVM loli bodies are currently simple).

### What survives into TODO_0006

When monadic staging (TODO_0006) eventually eliminates loli-in-consequents:
- `provePersistentGoals` stays — `tryMatch` needs it regardless
- `matchLoli` + loli scanning code are deleted
- The shared proving helper is the permanent foundation

## EVM Rule Patterns

Three rules use guarded loli continuations with ⊕:

```ill
evm/iszero: ... -o { shared * ((!eq V 0 -o { stack SH 1 }) + (!neq V 0 -o { stack SH 0 })) }.
evm/eq:     ... -o { shared * ((!neq X Y -o { stack SH 0 }) + (!eq X Y -o { stack SH 1 })) }.
evm/jumpi:  ... -o { shared * ((!neq C 0 -o { pc NPC }) + (!eq C 0 -o { pc PC' })) }.
```

Two rules use linear loli continuations:

```ill
evm/calldatacopy: ... -o { shared * (unblock -o {pc PC'}) }.
evm/sha3:        ... -o { shared * (unblockConcatMemory Z -o { ... }) }.
```

After the fix, the `+` forks into alternatives at the parent rule level. Each alternative produces a loli fact in state. The loli fires (or doesn't) independently. Guard failure → stuck leaf. Guard success → body produced.

Optional future optimization: rewrite `+`-with-loli-guard patterns into separate compiled rules (guards as persistent antecedents). This eliminates dynamic loli matching entirely but duplicates shared antecedents. Benchmark first.

## References

- `doc/theory/exhaustive-forward-chaining.md` — CALC's theoretical position (CLF extensions, loli linearity)
- `doc/research/chr-linear-logic.md` — CHR ↔ linear logic soundness (Betz & Frühwirth)
- `doc/research/forward-chaining.md` §6 — lolis as continuations
- `doc/documentation/forward-chaining-engine.md` §5.3, §7 — current implementation
- [TODO_0001](0001_loli-decomposition-bug.md) — subsumed (the immediate soundness bug)
- [TODO_0006](0006_lax-monad-integration.md) — future: monad operational semantics
- [TODO_0043](0043_chr-linear-logic-mapping.md) — CHR∨ soundness mapping for ⊕
