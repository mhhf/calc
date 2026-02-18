---
title: "Unified Rule Matching — Compiled Rules and Loli Continuations"
created: 2026-02-18
modified: 2026-02-18
summary: "The engine has two separate rule-firing mechanisms that should be one — compiled rules (full optimization pipeline) vs loli continuations (ad-hoc fallback). This causes a priority bug in exhaustive exploration and duplicates the forward/backward boundary."
tags: [architecture, forward-engine, loli, matching, soundness]
type: design
status: planning
priority: 8
depends_on: []
required_by: [TODO_0006, TODO_0010]
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

## References

- `doc/research/forward-chaining.md` §6 (lolis as continuations)
- `doc/documentation/forward-chaining-engine.md` §5.3, §7
- [TODO_0001](0001_loli-decomposition-bug.md) — the immediate soundness fix
- [TODO_0006](0006_lax-monad-integration.md) — monad operational semantics
- [TODO_0010](0010_ceptre-stages.md) — Ceptre stages (depends on monad)
- [TODO_0027](0027_clf-theory-questions.md) — Q3 (what is `_tryFireLoli` theoretically?)
