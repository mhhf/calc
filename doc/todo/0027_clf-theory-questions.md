---
title: "CLF Theory Questions: Loli, Monad, Layer Separation"
created: 2026-02-18
modified: 2026-02-19
summary: "Answer foundational questions about CLF monadic decomposition, loli firing, and engine layer separation"
tags: [research, CLF, loli, monad, theory]
type: research
status: researching
priority: 7
depends_on: []
required_by: [TODO_0041]
---

# CLF Theory Questions

Extracted from TODO_0001.Stage_3. Pure research — independent of the bug fix.

See [`doc/theory/exhaustive-forward-chaining.md`](../theory/exhaustive-forward-chaining.md) for the comprehensive analysis that addresses Q1-Q5 below.

## Q1: Why does CLF exclude lolis from the monad?

**Answered.** Three reasons, all confirmed by the CLF paper and Simmons' SLS thesis:

1. **Operational simplicity:** The monad's semantics require committed choice and atomic rule application. Lolis create "dormant rules" needing a firing mechanism (matching trigger, proving guard, scheduling) — this is a separate operational concern that CLF avoids.
2. **Monadic let suffices for sequencing:** `{A} tensor (A -o {B}) -o {B}` provides sequencing between forward steps at the *rule level* (between separate rules), making in-monad lolis redundant for sequencing.
3. **Metatheory:** Subject reduction and the concurrent definitional equality (which identifies computations differing only in order of independent steps) are simpler without dormant rules in state.

CALC violates this restriction deliberately — guarded continuations like `!eq(V,0) -o {stack SH 1}` express conditional production within a single rule's consequent, which monadic let cannot express.

## Q2: Why `!P -o {Q}` and not `!P -o Q`?

**Answered** (see TODO_0041 detailed analysis). The inner monad is syntactic, not semantic. After TODO_0041's fix (remove loli case from expandItem), both forms work identically. Recommendation: drop the inner monad braces after the fix.

## Q3: What IS `_tryFireLoli` theoretically?

**Answered.** It is the **loli-left rule** applied to facts in the linear state:

```
Delta, (A -o B), A |- C
------------------------  -oL (on state facts)
Delta, (A -o B) |- C
```

A `loli(trigger, body)` in `state.linear` is consumed along with its trigger `A`, producing body `B`. For persistent triggers (`!P`), "A is available" means "P is provable" (via backward chaining/FFI). This is a standard rule application — it should go through the same matching pipeline as compiled rules.

After TODO_0041, `_tryFireLoli` is deleted and this becomes part of the unified matching pipeline. The distinction between compiled rules (persistent `!(A -o {B})`) and loli continuations (linear `A -o B`) is just persistence — the matching mechanism is identical.

## Q4: Layer separation

**Partially answered.** The layers map to theory as follows:

| Layer | What | Theory vs Optimization |
|---|---|---|
| Multiset rewriting | Facts consumed/produced | Pure theory (ILL forward chaining) |
| Monadic decomposition (`expandItem`) | `{A}` → state updates | Theory (CLF monadic elimination) |
| Rule matching (`tryMatch`) | Find applicable rules | Theory (loli-left + bang elimination) |
| Strategy stack (fingerprint, disc-tree) | Index rules for fast lookup | **Optimization** (focused proof search compiled to indexing) |
| Mutation+undo | In-place state for DFS | **Optimization** (equivalent to copy-on-branch) |
| FFI bypass, compiled sub | Skip prove() machinery | **Optimization** (semantic equivalence to full backward proving) |

The strategy stack IS Andreoli focusing compiled into data structures (see theory doc Q4). Selectively disabling optimizations (fallback to linear scan, copy-on-branch) should yield identical results — this is a testable invariant.

## Q5: Is `expandItem` theoretically clean?

**Answered.** `expandItem` IS CLF's monadic decomposition — it's the elimination rule for `{A}`:

| Connective in `{C}` | Decomposition | CLF basis |
|---|---|---|
| atom | `{ linear: [atom] }` | Atom in state |
| `A tensor B` | cross product | tensor elimination |
| `!A` | `{ persistent: [A] }` | bang (persistent storage) |
| `1` | `{ }` | unit elimination |
| `A & B` / `A + B` | alternatives | additive case split |
| `A -o B` | **BUG** (was unsound) | Not in CLF (forbidden) |

If the loli case is removed, `expandItem` becomes exactly CLF's monadic decomposition — correct by construction. The remaining connective cases are all standard elimination rules.

Note: `plus` and `with` in `expandItem` go beyond CLF (which excludes additives from the monad). This is CALC's extension — justified by CHR-disjunction soundness results (Betz & Fruhwirth 2013).
