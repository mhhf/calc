---
title: "Forward Chaining Theory Cleanup: Loli Decomposition Bug"
created: 2026-02-17
modified: 2026-02-18
summary: "expandItem unsoundly decomposes loli continuations — transforms conditionals into unconditional assertions"
tags: [forward-engine, loli, soundness, CLF]
type: bug
status: planning
priority: 10
depends_on: []
required_by: [TODO_0002]
---

# Forward Chaining Theory Cleanup

## The Bug

`expandItem` in `compile.js:150-159` decomposes `!P -o {Q}` into `{ linear: [Q], persistent: [bang(P)] }`. This transforms a CONDITIONAL ("if P then Q") into an UNCONDITIONAL assertion ("Q and P"). Modus ponens applied without checking premise. Dead branches run with corrupted state. Exponential blowup: 263 -> 13109 nodes in multisig benchmark.

Existed before plus — old `evm/eq` with `&` had the same bug. Adding plus to iszero/jumpi amplified it from ~2 false branches to 2^N.

## Root Cause

`_tryFireLoli` only handles linear triggers (matching hashes against `state.linear`). A bang trigger (`!P`) would need to be PROVED (via FFI/backward chaining), but `_tryFireLoli` doesn't do this. So `expandItem` eagerly decomposes the loli to sidestep firing — and the sidestep is wrong.

## TODO_0001.Stage_1 — Fix loli continuation firing (correctness)

1. Remove `expandItem`'s loli decomposition (lines 150-159) — lolis become linear facts
2. Extend `_tryFireLoli` to handle bang triggers — prove inner predicate via FFI/backward chaining
3. When bang trigger proved: fire loli, consume it, produce body
4. When bang trigger fails: loli stays dormant, branch is stuck -> leaf
5. Test: both branches created, dead branch becomes stuck leaf (correct state, no corruption)

## TODO_0001.Stage_2 — Eager guard pruning (performance)

Prune dead branches at fork time: before creating a branch, check if its loli guard is decidable and false. Skip the branch entirely. This is Andreoli focusing — resolving synchronous choices eagerly when decidable.

## TODO_0001.Stage_3 — Theory cleanup

See [TODO_0027](0027_clf-theory-questions.md) — exported as standalone research task (Q1-Q5, layer separation, expandItem derivation).
