---
title: "Compiled Existential Chain — Partial Evaluation of Proof Search"
created: 2026-04-14
modified: 2026-04-14
summary: How existential-compile.js reduces ∃x.P(inputs, x) to x := f(inputs) for deterministic predicates via slot-to-slot dataflow.
tags: [optimization, partial-evaluation, existential, ffi, forward-chaining, implementation]
---

# Compiled Existential Chain

`lib/engine/opt/existential-compile.js` (166 LOC) compiles the existential goal sequence of a forward rule into direct slot-to-slot dataflow. For deterministic predicates (mode `+...+-`), existential resolution reduces from full SLD resolution to sequential function calls.

## Theory

For a predicate `P` with mode `+ + -` (first two args input, last output), resolving `∃x. P(a, b, x)` is equivalent to `x := f(a, b)` where `f` is the FFI function for `P`. This is partial evaluation of SLD resolution over a known goal sequence with known modes.

The compilation is sound because:
- Mode annotations guarantee exactly one output position
- FFI implements the same function as clause resolution
- On FFI failure, the caller falls back to full `provePersistent`

## Algorithm

`compileExistentialChain(rule, ffiContext)` runs once per rule at compile time:

1. **Collect goals** — gather existential goals from `rule.existentialSlots` and `rule.existentialGoals`, order by consequent-persistent position (mirrors `resolveExistentials` order)
2. **Per goal** — look up predicate, FFI handler, and mode annotations
3. **Map arguments** — for each arg position:
   - If child has a metavar slot → `argSlot[i] = slotIndex` (read from theta)
   - If input and ground → `argSlot[i] = -1`, `argMeta[i] = literal` (constant)
   - If output and no slot → skip (can't compile this goal)
4. **Build inputMask** — bitmask of which args are `+` mode (used for early-out when inputs unbound)
5. **Return chain** — array parallel to ordered goals, `null` entries for non-compilable goals

## Compiled Step Execution

`executeCompiledStep(step, theta, slots)` runs per goal per match attempt:

```
for each arg:
  if slot >= 0: read theta[slot] (deref metavar chains)
  if slot < 0:  use literal from argMeta
  if input and unbound: return false (early out)

result = handler(args)   // O(1) FFI call
if !result.success: return false

for each output binding:
  theta[outputSlot] = result.theta[k][1]
return true
```

Key: metavar chain dereferencing handles fused rules where `A→B→concrete` creates slot indirection.

## Interaction with Other Modules

- **evidence/hook mode** — bypassed when `onProveSuccess` or `onProveFail` hooks are set, or when `evidence` mode is active. The compiled fast path skips individual goal observation. `lnl/existential.js` checks: `!matchOpts.onProveSuccess && !matchOpts.onProveFail && !matchOpts.evidence`
- **FFI fallback** — per-step, not all-or-nothing. If step `i` fails, only that goal falls back to `provePersistent`. Other compiled steps still run.
- **Rule compilation** — chain is cached on `rule._existentialGoalOrder` to avoid Set+Array allocation per resolve call.

## Invariants

- **Deterministic only** — mode `+...+-` required. Non-deterministic predicates (all `+` or multiple `-`) are left as `null` in the chain.
- **Mode annotations required** — predicates without parsed modes are skipped.
- **FFI handler required** — predicates without FFI are skipped (compiled clause dispatch is separate, in `opt/compiled-clauses.js`).
- **Parallel to resolveExistentials** — ordering must match to ensure dependencies (goal A's output feeds goal B's input) are satisfied.

## Performance

The compiled chain eliminates per-goal overhead: no `subApplyIdx` (substitution traversal), no state lookup, no `tryFFIDirect` dispatch. For rules with 2-3 existential goals (typical EVM arithmetic), this saves ~3-5 function calls and ~2 hash lookups per goal.

## Key Files

| File | Role |
|---|---|
| `lib/engine/opt/existential-compile.js` | Compile-time chain builder + runtime step executor |
| `lib/engine/lnl/existential.js` | Caller — tries compiled steps, falls back to provePersistent |
| `lib/engine/compile.js` | Populates `rule.existentialSlots` and `rule.existentialGoals` |
| `lib/engine/opt/ffi.js` | FFI handler registry (shared with compiled steps) |
