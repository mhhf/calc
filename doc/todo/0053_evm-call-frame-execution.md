---
title: EVM CALL Frame Execution
created: 2026-02-26
modified: 2026-02-26
summary: Full callee execution with engine-level frame stack for CALL/DELEGATECALL/STATICCALL
tags: [evm, memory-model, symexec, forward-chaining]
type: implementation
status: planning
priority: 4
cluster: Symexec
depends_on: [TODO_0051]
required_by: []
---

# EVM CALL Frame Execution

## Problem

Stage A (TODO_0051) models CALL as nondeterministic success/failure. To actually execute callee code, the engine must isolate caller and callee state: separate code, pc, stack, memory, and other context.

## Code-Interference Problem

Caller's ~170 `code` facts must not interfere with callee's `code` facts. Both sit in `state.linear` simultaneously and both match via the fingerprint strategy.

The loli pattern (SHA3/CALLDATACOPY) doesn't work here because:
- Consuming caller's code facts requires a loop (~170 iterations)
- The loop marker competes with the loli trigger
- Symexec would fork between "save next code fact" and "fire loli prematurely"

## Design: Engine-Level Frame Stack

On CALL, the engine atomically saves caller context into a frame, removes it from state, and loads callee context. On RETURN, pops frame and restores. Analogous to FFI — operational infrastructure, not logical semantics.

### Frame contents

`pc`, `code`, `stack`, `sh`, `mem`, `memsize`, `gas`, `address`, `sender`, `callvalue`, `calldata`, `calldatasize`, `storage` (for non-DELEGATECALL).

### CALL vs DELEGATECALL vs STATICCALL

| Field | CALL | DELEGATECALL | STATICCALL |
|-------|------|-------------|------------|
| code | callee | callee | callee |
| storage | callee (fresh) | caller (shared) | callee (read-only) |
| address | callee | caller | callee |
| sender | caller | caller's sender | caller |
| memory | fresh | fresh | fresh |

### RETURN/REVERT

- RETURN: pop frame, restore caller state, push 1
- REVERT: pop frame, restore caller state, discard callee storage changes, push 0

### Callee code loading

New directive `#code(addr, file)` or callee bytecode embedded in state.

### Symexec integration

Frame stack in `symexec.js` mutation/undo: push frame on CALL, pop on RETURN/REVERT.

## Scope

~300 LOC across engine + rules + tests.
