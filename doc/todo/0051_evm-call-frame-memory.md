---
title: EVM CALL Frame Memory
created: 2026-02-26
modified: 2026-02-26
summary: Implement saved_mem/saved_memsize for CALL/RETURN/DELEGATECALL frame isolation
tags: [evm, memory-model, symexec, forward-chaining]
type: implementation
status: ready for implementation
priority: 5
cluster: Symexec
depends_on: [TODO_0049]
required_by: []
---

# EVM CALL Frame Memory

Extracted from TODO_0049.Stage_3.

## Problem

EVM CALL creates a fresh memory for the callee; RETURN restores the caller's memory. Without this, CALC cannot symbolically execute multi-contract interactions.

## Design

From TODO_0049:

```
saved_mem: bin -> type.
saved_memsize: bin -> type.

evm/call:
  ... mem M_caller * memsize S_caller ...
  -o { mem empty_mem * memsize 0 * saved_mem M_caller * saved_memsize S_caller * ... }.

evm/return:
  ... mem M_callee * memsize S_callee * saved_mem M_caller * saved_memsize S_caller ...
  -o { mem M_caller * memsize S_caller * ... }.
```

`saved_mem` and `saved_memsize` are linear facts consumed exactly once on RETURN. The caller's write-log is preserved as a content-addressed term in the Store.

## Scope

- Add `saved_mem`, `saved_memsize` type declarations to evm.ill
- Implement full CALL rule (currently simplified stub at evm.ill ~line 1194)
- Implement RETURN rule with memory restoration
- DELEGATECALL shares caller's memory (no save/restore)
- Tests: CALL then RETURN restores memory, nested CALL frames
