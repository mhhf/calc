---
title: EVM CALL Frame Memory
created: 2026-02-26
modified: 2026-02-26
summary: Abstract CALL model (nondeterministic success/failure) done; full callee execution deferred to TODO_0053
tags: [evm, memory-model, symexec, forward-chaining]
type: implementation
status: done
priority: 5
cluster: Symexec
depends_on: []
required_by: [TODO_0053]
---

# EVM CALL Frame Memory

Extracted from TODO_0049.Stage_3.

## Stage A — Abstract CALL (DONE)

Nondeterministic success/failure model. CALL consumes 7 stack items + `mem M * memsize S`, produces `(stack SH 1 + stack SH 0)` oplus fork with memory preserved. Same pattern for DELEGATECALL (0xf4, 6 args) and STATICCALL (0xfa, 6 args).

- `evm.ill`: removed `call` type, replaced stub with abstract rule, added DELEGATECALL/STATICCALL
- Multisig benchmark: 246 nodes, 29 leaves, 4 STOP (was 210 nodes stuck at `call(...)`)
- Multisig no-call baseline unchanged: 124 nodes, 11 leaves, 2 STOP

## Stage B — Full Callee Execution

See [TODO_0053](0053_evm-call-frame-execution.md).
