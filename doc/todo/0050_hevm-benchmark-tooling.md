---
title: hevm Benchmark Tooling
created: 2026-02-24
modified: 2026-02-24
summary: Track 1:1 hevm vs CALC benchmark comparison tooling and results
tags: [evm, benchmark, hevm, tooling]
type: tooling
status: in progress
priority: 5
cluster: Performance
depends_on: []
required_by: []
---

# hevm Benchmark Tooling

## Tooling

| Tool | Path | Purpose |
|------|------|---------|
| `tools/hevm-bench.sh` | Comparison runner | Runs hevm + CALC on same bytecode, reports median times |
| `tools/bytecode-to-ill.js` | Hex → .ill converter | Converts raw EVM hex to `code PC V` facts |
| `tools/symexec-inspect.js` | CALC tree inspector | Detailed leaf analysis for CALC symexec trees |

## Contracts Benchmarked

### 1. Multisig (no-call variant)

- **Bytecode**: `calculus/ill/programs/multisig_nocall.bin` (287 bytes)
- **CALC query**: `calculus/ill/programs/multisig_nocall.ill`
- **Modification**: CALL replaced with SSTORE(fired=1) + STOP
- **Opcodes used**: PUSH1, PUSH20, JUMP, JUMPDEST, CALLDATASIZE, CALLDATACOPY, GT, JUMPI, CALLDATALOAD, DUP1, DUP3, SLOAD, EXP, AND, OR, NOT, SWAP1, SSTORE, SHA3, LT, TIMESTAMP, SUB, CALLER, EQ, CALLVALUE, GASLIMIT, ISZERO, ADD, STOP, INVALID

**Results (2026-02-24):**

| Tool | Median | Notes |
|------|--------|-------|
| hevm 0.54.2 | ~44ms | Haskell + z3 solver |
| CALC (warm) | ~8ms | 124 nodes, 11 leaves, depth 60 |

**CALC is ~5x faster than hevm** on this 287-byte hand-crafted contract.

Caveats: hevm does full SMT solving (z3) for path feasibility; CALC uses FFI arithmetic. hevm supports the full EVM; CALC only supports non-memory opcodes. Single contract, hand-crafted bytecode — results may differ for solc-compiled code.

## Opcode Coverage

### Supported (in evm.ill)

STOP, ADD, MUL, SUB, DIV, MOD, EXP, LT, GT, EQ, ISZERO, AND, OR, NOT, SHL, SHR, SHA3, ADDRESS, BALANCE, CALLER, CALLVALUE, CALLDATALOAD, CALLDATASIZE, CALLDATACOPY, TIMESTAMP, GASLIMIT, POP, SLOAD, SSTORE, JUMP, JUMPI, GAS, JUMPDEST, PUSH0, PUSH1, PUSH2, PUSH4, PUSH20, PUSH32, DUP1, DUP2, DUP3, DUP4, DUP5, SWAP1, SWAP2, SWAP3, LOG4, CALL, RETURN, INVALID, REVERT

### Blocking Next Contracts

| Opcode | Needed for | Depends on |
|--------|-----------|------------|
| MLOAD (0x51) | All solc contracts | TODO_0049 (memory model) |
| MSTORE (0x52) | All solc contracts | TODO_0049 (memory model) |

## Next Targets

1. **Simple solc contract** — after memory model (TODO_0049)
2. **ERC20 token** — MLOAD/MSTORE + more stack ops
3. **K-framework comparison** — future
