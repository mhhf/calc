---
title: hevm Benchmark Tooling
created: 2026-02-24
modified: 2026-03-02
summary: Track 1:1 hevm vs CALC benchmark comparison tooling and results
tags: [evm, benchmark, hevm, tooling]
type: tooling
status: done
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

### 1. MultisigNoCall (solc 0.8.28, 1040 bytes)

- **Bytecode**: `calculus/ill/programs/multisig_nocall_solc.bin` (1040 bytes runtime)
- **CALC query**: `calculus/ill/programs/multisig_nocall_solc_symbolic.ill`
- **Function**: `confirmAndCheck(uint256,uint256,bytes32)`
- **Setup**: symbolic sender, symbolic calldata args, symbolic nonce

**Results (2026-03-02, 10-run median):**

| Tool | Median | Notes |
|------|--------|-------|
| hevm 0.54.2 + z3 4.15.1 | 41ms | Process wall-clock |
| CALC (explore, structural memo) | 7ms | 477 nodes, 11 leaves |
| CALC (end-to-end) | 9ms | load + explore |

**CALC is ~4.6x faster than hevm** on solc-compiled multisig with symbolic execution.

See [calc-vs-hevm.md](../documentation/calc-vs-hevm.md) for full analysis.

## Next Targets

1. **ERC20 token** — MLOAD/MSTORE + more stack ops
2. **K-framework comparison** — future
