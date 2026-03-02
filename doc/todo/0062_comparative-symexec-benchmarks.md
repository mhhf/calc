---
title: "Comparative Symbolic Execution Benchmarks — eth-sc-comp + Tool Test Suites"
created: 2026-03-02
modified: 2026-03-02
summary: "Extend CALC's EVM coverage to pass the eth-sc-comp benchmark suite and test cases from hevm, halmos, and kontrol. Then run comparative benchmarks across all four tools."
tags:
  - evm
  - symexec
  - benchmarking
  - hevm
  - halmos
  - verification
  - tooling
type: design
status: planning
priority: 3
cluster: Performance
depends_on: []
required_by: []
---

# TODO 0062: Comparative Symbolic Execution Benchmarks

## Goal

Pass every test case we can extract from the symbolic execution ecosystem, then benchmark CALC against hevm, halmos, and kontrol on the standardized eth-sc-comp suite.

**Order**: correctness first, speed second. Each phase extends CALC's EVM opcode coverage to pass more tests. Benchmarks come only after all passable tests are green.

## Benchmark Sources

| Source | Repository | Test count | Format |
|---|---|---|---|
| eth-sc-comp | `eth-sc-comp/benchmarks` | ~165 functions across 28 contracts | Foundry ds-test (`prove_*`) + 1tx-abstract |
| hevm | `ethereum/hevm` test/contracts/ | ~60 tests across 39 contracts | Foundry ds-test |
| halmos | `a16z/halmos` tests/regression/ | ~70 contracts + ERC20/ERC721 examples | Foundry (`check_*`) |
| kontrol | `runtimeverification/kontrol` | ~71 contracts | Foundry (`test_*`/`prove_*`) |

The **eth-sc-comp** suite is the canonical cross-tool benchmark (used in hevm's CAV 2024 paper). The tool-specific suites contain additional edge cases.

## Current CALC EVM Coverage

### Implemented (64 opcodes)

Arithmetic: ADD, MUL, SUB, DIV, MOD, EXP. Comparison: LT, GT, SLT, EQ, ISZERO. Bitwise: AND, OR, NOT, SHL, SHR. Crypto: SHA3. Environment: ADDRESS, BALANCE, CALLER, CALLVALUE, CALLDATALOAD, CALLDATASIZE, CALLDATACOPY, TIMESTAMP, GASLIMIT. Memory: MLOAD, MSTORE, MSTORE8, POP, MSIZE. Storage: SLOAD, SSTORE. Flow: JUMP, JUMPI, GAS, JUMPDEST, PUSH0. Push: PUSH1-4, PUSH12, PUSH15, PUSH20, PUSH32. Stack: DUP1-8, SWAP1-5. Logging: LOG2-4. System: CALL, DELEGATECALL, STATICCALL, RETURN, REVERT, INVALID, STOP.

### Missing (by priority for benchmark coverage)

| Priority | Opcodes | Impact | Unlocks |
|---|---|---|---|
| **P0 — trivial** | PUSH5-11, PUSH13-14, PUSH16-19, PUSH21-31 | Missing PUSH widths block arbitrary solc output | All solc contracts |
| **P1 — stack** | DUP9-16, SWAP6-16 | Variable-heavy code generates these | All non-trivial solc contracts |
| **P2 — arithmetic** | SGT, SDIV, SMOD, SIGNEXTEND, ADDMOD, MULMOD | Signed arithmetic, modular ops | arith-safe/unsafe, bitwise tests |
| **P3 — bitwise** | XOR, SAR, BYTE | Bit manipulation, signed shift | bitwise-safe, xor-magic, byte-level packing |
| **P4 — logging** | LOG0, LOG1 | Event emission | ERC20, any contract with events |
| **P5 — return data** | RETURNDATASIZE, RETURNDATACOPY | External call result handling | Any contract making external calls |
| **P6 — code access** | CODECOPY, CODESIZE | Bytecode introspection | Constructor patterns, code-hash checks |
| **P7 — external** | EXTCODESIZE, EXTCODECOPY, EXTCODEHASH | Account/contract queries | Contract existence checks, proxy patterns |
| **P8 — creation** | CREATE, CREATE2 | Contract deployment | Foundry setUp, factory patterns, constructors.sol |
| **P9 — context** | CHAINID, SELFBALANCE, BASEFEE | Chain-specific logic | Conditional chain logic |
| **P10 — legacy** | CALLCODE | Deprecated calling convention | Legacy contract tests |
| **P11 — modern** | MCOPY | Memory copy (post-Cancun) | Optimized solc ≥0.8.24 output |

## Implementation Phases

### TODO_0062.Phase_0 — Test Harness + Currently Passable Tests

**Goal**: Set up the pipeline: solc → bytecode → .ill → CALC explore → pass/fail verdict.

**Infrastructure**:
1. `tools/compile-benchmark.sh` — compile a Solidity file with `forge build` or `solc --combined-json`, extract runtime bytecode, convert to `.ill` via `tools/bytecode-to-ill.js`
2. `tools/run-benchmark.sh` — run CALC symbolic execution on compiled `.ill`, output `result: safe|unsafe|unknown` (eth-sc-comp protocol)
3. `tests/benchmarks/` — test runner that compiles + runs each benchmark contract, compares against expected outcome

**Integration approach**: Bypass Foundry test runner entirely. For each `prove_*` function:
1. Compile contract to runtime bytecode
2. Convert to `.ill` code facts
3. Set up symbolic initial state: symbolic calldata matching the function ABI, symbolic msg.sender, concrete selector
4. Run `explore()` — if any leaf reaches INVALID/REVERT from an `assert` (Panic(1)), report `unsafe`; if all paths complete without assertion failure, report `safe`

**Detection**: Solidity 0.8.x `assert(cond)` compiles to `JUMPI` over `INVALID` (0xfe). An assertion violation is a path reaching 0xfe. A `require` uses `REVERT` — these are expected failures (not assertion violations).

**Currently passable** (with P0+P1 only — PUSH widths + stack ops):

| Contract | Functions | Notes |
|---|---|---|
| assert-true.sol | 1 | Trivial |
| assert-false.sol | 1 | Trivial |
| calldata-safe.sol | 3 | CALLDATALOAD, CALLDATASIZE only |
| calldata-unsafe.sol | 3 | Same |
| loops-safe.sol | 2 | Small/medium bounded loops (large/unbounded may timeout) |
| loops-unsafe.sol | 2 | Same bound caveat |
| synthetic-manybranch.sol | 1 | 2^10 paths, tests path explosion handling |

~13 functions passable immediately after P0+P1.

### TODO_0062.Phase_1 — PUSH + Stack Coverage (P0 + P1)

**Goal**: Support all PUSH/DUP/SWAP widths so arbitrary solc output works.

**Changes to evm.ill**:
- Add PUSH5-11, PUSH13-14, PUSH16-19, PUSH21-31 rules (mechanical: same pattern as existing PUSHn, different byte widths)
- Add DUP9-16 rules (mechanical: same pattern as DUP8 with deeper stack peek)
- Add SWAP6-16 rules (mechanical: same pattern as SWAP5 with deeper stack swap)

Each PUSHn rule is identical in structure — only the opcode byte differs. DUPn/SWAPn rules follow the same structural pattern as existing ones, operating on deeper stack positions.

**FFI**: None needed. These are pure stack/code operations.

**Estimated effort**: ~100 lines of `.ill` rules (boilerplate).

**Test**: Compile a contract that generates DUP9+ / SWAP6+ and verify it runs.

### TODO_0062.Phase_2 — Arithmetic + Bitwise (P2 + P3)

**Goal**: Pass arith-safe/unsafe and bitwise-safe from eth-sc-comp.

**New opcodes** (9 total):

| Opcode | Rule pattern | FFI needed? |
|---|---|---|
| SGT | Same as SLT but `>` on signed values | Yes — `sgt(a,b)` signed comparison |
| SDIV | Like DIV but signed (two's complement) | Yes — `sdiv(a,b)` |
| SMOD | Like MOD but signed | Yes — `smod(a,b)` |
| SIGNEXTEND | Extend sign bit from byte position | Yes — `signextend(b,x)` |
| ADDMOD | `(a + b) % N` without overflow | Yes — `addmod(a,b,N)` |
| MULMOD | `(a * b) % N` without overflow | Yes — `mulmod(a,b,N)` |
| XOR | Bitwise exclusive or | Yes — `xor(a,b)` |
| SAR | Arithmetic right shift (sign-extending) | Yes — `sar(shift,value)` |
| BYTE | Extract byte from 256-bit word | Yes — `byte_extract(i,x)` |

**FFI additions**: All 9 need BigInt FFI implementations in `lib/engine/ffi/arithmetic.js`. These are straightforward 256-bit operations.

**Backward clauses**: Each needs `.ill` clause definitions for soundness (pattern: same as `plus`, `neq`, `inc`).

**Unlocks**: ~77 additional test functions (arith-safe ~40, arith-unsafe ~13, bitwise-safe ~24).

### TODO_0062.Phase_3 — Memory + Storage Tests

**Goal**: Pass memory-safe/unsafe and storage-safe/unsafe from eth-sc-comp.

**No new opcodes needed** — MLOAD, MSTORE, SLOAD, SSTORE, SHA3 are already implemented.

**Potential issues**:
- Storage tests use Solidity mappings (slot = keccak256(key . slot_number)). CALC's SHA3 FFI must handle symbolic-length inputs. Need to verify.
- Memory tests use non-aligned MLOAD/MSTORE. CALC's memory model (write-log) should handle this if mem_read FFI supports arbitrary offsets.
- Packed storage (multiple values in one 256-bit slot) requires BYTE, SHL, SHR, AND masking — already implemented except BYTE (Phase 2).

**Dependencies**: Phase 2 (BYTE opcode for packed storage).

**Unlocks**: ~24 functions (memory-safe 8, memory-unsafe 8, storage-safe ~5, storage-unsafe ~3).

### TODO_0062.Phase_4 — Logging (P4)

**Goal**: Support LOG0 and LOG1 so contracts with events can execute.

**Changes to evm.ill**: Add `evm/log0` and `evm/log1` rules. Pattern follows LOG2-4 but with fewer topic arguments.

**Note**: For symbolic execution, events are side effects that don't affect control flow. The rule just needs to pop the right number of stack items and consume the memory range. No FFI needed.

**Unlocks**: Event-emitting contracts can now be analyzed (needed for ERC20 tests).

### TODO_0062.Phase_5 — Return Data + Code Access (P5 + P6)

**Goal**: Handle external call results and code introspection.

**New opcodes**:
- RETURNDATASIZE: push size of last external call's return data
- RETURNDATACOPY: copy return data to memory
- CODECOPY: copy running code to memory
- CODESIZE: push size of running code

**Design decision**: For symbolic execution, external calls (CALL/STATICCALL/DELEGATECALL) currently return symbolic results. RETURNDATASIZE/RETURNDATACOPY need to track the return buffer from the last call.

**Implementation**: Add a `returndata` state fact that tracks the last call's return buffer. RETURNDATASIZE reads its length; RETURNDATACOPY reads from it.

CODECOPY/CODESIZE need the contract bytecode available as a fact. Add a `codesize` persistent fact set during initialization.

**Unlocks**: Contracts that check call return values, ABI-decode external call results.

### TODO_0062.Phase_6 — External Account Queries (P7)

**Goal**: EXTCODESIZE, EXTCODECOPY, EXTCODEHASH.

**Design**: For symbolic execution, unknown external accounts have symbolic code. EXTCODESIZE returns a symbolic value (nonzero for known contracts, symbolic otherwise). EXTCODEHASH returns symbolic hash.

**Approach**: Conservative — return symbolic values that don't constrain exploration. This matches hevm's behavior with abstract accounts.

### TODO_0062.Phase_7 — Contract Creation (P8)

**Goal**: CREATE and CREATE2 support.

**This is the hardest phase.** Foundry-style tests use `setUp()` which deploys contracts via CREATE. Without CREATE support, we can't run the setUp function, which means we can't test contracts that depend on deployed state.

**Two approaches**:

**Option A — Full CREATE**: Execute creation bytecode, produce a new contract address, track its code/storage. Requires a multi-contract state model (currently CALC tracks one contract's state).

**Option B — Pre-deployed state**: For benchmark purposes, compile the contract, extract deployed bytecode, pre-populate the state with the contract's code and storage. Skip setUp entirely and directly invoke `prove_*` functions on the deployed bytecode. This works for contracts where setUp only deploys the contract under test (the common case).

**Recommendation**: Option B first. It covers ~80% of test cases. Option A is a separate TODO for multi-contract symbolic execution.

**Unlocks**: constructors.sol, erc20.sol, amm.sol, bad-vault.sol, withdraw.sol, and all Foundry-style tests with setUp.

### TODO_0062.Phase_8 — Comparative Benchmarks

**Goal**: Run CALC, hevm, halmos, and kontrol on the full eth-sc-comp suite. Report correctness + timing.

**Prerequisites**: Phases 0-7 complete. All passable tests green.

**Tooling**:
1. Fork `eth-sc-comp/benchmarks`
2. Add `tools/calc.sh` following the harness protocol:
   ```bash
   # Input: sol_file contract function sig ds_test timeout memout dump_smt
   # Output: result: safe|unsafe|unknown
   ```
3. Run `bench.py` with all four tools
4. Generate comparison tables and graphs

**Expected coverage**:

| Category | CALC | hevm | halmos | kontrol |
|---|---|---|---|---|
| Arithmetic (safe+unsafe) | Phase 2 | Yes | Yes | Yes |
| Bitwise | Phase 2 | Yes | Yes | Yes |
| Memory | Phase 3 | Yes | Yes | Yes |
| Storage | Phase 3 | Yes | Yes | Yes |
| Calldata | Phase 0 | Yes | Yes | Yes |
| Loops (bounded) | Phase 0 | Yes | Yes | Yes |
| Keccak | Phase 3 | Yes | Yes | Yes |
| ERC20 | Phase 7 | Yes | Yes | Yes |
| AMM | Phase 7 | Yes | Yes | Yes |
| Bad vault | Phase 7 | Yes | Yes | Yes |
| Path explosion | Phase 0 | Yes | Yes | Yes |
| Constructors | Phase 7 | Yes | Yes | Yes |
| Deposit | Unlikely | Yes | Partial | Yes |

**Metrics**:
- Correctness: safe/unsafe/unknown vs ground truth
- Wall-clock time (median of 10 runs)
- Peak memory
- Solved instances within timeout (25s default)

## Test Tracking

Each test case gets a status: `pass`, `fail`, `skip` (unsupported opcode), `timeout`.

Tests should be tracked in a structured format (JSON or test file) so progress is visible:

```
tests/benchmarks/eth-sc-comp/
├── safe/
│   ├── assert-true.test.js
│   ├── arith-safe.test.js      # Phase 2
│   ├── bitwise-safe.test.js    # Phase 2
│   ├── calldata-safe.test.js   # Phase 0
│   ├── memory-safe.test.js     # Phase 3
│   ├── storage-safe.test.js    # Phase 3
│   ├── loops-safe.test.js      # Phase 0
│   ├── keccak.test.js          # Phase 3
│   ├── erc20.test.js           # Phase 7
│   └── amm.test.js             # Phase 7
├── unsafe/
│   ├── assert-false.test.js
│   ├── arith-unsafe.test.js    # Phase 2
│   ├── ...
│   └── synthetic-manybranch.test.js  # Phase 0
└── status.json                 # Automated pass/fail/skip tracking
```

## Opcode Implementation Checklist

### Phase 1 (mechanical — boilerplate rules)

- [ ] PUSH5, PUSH6, PUSH7, PUSH8, PUSH9, PUSH10, PUSH11
- [ ] PUSH13, PUSH14, PUSH16, PUSH17, PUSH18, PUSH19
- [ ] PUSH21, PUSH22, PUSH23, PUSH24, PUSH25, PUSH26, PUSH27, PUSH28, PUSH29, PUSH30, PUSH31
- [ ] DUP9, DUP10, DUP11, DUP12, DUP13, DUP14, DUP15, DUP16
- [ ] SWAP6, SWAP7, SWAP8, SWAP9, SWAP10, SWAP11, SWAP12, SWAP13, SWAP14, SWAP15, SWAP16

### Phase 2 (new semantics — need FFI)

- [ ] XOR — `xor: bin -> bin -> bin -> type`
- [ ] SAR — `sar: bin -> bin -> bin -> type`
- [ ] BYTE — `byte: bin -> bin -> bin -> type`
- [ ] SGT — `sgt: bin -> bin -> bin -> type`
- [ ] SDIV — `sdiv: bin -> bin -> bin -> type`
- [ ] SMOD — `smod: bin -> bin -> bin -> type`
- [ ] SIGNEXTEND — `signextend: bin -> bin -> bin -> type`
- [ ] ADDMOD — `addmod: bin -> bin -> bin -> bin -> type`
- [ ] MULMOD — `mulmod: bin -> bin -> bin -> bin -> type`

### Phase 4 (logging — trivial rules)

- [ ] LOG0 — pop offset+size from stack
- [ ] LOG1 — pop offset+size+topic from stack

### Phase 5 (return data + code — need state model extension)

- [ ] RETURNDATASIZE
- [ ] RETURNDATACOPY
- [ ] CODECOPY
- [ ] CODESIZE

### Phase 7 (creation — major feature)

- [ ] CREATE (or pre-deployed workaround)
- [ ] CREATE2

## Dependencies

- Phase 0 depends on nothing (infrastructure only)
- Phase 1 depends on nothing (mechanical rules)
- Phase 2 depends on Phase 1 (contracts that use these opcodes also use DUP9+)
- Phase 3 depends on Phase 2 (packed storage needs BYTE)
- Phase 4 depends on nothing
- Phase 5 depends on Phase 4 (contracts with events often also check return data)
- Phase 6 depends on Phase 5
- Phase 7 depends on Phase 6
- Phase 8 (benchmarks) depends on all above

## Key Design Decisions

### Assert Detection

Solidity 0.8.x:
- `assert(cond)` → compiles to conditional JUMPI over INVALID (0xfe). Panic code 0x01.
- `require(cond)` → compiles to conditional JUMPI over REVERT.

For benchmark verdicts: a path reaching INVALID = assertion violation = `unsafe`. All paths STOP/RETURN/REVERT(require) = `safe`.

CALC already handles INVALID as a terminal leaf type. Need to distinguish INVALID (assertion failure) from REVERT (expected failure) in the verdict logic.

### Loop Bounds

eth-sc-comp has bounded loops (5, 100, 10K) and unbounded loops. CALC's `maxDepth` parameter bounds exploration. For bounded loops, set `maxDepth` high enough to unroll. For unbounded loops, report `unknown` (no loop invariant support).

hevm and halmos also bound loop iterations. kontrol uses K-framework loop invariants (more powerful but slower).

### Multi-Contract State

Several tests (bad-vault, amm, erc20) involve multiple interacting contracts. CALC currently tracks one contract's execution. Options:
1. Pre-deploy all contracts and track a global storage mapping (keyed by address)
2. Implement full CALL semantics with context switching

Option 1 is sufficient for the benchmark suite. Option 2 is a separate TODO for general multi-contract symbolic execution.
