---
title: "hevm -- Symbolic Execution for EVM Bytecode"
created: 2026-02-24
modified: 2026-02-24
summary: "hevm is a Haskell EVM implementation for symbolic execution, equivalence checking, and symbolic unit testing of smart contracts, using eager branch exploration and SMT solving"
tags: [ethereum, symbolic-execution, formal-verification, evm, hevm, smt, haskell]
category: "Symbolic Execution"
---

# RES_0060: hevm -- Symbolic Execution for EVM Bytecode

## What hevm Is

hevm is a Haskell implementation of the Ethereum Virtual Machine (EVM) built for **symbolic execution**, **equivalence checking**, and **symbolic unit testing** of smart contracts. Originally part of [dapptools](https://github.com/dapphub/dapptools), it was forked by the Ethereum Foundation's formal methods team in August 2022 and is now maintained at [github.com/ethereum/hevm](https://github.com/ethereum/hevm). Published at CAV 2024.

Unlike fuzz testing (random inputs), hevm explores **all possible execution paths** symbolically, either proving properties hold or producing concrete counterexamples.

## Installation

```bash
# Static binary (requires z3)
# Download from https://github.com/argotorg/hevm/releases

# Nix
nix profile install github:argotorg/hevm

# Dependencies
apt install z3          # or brew install z3
curl -L https://foundry.paradigm.xyz | bash && foundryup  # Foundry/solc
```

## Architecture

### Three-Layer Design

1. **EVM Semantics** (`EVM.hs`) -- Pure EVM execution. State in a `VM` record, single-step via `exec1` in `State VM a` monad. On external data need (RPC/SMT), halts with `VMFailure (Query _)`.

2. **Meta-Language** (`Stepper.hs`) -- Programs orchestrating multiple EVM steps. Decouples execution strategy from core semantics.

3. **Interpreters** -- Concrete (deterministic) or symbolic (all branches). Parameterized by a `Fetcher` for RPC and SMT queries.

### The Expr GADT

Core internal representation. `Expr a` where `a` is one of:

| Type | Represents |
|------|-----------|
| `End` | Final states (success, failure, partial) + branching (if-then-else tree) |
| `EWord` | 256-bit stack values (concrete or symbolic) |
| `Byte` | Single bytes |
| `Buf` | Byte arrays (calldata, memory, returndata) |
| `Storage` | Contract storage |
| `EAddr` | Addresses |
| `EContract` | Contract state |

An `Expr End` is a **tree**: if-then-else branches (from JUMPI) with final states as leaves. Each leaf carries **path conditions** (list of `Prop`).

### Prop Datatype

Assertions/path conditions: boolean connectives, polymorphic equality, comparison operators over EVM words.

### Eager Exploration Strategy

hevm uses **eager exploration**: it explores all branches **without** querying the SMT solver for reachability. Only after the full execution tree is built does it check postconditions against leaves, invoking the solver only for branches where violations could occur.

- Branches at `JUMPI`: clone VM state, explore both sides **in parallel** (Haskell async runtime)
- Each branch summarized into `Expr End`, retaining only externally observable effects
- Loop handling: after `--ask-smt-iterations N` iterations, solver checks loop branch reachability

This is faster than per-branch SMT queries in most cases.

## Three Modes of Operation

### 1. Symbolic Execution (`hevm symbolic`)

Checks whether any call can trigger an assertion violation (opcode `0xfe` or Solidity panic revert).

```bash
# From raw bytecode
hevm symbolic --code "608060405234..." --sig "myFunction(uint256)"

# With models (concrete counterexample inputs)
hevm symbolic --code "608060405234..." --sig "myFunction(uint256)" --get-models

# Show execution tree
hevm symbolic --code "608060405234..." --show-tree

# Storage modes
hevm symbolic --code "..." --initial-storage Empty      # all slots = 0
hevm symbolic --code "..." --initial-storage Abstract   # unconstrained (default)

# Solver config
hevm symbolic --code "..." --solver z3 --smttimeout 30000

# Custom assertion codes
hevm symbolic --code "..." --assertions '[0x01, 0x11]'
```

### 2. Equivalence Checking (`hevm equivalence`)

Proves two bytecodes behave identically for all inputs (same return values, same storage effects). Does NOT check gas, events, stack depth.

```bash
hevm equivalence \
  --code-a $(solc --bin-runtime "v1.sol" | tail -n1) \
  --code-b $(solc --bin-runtime "v2.sol" | tail -n1)

# From files
hevm equivalence --code-a-file a.bin --code-b-file b.bin

# Raw bytecode
hevm equivalence \
  --code-a "60003560000260005260016000f3" \
  --code-b "7f00...0060005260016000f3"

# With function signature filter
hevm equivalence --code-a "..." --code-b "..." --sig "transfer(address,uint256)"
```

### 3. Forge Test Integration (`hevm test`)

Symbolically executes Forge/Foundry test suites.

```bash
forge build --ast
hevm test --prefix test --solver z3
```

## Minimal Real-World Example

### Contract

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

contract MyContract {
    mapping(address => uint) balances;

    function my_adder(address recv, uint amt) public {
        if (balances[recv] + amt >= 100) { revert(); }
        balances[recv] += amt;
    }
}
```

### Compile

```bash
solc --bin-runtime contract.sol
# outputs runtime bytecode: 608060405234...
```

### Symbolically Execute

```bash
hevm symbolic \
  --sig "my_adder(address,uint256)" \
  --code "608060405234..."
```

### Output (no violations found)

```
QED: No reachable assertion violations
```

### Equivalence Check (buggy vs correct)

```bash
hevm equivalence \
  --code-a $(solc --bin-runtime "correct.sol" | tail -n1) \
  --code-b $(solc --bin-runtime "buggy.sol" | tail -n1)
```

Output when not equivalent:
```
Found 90 total pairs of endstates
Asking the SMT solver for 58 pairs
Not equivalent. The following inputs result in differing behaviours:
-----
Calldata:
  0xafc2c949000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000023
Storage:
  Addr SymAddr "entrypoint": [(0x0,0x10)]
Transaction Context:
  TxValue: 0x0
```

Output when equivalent:
```
Found 108 total pairs of endstates
Asking the SMT solver for 74 pairs
No discrepancies found
```

## Output Formats

### Counterexample (assertion violation)

```
Calldata:
  0xb1712ffd...
Storage:
  Addr SymAddr "entrypoint": [(0x0, 0x2)]
Transaction Context:
  TxValue: 0x0
```

### With `--get-models`

Returns example inputs for **each** ending state (success and failure), useful for automatic test case generation.

### With `--show-tree`

Prints the full execution tree with symbolic terms rendered with semantic information rather than opaque `<symbolic>`.

### Equivalence Discrepancy

Shows specific calldata, storage slot values, and transaction context that cause divergent behavior between the two bytecodes.

## Key Command-Line Flags

| Flag | Description |
|------|------------|
| `--code TEXT` | Runtime bytecode (hex) |
| `--code-file STRING` | Read bytecode from file |
| `--sig TEXT` | Function signature (e.g. `"transfer(address,uint256)"`) |
| `--arg STRING` | Concrete argument (supports `"<symbolic>"` placeholder) |
| `--calldata TEXT` | Concrete calldata (hex) |
| `--get-models` | Show concrete inputs for each end state |
| `--show-tree` | Print execution tree |
| `--initial-storage` | `Empty` (zero) or `Abstract` (unconstrained, default) |
| `--solver TEXT` | SMT solver: `z3`, `cvc5`, `bitwuzla` |
| `--num-solvers N` | Parallel solver instances |
| `--smttimeout N` | Solver timeout in milliseconds |
| `--ask-smt-iterations N` | Loop iterations before solver check |
| `--assertions LIST` | Which panic codes to check (default: `0x01` only) |
| `--prefix TEXT` | Test function prefix for `hevm test` |

## Performance

From CAV 2024 benchmarks (single transaction, Z3):

| Tool | Time |
|------|------|
| **hevm** | **0.08-0.1s** |
| Manticore | 1.6-2.2s |
| Mythril | 2.6-3.4s |

hevm's eager exploration (skip SMT during traversal) is the key performance advantage.

## Relevance to CALC

hevm's architecture shares structural similarities with CALC's forward engine:

- **Execution tree**: hevm produces `Expr End` trees (if-then-else branches, final-state leaves with path conditions). CALC's symexec produces exploration trees (rule-application branches, stuck/success leaves with linear context).
- **Eager exploration**: hevm explores all branches before checking postconditions. CALC's symexec does exhaustive DFS before analyzing leaves.
- **Counterexample generation**: hevm finds concrete inputs violating assertions. CALC could find concrete resource configurations that reach stuck states.
- **Equivalence checking**: hevm compares two bytecodes. CALC could compare two rule sets for behavioral equivalence.
- **Path conditions as propositions**: hevm accumulates `Prop` along paths. CALC accumulates linear context transformations.
