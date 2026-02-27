---
tags:
  - evm
  - hevm
  - symexec
  - symbolic-execution
  - benchmarking
  - smt
  - verification
---

# calc vs hevm: Symbolic Execution Comparison

Comparing symbolic execution of `MultisigNoCall.sol` (solc 0.8.28, 1040 bytes).
Both tools explore the same contract with symbolic sender + symbolic calldata arguments.

## Setup

| Dimension | calc | hevm |
|---|---|---|
| **Sender** | Symbolic (`Sender` freevar) | Symbolic (`SymAddr "caller"`) |
| **Calldata args** | Symbolic (Deadline, CallValue, DataHash) | Symbolic (arg1, arg2, arg3) |
| **Storage** | Symbolic nonce (`Nonce` freevar), `fired=0` | AbstractStore (fully symbolic) |
| **Selector** | Concrete (0xcd68b367) | Concrete (via `--sig`) |
| **Timestamp** | Symbolic (`Time` freevar) | Concrete (0) |
| **Arithmetic** | FFI (ground) + existential variables (symbolic) | Symbolic expressions + SMT (z3) |

## Results (2026-02-27, verified)

| Metric | calc | calc (structural memo) | hevm (--sig) |
|---|---|---|---|
| **Time (warm)** | 57ms | 22ms | 52ms |
| **Branch nodes** | 30 oplus | 30 oplus | 30 ITE |
| **Leaves** | 31 (18 STOP + 13 REVERT) | 11 (2 real + 9 memo) | 31 (18 Success + 13 Failure) |
| **Total nodes** | 2125 | 477 | 61 |
| **Behavioral outcomes** | 5 (×6 per member + 6 overflow) | 5 | 5 (×6 per member + 6 overflow) |

Verified with hevm v0.54.2 `hevm symbolic --show-tree`.

Both tools discover identical behavioral outcomes with identical leaf counts:

| Outcome | calc leaves | hevm leaves | Description |
|---|---|---|---|
| NON-MEMBER | 1 REVERT | 1 Failure | `getMemberBit` fails all 6 checks |
| ALREADY-VOTED | 6 STOP | 6 Success | `nonce & voteBit != 0`, early return |
| VOTED | 6 STOP | 6 Success | Vote recorded, counter < threshold |
| FIRED | 6 STOP | 6 Success | Threshold reached, deadline OK |
| DEADLINE-PASSED | 6 REVERT | 6 Failure | `require(timestamp <= deadline)` |
| OVERFLOW | 6 REVERT | 6 Failure | Checked arithmetic on symbolic counter |

**Neither tool merges per-member subtrees.** Both produce 6 copies of the vote subtree (one per member). hevm represents each copy compactly (4 ITE nodes); calc represents each copy as ~50 explicit opcode steps. calc's structural memo skips 5 of 6 copies entirely.

## Why the node count differs (2125 vs 61)

The 34× difference in total nodes is about **representation granularity**, not exploration behavior:

**hevm (61 nodes):** Each ITE node represents one behavioral decision (JUMPI that affects control flow). The 50+ EVM opcodes between JUMPIs are executed internally and their results captured in symbolic expressions. A `Success` leaf contains the final storage/log state as a symbolic expression tree — the intermediate steps are implicit.

**calc (2125 nodes):** Each EVM opcode is a forward rule application, producing one explicit tree node. MSTORE, SHA3, SLOAD, SSTORE, etc. are all visible in the tree. This gives full observability but inflates node count.

Both tools execute the same opcodes. hevm compresses the representation; calc makes every step explicit.

## Architectural Differences

### Value representation

**calc** uses content-addressed hashes (ground integers). When an EVM operation like `AND(Nonce, VoteBit)` can't be computed (because `Nonce` is symbolic), the forward rule produces a **fresh existential variable** as the result. Subsequent operations propagate this evar through the computation, branching at every `EQ`/`ISZERO`/`JUMPI`.

**hevm** uses symbolic expression trees. `AND(Nonce, VoteBit)` produces an `And(nonce, voteBit)` expression node. This expression propagates lazily — hevm only branches at `JUMPI` when the condition determines different control flow.

### Branching strategy

Both tools branch at the same 30 points. The getMemberBit function produces 6 member-check branches (EQ) plus additional vote-logic branches (ISZERO/JUMPI) per member path.

**calc (eager):** branches at every oplus (EQ/ISZERO/JUMPI result). Each member path carries its own concrete `bitPos` value (247, 246, ..., 242). The constraint solver prunes impossible alternatives, collapsing many 2-way branches to 1-way.

**hevm (lazy):** branches at every JUMPI. hevm's forward-jump merge (`Merge.hs`) speculatively executes the fall-through path of each JUMPI, merging stack values using ITE expressions when possible. This reduces intermediate nodes but does NOT reduce the number of behavioral branches.

### Constraint solving

**calc**: union-find EqNeqSolver for `eq`/`neq` constraints. Prunes branches where ground values contradict (e.g., `!eq 0 1`). Cannot reason about arithmetic bounds (e.g., `AND(x, 0xFF) + 1 < 2^256`).

**hevm**: z3 SMT solver. Can prove arithmetic properties. However, hevm does NOT prune the overflow branches in the multisig — it produces 6 overflow Failure leaves, same as calc.

### False positives

Both tools produce the same 6 overflow REVERT/Failure leaves from solc 0.8's checked arithmetic on `(nonce & 0xFF) + 1`. In calc, the `AND` result is an evar (unknown). In hevm, it's a symbolic `And` expression. Neither tool can prove the result fits in uint256 without more sophisticated reasoning.

## How calc handles symbolic values

calc's "implicit symbolic execution" works through three mechanisms:

1. **Existential variables in consequents**: When a forward rule like `evm/and` produces `!and X Y Z` with Z free, Z becomes an existential variable (evar) in the state. The AND result is unknown but tracked.

2. **Tensor-in-oplus branching**: When `evm/iszero` produces `(!eq V 0 * stack SH 1) + (!neq V 0 * stack SH 0)` where V is an evar, both alternatives are explored — the solver can't determine which is true.

3. **Constraint accumulation**: The EqNeqSolver tracks `!eq`/`!neq` constraints along each path. When a later branch contradicts an earlier constraint (e.g., `!eq X 0` then `!neq X 0`), the branch is pruned.

This gives calc a form of symbolic execution without an SMT solver — at the cost of per-member path enumeration and some false positives where arithmetic bounds can't be verified.

## Performance comparison across setups

| Setup | calc nodes | calc leaves | calc time | hevm time |
|---|---|---|---|---|
| Concrete sender, nonce=0 | 280 | 1 (STOP) | 3.9ms | — |
| Symbolic sender, nonce=0 | 1333 | 7 (6 STOP + 1 REVERT) | 22ms | — |
| Symbolic sender + nonce | 2125 | 31 (18 STOP + 13 REVERT) | 57ms | 52ms |
| Symbolic + structural memo | 477 | 2 + 9 memo | **22ms** | 52ms |

## Structural memoization

calc's `structuralMemo` option detects structurally isomorphic subtrees using a control hash based on `(PC, SH)`. In the multisig, the 6 member paths through `getMemberBit` produce identical subtrees (same opcodes, same branch pattern) — only concrete values differ. Structural memo explores the first member body and skips the remaining 5.

**Reduction**: 2125 → 477 nodes, 57ms → 22ms. calc is **2.4× faster** than hevm with structural memo enabled.

**Soundness**: The control hash is sound when branching depends only on symbolic values (evars/freevars), not on concrete argument values excluded from the hash. This holds for the multisig case (all body branching is on symbolic AND/ISZERO results). The option is opt-in for programs where this assumption may not hold.

## hevm tree structure (verified)

```
ITE [caller == M6?]
├─ true: vote subtree (4 ITE + 5 leaves)
│  ITE [already voted?]
│  ├─ true:  Success (early return)
│  └─ false: ITE [counter >= threshold?]
│     ├─ true:  ITE [overflow check]
│     │  ├─ ok:   Success (voted)
│     │  └─ overflow: ITE [timestamp <= deadline?]
│     │     ├─ true:  Success (fired)
│     │     └─ false: Failure (deadline passed)
│     └─ false: Failure (counter overflow)
└─ false: ITE [caller == M5?]
   ├─ true: vote subtree (identical structure)
   └─ false: ITE [caller == M4?]
      ├─ true: vote subtree (identical structure)
      └─ false: ITE [caller == M3?]
         ├─ true: vote subtree (identical structure)
         └─ false: ITE [caller == M2?]
            ├─ true: vote subtree (identical structure)
            └─ false: ITE [caller == M1?]
               ├─ true: vote subtree (identical structure)
               └─ false: Failure (Not a member)
```

6 member-check ITEs + 6 × 4 vote ITEs = 30 ITE. 6 × 5 leaves + 1 = 31 leaves. Total: 61 nodes.

## Key insights

1. **Same behavioral outcomes**: Both tools discover identical results — 30 branches, 31 leaves, 5 outcome types × 6 members + 1 non-member. Neither tool merges per-member subtrees.

2. **calc is faster**: With structural memo, calc (22ms) is 2.4× faster than hevm (52ms), despite calc using no external solver.

3. **Node count difference is representation**: hevm's 61 nodes vs calc's 477 (with memo) reflects representation granularity, not exploration efficiency. hevm compresses 50 opcodes into one ITE node; calc makes each opcode explicit.

4. **Structural memo is unique to calc**: calc's `(PC, SH)` control hash detects isomorphic member subtrees and skips 5 of 6. hevm has no equivalent — it fully explores all 6 member vote subtrees (producing 6 × 9 = 54 nodes). This is why calc has fewer leaves (11 vs 31).

5. **No solver dependency**: calc requires no external tools. hevm requires z3 (or cvc5). This makes calc more portable and predictable (no SMT timeout variance).
