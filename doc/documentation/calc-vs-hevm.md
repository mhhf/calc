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

## Results (2026-02-27)

| Metric | calc | hevm (--sig) |
|---|---|---|
| **Time (warm)** | 47.5ms | ~50ms |
| **Nodes** | 2125 | 7 (symbolic ITE tree) |
| **Leaves** | 31 | 4 (3 Success + 1 Failure) |
| **Behavioral outcomes** | 5 (×6 per member + 6 false positives) | 5 (merged) |

Both discover the same 5 behavioral outcomes:

| Outcome | calc | hevm | Description |
|---|---|---|---|
| NON-MEMBER | 1 leaf (REVERT) | 1 Failure | `getMemberBit` fails all 6 checks |
| ALREADY-VOTED | 6 leaves (STOP) | merged into 1 Success | `nonce & voteBit != 0`, early return |
| VOTED | 6 leaves (STOP) | merged into 1 Success | Vote recorded, counter < threshold |
| FIRED | 6 leaves (STOP) | merged into 1 Success | Threshold reached, deadline OK |
| DEADLINE-PASSED | 6 leaves (REVERT) | merged into 1 Failure | `require(timestamp <= deadline)` |
| *Overflow (false positive)* | *6 leaves (REVERT)* | *pruned by SMT* | Checked arithmetic on symbolic counter |

## Architectural Differences

### Value representation

**calc** uses content-addressed hashes (ground integers). When an EVM operation like `AND(Nonce, VoteBit)` can't be computed (because `Nonce` is symbolic), the forward rule produces a **fresh existential variable** as the result. Subsequent operations propagate this evar through the computation, branching at every `EQ`/`ISZERO`/`JUMPI`.

**hevm** uses symbolic expression trees. `AND(Nonce, VoteBit)` produces an `And(nonce, voteBit)` expression node. This expression propagates lazily — hevm only branches at `JUMPI` when the condition determines different control flow.

### Branching strategy

**calc (eager)**: branches at every oplus (EQ/ISZERO/JUMPI result). For `getMemberBit`, this creates 7 paths (6 members + 1 revert). Each member path carries its own concrete `bitPos` value (247, 246, ..., 242).

**hevm (lazy)**: branches only at behavioral divergence points. The 6 `getMemberBit` checks become a single symbolic expression `ITE(EQ(caller, M1), 247, ITE(EQ(caller, M2), 246, ...))`. hevm branches at 3 points: (1) already voted? (2) threshold reached? (3) deadline valid?

### Constraint solving

**calc**: union-find EqNeqSolver for `eq`/`neq` constraints. Prunes branches where ground values contradict (e.g., `!eq 0 1`). Cannot reason about arithmetic bounds (e.g., `AND(x, 0xFF) + 1 < 2^256`).

**hevm**: z3 SMT solver. Can prove arithmetic properties, eliminating false-positive branches like overflow checks on bounded values.

### False positives

calc produces 6 false-positive REVERT leaves from solc 0.8's checked arithmetic overflow on `(nonce & 0xFF) + 1`. Since `nonce & 0xFF` produces an existential variable, calc cannot prove the result fits in uint256. hevm's SMT solver proves the bound and eliminates these paths.

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
| Symbolic sender + nonce | 2125 | 31 (18 STOP + 13 REVERT) | 47.5ms | ~50ms |

## Key insights

1. **Comparable performance**: calc matches hevm's speed (~50ms) on the same symbolic workload despite exploring 300× more tree nodes, because pattern matching + FFI arithmetic is cheaper per-node than SMT queries.

2. **Different tree semantics**: calc produces an explicit enumeration (31 leaves), hevm produces a compact symbolic tree (7 nodes). Both discover the same 5 behavioral outcomes.

3. **SMT advantage**: hevm can prune 6 false-positive overflow branches that calc cannot, thanks to z3's arithmetic reasoning. For deeper contracts with more checked arithmetic, this gap would widen.

4. **Merging gap**: hevm's lazy symbolic expressions merge the 6 member paths into 1. calc enumerates them separately. Post-hoc subtree equivalence detection could close this presentation gap without architecture changes.

5. **No solver dependency**: calc requires no external tools. hevm requires z3 (or cvc5). This makes calc more portable and predictable (no SMT timeout variance).
