---
title: "Calldata Representation"
created: 2026-04-09
modified: 2026-04-09
summary: Unified calldata model for concrete/symbolic EVM execution — sconcat chain, cd_read/cd_copy backward clauses, byte_join cross-boundary constructor
tags: [evm, calldata, forward-chaining, ffi, symbolic-execution]
---

# Calldata Representation

Calldata is a single linear resource `calldata D` where `D : bin` is either a ground binlit (concrete VMTests) or a structured `sconcat` chain (symbolic ABI layout). Reading is via backward predicate `cd_read`.

## Data Model

```
sconcat: bin -> bin -> bin -> bin.   % sconcat(Size, Value, Rest) — sized segment chain
epsilon: bin.                        % empty byte sequence (terminal)
byte_join: bin -> bin -> bin -> bin. % byte_join(N, Head, Tail) — cross-boundary value
```

**Concrete** (VMTests): `calldata 0xAABBCCDD` — single ground binlit. cd_read via FFI (O(1) byte extraction).

**Structured symbolic** (multisig ABI): `calldata sconcat(4, 0xcd68b367, sconcat(32, ?Deadline, sconcat(32, ?Amount, epsilon)))`. cd_read via backward clauses (structural traversal).

**Opaque symbolic**: `calldata ?X` — cd_read produces freshEvar with constraint.

## cd_read Clauses

```
cd_read/hit:   cd_read (sconcat 32 Val Rest) 0 Val.
cd_read/skip:  cd_read (sconcat SZ Val Rest) Offset Result  <- le SZ Offset <- sub ...
cd_read/cross: cd_read (sconcat SZ Val Rest) 0 (byte_join SZ Val TailVal)  <- lt SZ 32 <- ...
cd_read/nil:   cd_read epsilon Offset 0.
```

Cross-boundary reads produce `byte_join(N, Head, Tail)` — a stuck constructor decomposed by `shr/byte_join` when shift matches (e.g., SHR(224, byte_join(4, Selector, _)) = Selector).

## Forward Rules

All three calldata opcodes use `$calldata CD` (preserved sugar — consumed and re-produced):

- **CALLDATALOAD**: exists pattern — `exists Val. (... * !cd_read CD Offset Val)`
- **CALLDATASIZE**: reads from separate `$calldatasize Size` fact
- **CALLDATACOPY**: exists pattern — `exists MOut. (... * !cd_copy CD DataOffset End DestOffset M MOut)`. Replaces the old `calldatacopy_iter` loli pattern.

## FFI

`ffi/calldata.js` handles ground binlit only (mode `+ + -`, multiModal). Sconcat traversal is NOT duplicated in FFI — backward clauses are the single source of truth for structural navigation.

## Files

| File | Role |
|------|------|
| `calculus/ill/programs/evm.ill` | Declarations, forward rules, backward clauses |
| `lib/engine/ill/ffi/calldata.js` | cd_read FFI for ground binlit |
| `lib/engine/ill/residual-resolver.js` | Compile-time cd_read resolution |
| `tests/engine/calldata.test.js` | Unit tests (aligned, cross-boundary, preserved, symbolic) |

See TODO_0141 for full design rationale and coverage matrix.
