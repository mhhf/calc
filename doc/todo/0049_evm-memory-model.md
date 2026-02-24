---
title: EVM Memory Model Design
created: 2026-02-24
modified: 2026-02-24
summary: Design MLOAD/MSTORE memory model for CALC's EVM symbolic executor
tags: [evm, memory, architecture]
type: design
status: planning
priority: 6
cluster: Symexec
depends_on: []
required_by: []
---

# EVM Memory Model Design

## Current State

CALC uses `memory Pos Size V` facts (consumed by SHA3/CALLDATACOPY only). No MLOAD/MSTORE support — blocks all solc-compiled bytecode.

## Why It Matters

Every solc-compiled contract uses MLOAD/MSTORE extensively (ABI encoding, scratch space, free memory pointer at 0x40). Without memory support, CALC can only run hand-crafted bytecode.

## Design Space

### Option A: Skolemization

Single `mem M` resource with nested `(mstore M offset val)` terms. MLOAD uses FFI to simplify/lookup. Changes Store architecture fundamentally — terms become functional, not just content-addressed atoms.

### Option B: Generation Counters

`memory OFFSET GEN V` with monotonic generation counter. MSTORE increments gen. MLOAD reads highest gen for offset. Requires ordering/max over persistent facts.

### Option C: Two-Rule MSTORE

`mstore_new` (no existing entry) + `mstore_update` (overwrite). Problem: symexec branches on both rules at every MSTORE — exponential blowup.

### Option D: Persistent Map with Shadow Writes

Single `memstate` persistent fact + FFI for read/write. Keeps memory outside linear logic entirely. Fast but loses symbolic reasoning about memory contents.

### Option E: hevm Approach

hevm uses a Haskell `Expr` GADT with symbolic `WriteWord`/`ReadWord` nodes. Memory is a tree of writes; reads search backward through writes. Closest analog in CALC: nested terms (Option A).

## Impact Analysis

| Component | Impact |
|-----------|--------|
| Forward engine matching | New patterns for mem facts |
| Store representation | Possibly nested function terms |
| FFI | Memory read/write operations |
| Symexec branching | Must avoid spurious MSTORE branches |

## Decision

TBD — requires prototyping. Start with Option B (generation counters) as simplest to implement, fall back to Option A if branching is unacceptable.
