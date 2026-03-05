---
title: "Proof Certificates for Forward Execution"
created: 2026-03-04
modified: 2026-03-05
summary: "Make forward execution produce ILL proof trees where every leaf is an axiom. Each forward step becomes a ⊸L node, each persistent goal a backward proof subtree from clauses, rightFocus a succedent decomposition tree. Closes the monad_r trust gap."
tags: [proof-certificates, kernel, verification, soundness, forward-chaining, architecture, proof-theory, de-bruijn, focusing]
type: implementation
cluster: Theory
status: planning
priority: 3
depends_on: [TODO_0068]
required_by: [TODO_0045, TODO_0008]
subsumed_by: TODO_0068
starred: false
---

# Proof Certificates for Forward Execution

## 1. Core Principle

**A proof certificate IS a proof tree where every leaf is an axiom.**

There is no "evidence format" or "method tags." The forward engine produces a genuine ILL proof tree. The L1 kernel checks it with `verifyTree`. If any step can't produce a proper proof tree ending in axioms, it's a hole — not a certificate.

**What this means concretely:**
- A forward rule application = a `⊸L` (loli-left) node in the proof tree
- A persistent antecedent proof = a backward proof subtree from clauses (leaves = axioms)
- rightFocus succedent decomposition = `tensor_r`, `one_r`, `bang_r`, `id` nodes
- A loli-drain = just another `loli_l` application (not special)
- FFI = optimization for proof search speed only. NOT part of the certificate. When certificates are enabled, persistent goals are proved by clause resolution, producing real proof trees.

---

## 2. Problem Statement

CALC has two execution modes with different trust levels:

| Mode | Verifier | Trust boundary |
|------|----------|----------------|
| Backward (L3 prover) | `kernel.js:verifyStep` + `verifyTree` | ~205 LOC kernel. Every step machine-checked. |
| Forward (engine) | **None** | ~1500 LOC engine is fully trusted. |

When `monad_r` fires, the backward prover delegates to the forward engine. The kernel currently returns:

```javascript
// kernel.js:84-90
return { valid: true, unverified: 'modeSwitch', evidence: null };
```

This is an explicit trust gap. The forward engine could have bugs in `explore()`, `findAllMatches()`, `tryMatch()`, `mutateState()`, the strategy stack, preserved-skip, compiled substitution, or constraint solving — none of it is kernel-checked.

**Goal:** Make the forward engine emit **proof trees** — genuine ILL derivations where every leaf is an axiom — so the L1 kernel can independently verify every forward step.

### 2.1 Design Constraints

**Zero overhead when off.** Certificate generation is opt-in. The normal execution path must have **no branches, no allocations, no function call overhead** from certificate code. Mechanism: **function pointer swap at entry** — not `if (certificates)` scattered in hot loops. The caller selects variant functions before entering the main loop:

```javascript
// At explore/forward entry:
const proveGoals = opts.certificates ? provePersistentWithCerts : provePersistentWithFFI;
const proveBackward = opts.certificates ? proveWithCert : prove;
```

V8 sees one monomorphic call site per loop — zero branch prediction cost, zero deopt risk.

**Zig-friendly.** Certificate nodes are flat structs with interned tag IDs — no closures, no GC pointers, no recursive JS objects in the hot representation. The certificate builder (JS, untrusted) constructs an arena of flat nodes. The verifier (trusted) works on this flat representation. Binary serialization extends the existing `store-binary.js` SoA pattern — a certificate is a contiguous byte buffer that can be memory-mapped and verified without any JS runtime.

```
CertNode { kind: u8, rule: u16, numChildren: u8, childStart: u32, termIdx: u32 }
```

The JS-object notation in §5 is the logical structure; the physical layout is a flat `CertNode[]` arena with a parallel `Term[]` arena for expanded terms.

**Separation of concerns.** Existing modules (`prove.js`, `match.js`, `explore.js`, `forward.js`) are NOT modified with certificate logic. Instead:

| Module | Role | Trust |
|--------|------|-------|
| `lib/engine/certificate.js` | Builder: takes match results → cert nodes, term expansion | Untrusted |
| `lib/prover/verify-forward.js` | Checker: verifies cert trees structurally | **Trusted** (~150 LOC) |
| `lib/engine/prove.js` | New export `proveWithCert()` wrapping existing `search()` | Untrusted |
| `lib/engine/opt/cert-proving.js` | `provePersistentWithCerts` (builds on existing `provePersistentNaive`) | Untrusted |

Existing hot-path functions stay untouched. Certificate variants are separate functions in separate files, selected by function pointer at entry.

**Leveraging existing code.** `provePersistentNaive` (match.js:213) already does state lookup → clause resolution without FFI. Certificate mode builds on this — adding proof tree collection. `prove.js` already has `useFFI` flag (line 146) — passing `useFFI: false` gives clause-only proving. Only proof tree return needs adding.

---

## 3. Theoretical Foundations

### 3.1 The De Bruijn Criterion

Proof *generation* and proof *checking* must be independent. The prover can be arbitrarily complex; a small, independent checker validates its output. Only the checker is trusted.

Systems satisfying this:
- **Metamath Zero** — ~250 LOC verifier
- **HOL Light** — ~400 LOC OCaml kernel
- **Coq** — CIC type checker kernel

CALC's backward prover already follows this (L1 kernel = checker, L2-L4 = untrusted search). The forward engine breaks it.

### 3.2 ILL Proof Tree for a Forward Step

A forward rule `r : A₁ ⊗ A₂ ⊗ !P ⊸ {B₁ ⊗ B₂}` applied to state `A₁, A₂, !P` produces the following ILL derivation via `⊸L`:

```
                                          Γ, B₁, B₂ |- Goal
────── id   ────── id                     ─────────────────── ⊗L
A₁ |- A₁    A₂ |- A₂                     Γ, B₁ ⊗ B₂ |- Goal
──────────────────── ⊗R   ────── id       ──────────────────── monad_l
 A₁, A₂ |- A₁ ⊗ A₂       !P |- !P       Γ, {B₁ ⊗ B₂} |- Goal
 ──────────────────────────────── ⊗R       ────────────────────
   A₁, A₂, !P |- A₁ ⊗ A₂ ⊗ !P            (continuation)
   ──────────────────────────────────────────────────────────── ⊸L
      A₁, A₂, !P, Γ, (A₁ ⊗ A₂ ⊗ !P ⊸ {B₁ ⊗ B₂}) |- Goal
```

Key structure:
- **Left premise of ⊸L**: proves the antecedent by tensoring consumed facts (each an identity axiom)
- **Right premise of ⊸L**: continuation with the body `{B₁ ⊗ B₂}` in context
- **monad_l**: unpacks `{B₁ ⊗ B₂}` into `B₁ ⊗ B₂` in the linear context
- **⊗L**: splits tensor into individual facts (new state)

### 3.3 Composition of Multiple Steps

Multiple forward steps compose as nested `⊸L + monad_l` applications — corresponding to CLF monadic let-bindings:

```
let {b₁ ⊗ b₂} = r₁ a₁ a₂ in     -- step 1: ⊸L + monad_l
let {c}        = r₂ b₁ b₃ in     -- step 2: ⊸L + monad_l
  c ⊗ b₂                          -- final state
```

Each `let` corresponds to a `⊸L` application followed by `monad_l` to unpack the body.

### 3.4 Persistent Antecedents = Backward Proof Subtrees

When a forward rule has a persistent antecedent `!P`, the proof must include a **backward proof subtree** deriving `P` from clauses. For example, `!plus(3, 5, 8)` with clauses `plus/z` and `plus/s`:

```
plus/s [plus(3, 5, 8)]
  └── plus/s [plus(2, 5, 7)]
      └── plus/s [plus(1, 5, 6)]
          └── plus/z [plus(0, 5, 5)]  ← axiom (no premises)
```

**FFI is NOT part of the certificate.** FFI (`arithmetic.js`, `memory.js`) is an optimization that speeds up proof search. The certificate must contain the real backward proof from clauses. When certificates are enabled, `provePersistentGoals` bypasses FFI and uses clause resolution only, which produces proof trees.

For persistent goals proved via **state lookup** (fact already in `state.persistent`): the proof is an identity axiom — the fact exists.

### 3.5 Loli Steps = Normal ⊸L Applications

A loli `!P ⊸ {Q}` in the state is just a linear implication. Firing it is a normal `loli_l` proof step:

```
                    Γ, Q |- Goal
────── id           ──────────── monad_l
!P |- !P            Γ, {Q} |- Goal
──────────────────────────────────── loli_l
  Γ, !P, (!P ⊸ {Q}) |- Goal
```

Certificate: `loli_l(id, monad_l(continuation))`

When certificates are enabled, the `drainPersistentLolis` optimization is disabled. Lolis fire through the normal `findAllMatches` → `matchLoli` path, producing normal tree nodes with normal `loli_l` certificates. No special handling needed.

### 3.6 rightFocus = Succedent Decomposition

After the forward engine reaches quiescence, `rightFocus` decomposes the succedent against residual state. This corresponds to standard right rules:

```
rightFocus(state, a ⊗ b):       rightFocus(state, 1):
  tensor_r                        one_r  [state empty]
  ├── id  [a ∈ state]
  └── id  [b ∈ state]

rightFocus(state, !p):
  bang_r
  └── id  [p ∈ persistent]
```

Each `rightFocus` call produces a proof tree node. Leaves are identity axioms.

### 3.7 Foundational Proof Certificates (Miller, 2013)

FPC uses focused sequent calculi as the kernel. Focusing separates deterministic (clerk) from choice-point (expert) phases — mapping directly to certificates:

- **Clerk** (asynchronous/negative): deterministic — consuming facts, applying substitution, producing consequent. No guidance needed.
- **Expert** (synchronous/positive): supplies choices — which rule to fire, which facts to match, what substitution to use.

### 3.8 Compact Certificates (Chaudhuri, 2012)

Certificates for linear logic do **not** need to record resource splits between premises — the checker reconstructs them. The certificate only needs: rule name, consumed facts, substitution, and persistent proof subtrees.

---

## 4. Store-Free Verifier

### 4.1 Design Principle

The certificate verifier works with **plain term objects**, not content-addressed hashes. The Store (~300 LOC) stays outside the trust boundary.

The certificate builder (untrusted, has Store access) expands hashes into term objects:

```javascript
// Content-addressed hash 48291 → expanded term object
{ tag: 'plus', children: [
  { tag: 'atom', name: '3' },
  { tag: 'atom', name: '5' },
  { tag: 'atom', name: '8' }
]}
```

The verifier uses:
- **Structural equality**: recursive comparison of term objects
- **Substitution application**: replace freevar nodes with bindings (~15 LOC)
- **Proof tree walking**: recursive verification (~40 LOC)

No Store, no hash-consing, no tag tables in the trust boundary.

### 4.2 Trust Boundary

| Component | Trusted | Size |
|-----------|---------|------|
| `kernel.js` (existing backward verification) | Yes | 205 LOC |
| Forward proof tree verifier | Yes | ~100 LOC |
| rightFocus proof tree verifier | Yes | ~30 LOC |
| Backward clause proof verifier | Yes | ~40 LOC |
| Term object equality + substitution | Yes | ~25 LOC |
| **Total trusted code** | | **~400 LOC** |
| Store, hash-consing, tag tables | **No** | ~300 LOC |
| `explore.js`, `match.js`, `forward.js`, `strategy.js`, `state-ops.js` | **No** | ~1500 LOC |
| `prove.js` (backward search) | **No** | ~280 LOC |
| FFI (`arithmetic.js`, `memory.js`) | **No** | ~200 LOC |

---

## 5. Certificate Structure

### 5.1 Forward Step Proof Node

Each forward step is a `⊸L` node with:

```javascript
{
  rule: 'loli_l',              // ILL rule applied
  forwardRule: string,         // Name of the forward rule (e.g. 'evm/add')
  // Left premise: antecedent proof (tensored identity axioms)
  antecedentProof: {
    rule: 'tensor_r',
    children: [
      { rule: 'id', term: expandedTerm },  // identity axiom for each consumed fact
      ...
    ]
  },
  // Persistent antecedent proofs (backward proof subtrees)
  persistentProofs: [
    // For state lookup:
    { rule: 'id', term: expandedTerm },
    // For clause resolution:
    { rule: 'clause_name', goal: expandedTerm, children: [ ...subProofs ] },
    ...
  ],
  // Right premise: continuation (next step or leaf)
  continuation: nextProofNode
}
```

### 5.2 Backward Clause Proof Node

Each backward proof from clause resolution:

```javascript
{
  rule: string,                // Clause name (e.g. 'plus/s')
  goal: expandedTerm,          // What was being proved (e.g. plus(3, 5, 8))
  unifier: { [varName]: expandedTerm },  // How clause head unified with goal
  children: [                  // Proofs of clause premises
    { rule: 'plus/s', goal: ..., children: [...] },
    ...
    { rule: 'plus/z', goal: ..., children: [] }  // ← axiom (leaf)
  ]
}
```

### 5.3 rightFocus Proof Node

```javascript
// tensor_r: A ⊗ B → prove A and B separately
{ rule: 'tensor_r', children: [leftProof, rightProof] }

// one_r: 1 → check state empty
{ rule: 'one_r', children: [] }

// bang_r: !A → check A in persistent
{ rule: 'bang_r', children: [{ rule: 'id', term: expandedTerm }] }

// id: atom → consume from state
{ rule: 'id', term: expandedTerm }
```

### 5.4 Loli Step Proof Node

A loli `!P ⊸ {Q}` fired from state — same structure as §5.1 but the rule is a loli from the state, not a compiled forward rule:

```javascript
{
  rule: 'loli_l',
  loliHash: expandedTerm,     // The loli formula itself
  antecedentProof: { ... },   // Proof of !P (identity or backward proof)
  monadUnpack: {
    rule: 'monad_l',
    child: continuation       // Next step with Q in context
  }
}
```

### 5.5 Full Trace Certificate (Committed Choice)

For `forward.run()`:

```javascript
{
  type: 'forwardTrace',
  initialState: { linear: [...expandedTerms], persistent: [...expandedTerms] },
  proofTree: nestedProofNode,  // Nested ⊸L + monad_l applications
  finalState: { linear: [...expandedTerms], persistent: [...expandedTerms] },
  rightFocusProof: rightFocusProofNode,  // Succedent decomposition tree
  quiescent: boolean
}
```

### 5.6 Tree Certificate (Exhaustive Exploration)

For `explore()`, each tree node carries a proof fragment:

```javascript
{
  type: 'branch',
  children: [{
    rule: string,
    choice: number | null,
    proof: forwardStepProofNode,  // ⊸L node for this step
    child: subtreeNode
  }, ...]
}
```

### 5.7 Explore Tree Non-Proof Nodes

Not all explore tree nodes carry proof certificates. Only `branch` and `leaf` nodes represent valid ILL derivation steps:

| Node type | Certificate | Rationale |
|-----------|-------------|-----------|
| `branch` | ⊸L proof per child | Each child = one forward step |
| `leaf` | rightFocus proof | Quiescent state decomposed against succedent |
| `bound` | None | Depth limit — exploration incomplete, not a proof |
| `cycle` | None | Back-edge — loop detected, not a proof |
| `memo` | Reference to earlier cert | Structurally identical subtree already certified |
| `dead` | None | Constraint UNSAT pruning — optimization, not derivation |

`dead` and `memo` are optimizations. If we want to certify the explore tree *structure* (all branches correctly explored), that's a separate concern from certifying individual steps. Step certificates are Phase 1; tree-structure certificates are future work (TODO_0045 scope).

---

## 6. Verification Algorithm

### 6.1 Forward Step Verification

```
Input: ⊸L proof node, state (as term objects)
Output: { valid: boolean, stateAfter }

1. Check antecedent proof:
   a. Walk the tensor_r tree of identity axioms
   b. For each id leaf: check the term EXISTS in state.linear
   c. Mark each matched term as consumed

2. Check persistent proofs:
   a. For 'id' (state lookup): check term ∈ state.persistent
   b. For clause proof: verify clause proof tree (§6.2)

3. Check production:
   a. Apply substitution to forward rule's consequent patterns
   b. Compute new state = old state - consumed + produced

4. Check monad_l: body unpacks correctly

5. Return { valid: true, stateAfter }
```

### 6.2 Backward Clause Proof Verification

```
Input: clause proof node, clause definitions
Output: { valid: boolean }

1. Look up clause by name
2. Apply unifier to clause head → check equals goal
3. Apply unifier to each clause premise → check equals child's goal
4. Recursively verify each child
5. Leaf (axiom): clause with no premises → valid
```

### 6.3 rightFocus Verification

```
Input: rightFocus proof node, residual state
Output: { valid: boolean, remainingState }

For tensor_r: verify left child, then right child (threading state)
For one_r: check state is empty
For bang_r: check inner term ∈ persistent
For id: check term ∈ linear, consume it
```

### 6.4 Full Trace Verification

```
Input: trace certificate
Output: { valid: boolean, errors: string[] }

1. state = initialState
2. Walk the nested ⊸L + monad_l proof tree:
   At each ⊸L: verify step (§6.1), advance state
3. At the final state: verify rightFocus proof (§6.3)
4. Check remaining state is empty after rightFocus
5. Optionally: check no rules match final state (quiescence)
```

---

## 7. Implementation Plan

### Phase 1: `proveWithCert` — backward proving with proof trees (~60 LOC)

New function in `prove.js` — a **separate export**, not a modification of `prove()`:

```javascript
// prove.js — existing prove() is UNTOUCHED
function proveWithCert(goal, clauses, types, opts = {}) {
  // Same as prove() but useFFI forced false, collects proof tree nodes
  // Wraps the existing search() loop, adding tree construction on success path
}
```

`prove()` continues to return `{ success, theta }`. `proveWithCert()` returns `{ success, theta, proof }`. The existing `search()` is refactored to accept a `buildProof` callback (or duplicated — it's ~50 LOC). No `if` branches in the hot path.

**Leverages existing `useFFI` flag** (prove.js:146) — just pass `useFFI: false`. Only proof tree assembly is new.

### Phase 2: `provePersistentWithCerts` — cert-mode persistent proving (~60 LOC)

New file `lib/engine/opt/cert-proving.js`. Based on existing `provePersistentNaive` (match.js:213) — same state lookup → clause resolution flow, plus proof tree collection:

```javascript
function provePersistentWithCerts(patterns, startIdx, theta, slots, state, calc) {
  // Same structure as provePersistentNaive, but:
  // - State lookup hit → record { rule: 'id', term }
  // - Clause resolution → call proveWithCert, record proof subtree
  // - Returns { idx, proofs: [...] }
}
```

Not a modification of `provePersistentWithFFI` or `provePersistentNaive`. Separate function, separate file.

### Phase 3: `certificate.js` — builder module (~80 LOC)

New file `lib/engine/certificate.js` (untrusted). All cert construction in one place:

- `expandTerm(hash)` — Store hash → flat term object
- `buildStepCert(match, persistentProofs)` — match result → ⊸L proof node
- `buildLoliCert(loliMatch, antecedentProof)` — loli match → loli_l proof node
- `rightFocusCert(linear, persistent, hash, roles)` — succedent → decomposition tree
- `buildTraceCert(initialState, steps, rightFocusProof)` — full trace cert
- `flattenToArena(certTree)` — JS objects → flat `CertNode[]` for Zig/binary

This module imports Store (untrusted). The verifier does NOT import this module.

### Phase 4: Store-free verifier (~150 LOC)

New module `lib/prover/verify-forward.js` (**trusted**, in kernel boundary):

- `verifyForwardStep(proofNode, state)` — verify one ⊸L application (~40 LOC)
- `verifyClauseProof(proofNode, clauses)` — verify backward proof tree (~40 LOC)
- `verifyRightFocus(proofNode, state)` — verify succedent decomposition (~30 LOC)
- `termEqual(a, b)` — structural equality on term objects (~10 LOC)
- `applySubstitution(term, theta)` — replace freevars (~15 LOC)
- `verifyForwardTrace(trace, clauses)` — full trace verification (~15 LOC)

Works with plain term objects only. No Store dependency. No engine imports. Zig-translatable.

### Phase 5: Wire into entry points (~30 LOC)

**Function pointer swap** at `explore()` / `forward.run()` entry:

```javascript
// explore.js entry
const proveGoals = opts.certificates ? provePersistentWithCerts : provePersistentWithFFI;
const drainLolis = opts.certificates ? null : drainPersistentLolis;
// Pass proveGoals / drainLolis into go() — no if-branches in the DFS loop
```

Extend `kernel.js:verifyStep` for monad_r:

```javascript
if (ruleName === 'monad_r') {
  if (evidence) {
    const fwdVerify = require('./verify-forward');
    return fwdVerify.verifyForwardTrace(evidence, clauseDefinitions);
  }
  return { valid: true, unverified: 'modeSwitch', evidence: null };
}
```

Extend `bridge.js:executeModeSwitch` to pass `certificates` option through.

### Phase 6: Binary serialization (~40 LOC)

Extend `store-binary.js` SoA pattern for certificates:

```
Header: magic, version, nodeCount, termCount
Nodes:  kind[N], rule[N], numChildren[N], childStart[N], termIdx[N]
Terms:  (reuse existing Store binary format)
CRC32
```

A certificate is a single contiguous buffer. Can be memory-mapped by a Zig verifier. Same pattern as the existing Store snapshot.

### Phase 7: Tests (~80 LOC)

**Certificate generation:**
- Single forward step → ⊸L proof node with identity axiom leaves
- Persistent goal via clause → backward proof tree (e.g. plus/z, plus/s chain)
- Persistent goal via state lookup → identity axiom
- Loli firing → loli_l(id, monad_l(continuation))
- rightFocus → tensor_r / one_r / bang_r tree

**Certificate verification:**
- Valid certificates → verifier accepts
- Tampered: wrong substitution → verifier rejects
- Tampered: missing consumed fact → verifier rejects
- Tampered: wrong clause proof → verifier rejects
- Tampered: wrong rightFocus tree → verifier rejects

**Zero-overhead:**
- Benchmark: explore with `certificates: false` matches baseline (no regression)
- No extra allocations when certificates disabled

**Integration:**
- Backward prover fires monad_r → forward engine runs with certificates → kernel verifies full proof tree
- `verifyTree` on a proof tree containing monad_r returns `{ valid: true }` with NO `unverified` flags

---

## 8. Certificate-Mode Behavior

When `certificates: true` is passed to the forward engine:

| Feature | Normal mode | Certificate mode |
|---------|------------|------------------|
| FFI for persistent goals | Enabled (fast path) | **Disabled** — clause resolution only |
| `drainPersistentLolis` | Enabled (eager) | **Disabled** — lolis fire via normal matching |
| prove.js return value | `{ success, theta }` | `{ success, theta, proof: proofTree }` |
| Tree node data | `{ rule, child }` | `{ rule, proof: ⊸LNode, child }` |
| rightFocus | Returns remaining state | Returns remaining state **+ proof tree** |
| forward.run trace | `["[0] ruleName", ...]` | `[proofNode, ...]` |
| Preserved-skip | Enabled | Normalized out in certificate (logical view) |

**Zero overhead when disabled.** Function pointer swap at entry — no branches, no allocations, no shape pollution in the normal path. V8 sees monomorphic call sites.

**Certificate mode is slower — by design.** FFI disabled → clause resolution for all persistent goals. For EVM (153 prove() calls per tree: 75× inc, 60× plus, 18× neq), clause resolution replaces O(1) FFI with recursive backward search. Expected ~5-10× slower in cert mode. This is acceptable: correctness trumps speed when verifying. Normal mode is unaffected.

---

## 9. What This Enables

### 9.1 Machine-Checked Soundness

Every forward step is independently verified as a valid ILL derivation. Bugs in `explore()`, `findAllMatches()`, `tryMatch()`, the strategy stack, preserved-skip, compiled substitution, Arena mutation/undo, constraint solver, FFI — none can compromise soundness. Only the ~400 LOC verifier (working with plain term objects) is trusted.

### 9.2 Closing the Monad Gap

`monad_r` steps go from `{ valid: true, unverified: 'modeSwitch' }` to `{ valid: true }`. Full proof trees (backward + forward) become kernel-verified end-to-end.

### 9.3 Foundation for TODO_0045 and TODO_0008

The execution tree judgment `Σ; Δ ⊢_fwd T` requires each step be a valid ILL derivation — certificates provide the machine-checkable witness. Metaproof properties (invariants, reachability) verified against certified traces inherit soundness.

---

## 10. Worked Example

### Forward rule: `evm/add`

```
evm/add: pc(PC) * code(PC, 0x01) * stack(0, A) * stack(1, B) * !plus(A, B, C) * !inc(PC, PC')
  -o { pc(PC') * stack(0, C) }
```

State: `pc(0), code(0, 0x01), stack(0, 3), stack(1, 5)`

**Step 1: Match.** θ = {PC→0, A→3, B→5, C→8, PC'→1}

**Certificate proof tree:**

```
⊸L [evm/add]
├── left: ⊗R                          (antecedent proof)
│   ├── id [pc(0)]
│   ├── id [code(0, 0x01)]
│   ├── id [stack(0, 3)]
│   └── id [stack(1, 5)]
├── persistent proofs:
│   ├── plus(3, 5, 8):                 (backward proof from clauses)
│   │   plus/s [plus(3, 5, 8)]
│   │   └── plus/s [plus(2, 5, 7)]
│   │       └── plus/s [plus(1, 5, 6)]
│   │           └── plus/z [plus(0, 5, 5)]  ← axiom
│   └── inc(0, 1):
│       inc/s [inc(0, 1)]
│       └── inc/z [inc(0, 1)]               ← axiom (*)
└── right: monad_l                     (unpack body, new state)
    └── continuation...               (next step or leaf)
```

**Verifier checks:**
1. `pc(0)` ∈ state? Yes ✓
2. `code(0, 0x01)` ∈ state? Yes ✓
3. `stack(0, 3)` ∈ state? Yes ✓
4. `stack(1, 5)` ∈ state? Yes ✓
5. plus/s head unifies with plus(3,5,8)? Yes ✓ (recursively down to plus/z axiom)
6. inc clause head unifies with inc(0,1)? Yes ✓
7. Apply θ to consequent: `pc(1) * stack(0, 8)`? Matches produced ✓
8. New state: `{pc(1), code(0, 0x01), stack(0, 8)}` ✓

### Loli step example

State: `pc(6), stack(0, 8), !done, (!done ⊸ {result(ok)})`

```
                         pc(6), stack(0,8), result(ok) |- {1}
────────── id            ─────────────────────────────────── monad_l
!done |- !done           pc(6), stack(0,8), {result(ok)} |- {1}
─────────────────────────────────────────────────────────────── loli_l
pc(6), stack(0,8), !done, (!done ⊸ {result(ok)}) |- {1}
```

Certificate: `loli_l(id, monad_l(continuation))`

---

## 11. References

### External

- Miller, D. (2013) — "Foundational Proof Certificates" CADE. Clerk/expert pattern.
- Chaudhuri, K. (2012) — "Compact Proof Certificates for Linear Logic" CPP. Resource splits reconstructable.
- Watkins et al. (2004) — "CLF: A Concurrent Logical Framework." Monadic proof terms.
- Betz & Frühwirth (2013) — "Linear-Logic Based Analysis of CHR∨" TOCL. Soundness theorem 4.8: each forward step = valid ILL derivation.
- Carneiro, M. (2019) — "Metamath Zero." Minimal verifier architecture.
- Frühwirth, T. (2020) — "Justifications in CHR for Logical Retraction." Per-constraint provenance.
- Pfenning (2012) — "Lecture Notes on Monadic Logic Programming" 15-816. Forward steps as let-bindings.

### Internal

- [TODO_0045](0045_execution-tree-judgment.md) — Formal judgment for execution trees (§3.3, §5)
- [TODO_0066](0066_modular-architecture-refactor.md) — Architecture refactor (Decision 5, §5.5, Phase 2.4)
- [TODO_0008](0008_metaproofs.md) — Metaproofs (consumer of certificates)
- [RES_0077](../research/0077_modular-proof-kernel-architectures.md) — Modular proof kernel architectures (§4: FPC)
- [RES_0050](../research/0050_metaproof-verification-landscape.md) — Metaproof & verification landscape

### Code (existing)

- `lib/prover/kernel.js` — L1 kernel, `verifyStep` (line 84-90: monad_r placeholder)
- `lib/prover/bridge.js` — Mode switch bridge, `executeModeSwitch` + `rightFocus`
- `lib/engine/explore.js` — DFS exploration, tree construction (function pointer swap at entry)
- `lib/engine/forward.js` — Committed-choice loop, trace collection
- `lib/engine/match.js` — `tryMatch`, `provePersistentNaive` (line 213, base for cert-proving)
- `lib/engine/prove.js` — Backward clause resolution, `useFFI` flag (line 146)
- `lib/engine/opt/ffi.js` — `provePersistentWithFFI` (normal mode, untouched)
- `lib/engine/opt/loli-drain.js` — Loli drain (null'd out via function pointer in cert mode)
- `lib/engine/state-ops.js` — `mutateState`, consume/produce operations
- `lib/engine/store-binary.js` — Binary SoA serialization (pattern for cert serialization)

### Code (new — to be created)

- `lib/engine/certificate.js` — Builder: match results → cert nodes, term expansion (untrusted)
- `lib/engine/opt/cert-proving.js` — `provePersistentWithCerts` (untrusted)
- `lib/prover/verify-forward.js` — Store-free verifier (~150 LOC, **trusted**)
