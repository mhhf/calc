---
title: "Self-Verification via Reflective Towers: Milawa, Proof Certificates, and the Road to CALC-in-CALC"
created: 2026-03-23
modified: 2026-03-24
summary: "Survey of self-verification strategies for proof systems: Milawa's reflective tower (first-order, no dependent types), Lean4Lean, MetaCoq, and what CALC already has vs what it needs. Two paths: Milawa-style (proof certificates + reflection) vs Idris-style (QTT + self-hosting). Milawa path is more natural for CALC."
tags:
  - proof-theory
  - verification
  - proof-certificates
  - self-verification
  - milawa
  - dependent-types
  - QTT
  - bootstrapping
  - linear-logic
  - architecture
  - curry-howard
  - clf
category: "Implementation"
---

# Self-Verification via Reflective Towers

## The Goal

Two aspirations for CALC:
1. **Prove properties about programs** written in the calculus (safety, conservation, termination)
2. **Implement CALC inside CALC** and prove it correct internally (self-hosting / self-verification)

This survey examines how existing systems achieve these goals and what CALC needs.

---

## 1. The Landscape: How Systems Self-Verify

### 1.1 Milawa — Self-Verification Without Dependent Types

**Milawa** (Davis, UT Austin, 2009) is a self-verifying theorem prover for an ACL2-like first-order logic. It demonstrates that **dependent types are not required for self-verification**.

**Architecture: reflective tower of 11 levels.**

```
Level 1:  Tiny proof checker (~1500 lines)
          Only does: instantiation + cut
          Small enough to verify by hand / social audit

Level 2:  Adds propositional reasoning
          Proved sound relative to Level 1

Level 3:  Adds rewriting
          Proved sound relative to Level 2
  ...
Level 11: Full ACL2-style reasoning
          Proved sound relative to Level 10
```

Each level is a proof checker that can verify proofs produced by the level above it. The key property: **trust reduces transitively** — trusting Level 11 reduces to trusting Level 1. Level 1 is small enough to verify by inspection.

**Verified all the way to machine code.** The Jitawa project (Myreen & Davis) verified a Lisp runtime in HOL4 and compiled Milawa to x86 machine code with a machine-checked correctness proof. The trust chain goes from the mathematical specification to the hardware ISA.

**What Milawa does NOT need:**
- Dependent types
- Universe hierarchy
- Higher-order logic
- Linear types

**What Milawa DOES need:**
- First-order logic with equality
- Inductive data types (for representing terms and proofs)
- A reflection principle (proofs are data that can be inspected by programs)
- A small, trusted kernel that checks proof certificates

**Reference:** Davis, *Verified Milawa*, UT Austin 2009. Myreen & Davis, *The Reflective Milawa Theorem Prover Is Sound*, JAR 2015.

### 1.2 Lean4Lean — Verified Type Checker

Lean 4 is self-hosted (written in Lean, compiled via C). **Lean4Lean** (Carneiro, 2024) independently reimplements Lean's type checker in Lean itself:
- Re-checks all of Mathlib at ~20-50% overhead
- Found and triggered a fix for one soundness bug in the reference C++ kernel
- Proves partial correctness of kernel components

The trusted base remains the C++ reference kernel. Full formal verification of the kernel is in progress.

**Reference:** Carneiro, *Lean4Lean*, arXiv:2403.14064, 2024.

### 1.3 MetaCoq — Coq's Theory Formalized in Coq

MetaCoq/MetaRocq formalizes Coq's type theory (PCUIC) inside Coq:
- Verified type checker for a fragment of Coq (no modules, no template polymorphism)
- Certified erasure procedure (types/proofs → untyped lambda calculus)
- Proves soundness relative to the formal spec

**Key shift: Trusted Theory Base (TTB) vs Trusted Code Base (TCB).** Instead of trusting the implementation, trust the mathematical specification. The implementation is proved correct relative to the spec. What remains axiomatic (by Gödel): consistency and strong normalization of PCUIC itself.

**Reference:** Sozeau et al., *Coq Coq Correct!*, POPL 2020.

### 1.4 Nuprl — Computational Reflection

Nuprl implements Computational Type Theory (CTT, realizability-based). It has direct reflection: syntax is part of the semantics, allowing Nuprl to reason about its own derivations. The kernel (which gives types their semantics) is trusted but not self-verified.

### 1.5 CakeML — Verified Compiler Bootstrapping

CakeML is a verified ML compiler bootstrapped inside HOL4. The compiler compiles itself; the compiled binary has a HOL4-checked correctness theorem down to machine code. Shows that verified self-compilation is achievable for practical languages. No dependent types — uses HOL4 (higher-order logic) for the proofs.

### Summary Table

| System | Self-hosting | Kernel verified | Min logic | TCB |
|---|---|---|---|---|
| Milawa | Yes (reflective tower) | Yes (down to x86) | First-order + reflection | Level-1 checker (~1500 LOC) |
| Lean 4 | Yes (via C) | Partial (Lean4Lean) | CIC-like | C++ kernel + stage0 |
| MetaCoq | Verified relative to spec | Yes (parts) | CIC | PCUIC spec (TTB) |
| CakeML | Yes (compiler) | Yes (in HOL4) | HOL4 | HOL4 + ISA semantics |
| Idris 2 | Yes (via Scheme) | No | QTT | TT kernel + Chez Scheme |
| Celf | No | No | CLF | Trusted interpreter |
| **CALC** | **No** | **Partial (backward only)** | **ILL + lax monad** | **~205 LOC L1 kernel + ~1500 LOC engine** |

---

## 2. What CALC Already Has

CALC's proof infrastructure is more advanced than it might seem:

### 2.1 Backward Prover: Full Proof Certificates

The backward prover (L1-L4) produces **ProofTree** objects — recursive trees where each node carries a conclusion (sequent), a rule name, and child proof trees. The L1 kernel (`kernel.js`, ~205 LOC) verifies these via `verifyTree`: for each node, it recomputes expected premises from the rule descriptor and checks them against the actual children.

```
ProofTree node:
  { conclusion: Sequent, rule: string, proven: boolean, premises: ProofTree[] }
```

This is the de Bruijn criterion in action: the prover (L2-L4) is untrusted; only the L1 kernel checker is trusted.

### 2.2 Forward Engine: The Trust Gap

The forward engine (`forward.js`, `explore.js`) does NOT produce proof trees. It produces **execution traces** — sequences of `{rule, consumed, theta}` records. The bridge (`bridge.js`) wraps these in a `monad_r` ProofTree node with `unverified: 'modeSwitch'` — an explicit trust gap.

### 2.3 Guided Mode: Closing the Gap

The `'guided'` execution profile closes this gap partially:
- Forward engine emits enriched traces with `persistentEvidence` (backward proof subtrees for each persistent goal)
- `guidedTerm` constructs a full ILL proof term (GenericTerm tree)
- `check-term.js` verifies it
- The kernel returns `{ valid: true, evidence: state.monadicTerm }` — verified!

### 2.4 Content-Addressed Store

Every formula, sequent, and term is a content-addressed hash (int32). Equality is O(1). This is a natural representation for proof terms as data — the store already interns everything.

### 2.5 What's Missing for Milawa-Style Self-Verification

| Have | Missing |
|---|---|
| L1 kernel verifies backward proofs | Forward engine not fully certified (TODO_0067) |
| GenericTerm proof terms (`Δ ⊢ t : A`) | Proof terms are JS objects, not Store-interned (~50 LOC to fix) |
| Content-addressed store | — (Store already interns all formulas; proof terms just need the same treatment) |
| `!` modality + forward chaining = recursion | ~15 persistent `check` rules needed (one per ILL constructor) |
| Forward exhaustive exploration | No self-representation of rule definitions (can't inspect own rules) |

**Key insight (2026-03-23):** ADTs/inductive types are NOT required for the self-verification checker. The `!` (bang) modality + forward chaining already provides structural recursion: persistent `check` rules re-trigger on their own output, decomposing proof trees to leaves. This is standard fixpoint computation. The forward engine already handles this pattern in every `.ill` program. See TODO_0008 §14 for the concrete approach.

What IS still missing:
1. **Intern GenericTerms in Store** — small mechanical change (~50 LOC)
2. **Write ~15 persistent check rules** — one per proof constructor (~30 lines of `.ill`)
3. **Complete forward proof certificates** (TODO_0067) — so all execution modes produce verifiable terms
4. **Self-representation of rules** — for Level 2+ soundness proofs, the system needs to inspect its own rule definitions within the logic. This is the harder, longer-term piece.

---

## 3. Two Paths to Self-Verification

### 3.1 Path A: Milawa-Style Reflective Tower

**Idea:** Don't change the logic. Use CALC's existing forward/backward machinery to build a reflective tower.

**Step 1: Complete proof certificates (TODO_0067).** Make the forward engine emit verifiable ILL proof trees for every step. The guided mode (`guidedTerm`) already does this partially — extend to all execution modes. The L1 kernel then verifies ALL execution, not just backward proofs.

**Step 2: Intern proof terms in Store.** GenericTerms are currently plain JS objects. Interning them via `Store.put('tensor_r', [child1, child2])` makes them content-addressed hashes that can appear as ILL facts. Small mechanical change (~50 LOC).

**Step 3: Encode Level-1 checker as persistent ILL rules.** Write ~15 persistent check rules — one per proof constructor:

```ill
% Level-1 checker as persistent forward rules
!check_tensor_r: !(check(tensor_r(P1, P2), tensor(A, B)) -o {check(P1, A) * check(P2, B)}).
!check_id:       !(check(id(X), X)                        -o {verified(X)}).
!check_loli_l:   !(check(loli_l(P1, P2), loli(A, B))     -o {check(P1, A) * check(P2, B)}).
% ... ~12 more rules
```

Seed state with `check(proofHash, goalType)`. The forward engine fires rules to quiescence — each step decomposes one proof node, producing sub-checks. At leaves, `id` produces `verified`. No ADTs needed — the `!` modality + forward chaining IS structural recursion.

**Step 4: Prove Level-2 strategies sound.** Use CALC's own proof search to prove that higher-level strategies (focusing, auto mode) produce proof trees that Level 1 accepts. This is where the reflective tower starts.

**Pros:** No dependent types needed. No ADTs needed. Incremental. Uses existing infrastructure.
**Cons:** Self-referential reasoning is limited without dependent types. Bounded verification only (any concrete proof can be checked, but "all proofs" requires induction).

### 3.2 Path B: QTT / Idris-Style Self-Hosting

**Idea:** Extend CALC's type system to QTT (Quantitative Type Theory). Then CALC becomes a dependently-typed linear language that can host its own type checker.

**The QTT type system.** Every variable binding carries a quantity:
- `0` = erased (available for types, not computation)
- `1` = linear (used exactly once)
- `ω` = unrestricted (used freely)

Types are always checked in the ω-world (substitution into types is unrestricted). Linearity is enforced only in the term layer. This resolves the fundamental tension: "types need to inspect values that are linear."

**Minimal steps for CALC:**

```
Current ILL  →  ADTs + recursion  →  Sort refinements  →  Graded modalities (0/1/ω)
  →  Dependent Π (unrestricted)  →  Full QTT  →  Universes + reflection
```

Each step is independently useful. Full self-hosting requires the final step (universes + reflection), which is years out.

**Key papers:**
- Atkey, *Syntax and Semantics of QTT*, LICS 2018
- Brady, *Idris 2: QTT in Practice*, ECOOP 2021
- Krishnaswami, Pradic & Benton, *Integrating Linear and Dependent Types*, POPL 2015
- Speight, *Impredicativity in Linear Dependent Type Theory*, arXiv:2602.08846, 2026 (state of the art)

**Key obstacle:** LLF (Cervesato-Pfenning 1996) proved that in a linear logical framework, types must live in the intuitionistic fragment. Types cannot depend on linear variables. QTT resolves this via quantity-0 (erased) bindings — the value is available for type computation but erased at runtime. See RES_0071 for full survey of the LLF/CLF/QTT hierarchy.

**Pros:** Most expressive. Full Curry-Howard. Self-hosting becomes natural.
**Cons:** Massive extension. Years of work. Requires rearchitecting kernel, parser, unifier.

### 3.3 Recommended Path: A then B

```
NOW:      VMTests with [default: _ 0]           (current ILL, no changes)
NEXT:     Complete proof certificates             (TODO_0067, guided mode extension)
NEXT:     Intern proof terms in Store             (~50 LOC, enables check rules)
NEXT:     ~15 persistent check rules              (~30 lines .ill, Level-1 checker in ILL)
          ─── Milawa Path A available here ───
THEN:     ADTs + recursive types                  (TODO_0009, enables inductive reasoning)
THEN:     Sort refinements                        (three-layer cake becomes first-class)
LATER:    Graded modalities (0/1/ω)               (QTT quantities, enables erasure)
LATER:    Dependent Π                             (types depend on ω-variables)
FAR:      Full QTT + universes + reflection        (self-hosting)
```

Path A (Milawa) becomes available much earlier than previously thought — immediately after proof certificates + Store interning + check rules. No ADTs required for the operational checker. ADTs (TODO_0009) add inductive reasoning ("for ALL proofs, the checker is correct") but the concrete checker works without them. Path B (QTT) becomes available at the final step. Both paths build on each other — Path A infrastructure is useful even after Path B arrives.

---

## 4. The Proof Certificate Question

**"Don't we already have proof certificates in the form of terms?"**

Yes, partially:

| Component | Has certificates? | Verified by kernel? |
|---|---|---|
| Backward prover (L1-L4) | Yes — ProofTree | Yes — `verifyTree` |
| Forward engine (`run`) | Trace only | No — `unverified: 'modeSwitch'` |
| Forward engine (`guided`) | Yes — GenericTerm | Yes — `check-term.js` |
| Exhaustive exploration | Execution tree + per-leaf traces | No (tree structure unverified) |

The backward prover fully satisfies the de Bruijn criterion. The forward engine in `guided` mode also satisfies it (proof terms are verified by `check-term.js`). The gap is:

1. **`'full'` mode** (default) produces opaque CLF let-chains, not verified ILL proof trees
2. **`explore()`** produces execution trees with per-leaf traces, but the tree structure (branching, cycle detection, memoization) is not independently verified
3. **No self-representation** — proof terms are JS objects, not ILL facts. The system can produce and verify proofs, but cannot reason *about* proofs within the logic

TODO_0067 addresses gap 1-2. Gap 3 requires ADTs + reflection (Milawa Step 2-3).

---

## 5. Forward-Chaining and Property Verification

CALC's `explore.js` can already verify properties by exhaustive exploration — but with limits:

**What forward-chaining CAN verify:**
- Reachability of specific states (does execution ever produce a fact pattern?)
- Invariant preservation over finite state spaces (every reachable state satisfies P)
- Protocol safety (no "bad" multiset is reachable)
- Program termination (if exploration terminates, the program terminates)

**What it CANNOT verify without more machinery:**
- Universal quantification over infinite inputs (`∀n. program(n) satisfies P`)
- Properties of non-terminating programs (liveness, fairness)
- Self-referential properties about the engine itself

The `!` (bang) modality makes ILL undecidable (Cervesato, certified in Coq by Larchey-Wendling). Exhaustive exploration is semi-decidable — it confirms properties when it terminates but cannot guarantee termination.

For bounded verification, `explore()` is already a model checker. For unbounded verification, inductive reasoning is needed — which is what the Milawa-style reflective tower (or dependent types) provides.

See RES_0050 for the full metaproof verification landscape (Petri net invariants, CEGAR, confluence checking).

---

## Key References

- Davis, *A Self-Verifying Theorem Prover*, UT Austin PhD thesis, 2009
- Myreen & Davis, *The Reflective Milawa Theorem Prover Is Sound*, JAR 55(2), 2015
- Carneiro, *Lean4Lean: Lean's Type Theory in Lean*, arXiv:2403.14064, 2024
- Sozeau et al., *Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq*, POPL 2020
- Kumar et al., *CakeML: A Verified Implementation of ML*, POPL 2014
- Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS 2018
- Brady, *Idris 2: Quantitative Type Theory in Practice*, ECOOP 2021
- Cervesato & Pfenning, *A Linear Logical Framework*, LICS 1996 / I&C 2002
- Krishnaswami, Pradic & Benton, *Integrating Linear and Dependent Types*, POPL 2015
- Speight, *Impredicativity in Linear Dependent Type Theory*, arXiv:2602.08846, 2026
- Rouvoet et al., *Intrinsically-Typed Definitional Interpreters for Linear, Session-Typed Languages*, CPP 2020
- McCreight & Schürmann, *A Meta Linear Logical Framework (MLLF)*, LFM 2004
- Larchey-Wendling & Forster, *Certified Undecidability of ILL*, CPP 2019
