---
title: "ZK Proof Certification as Proof Theory: Deriving STARK Verifiers from Inference Rules"
created: 2026-03-17
modified: 2026-03-17
summary: "CALC's ZK backend derives STARK verifier chips from the same declarative rule definitions that drive proof search, establishing a proof-theoretic correspondence where buses encode structural rules and STARK soundness yields certified derivability."
tags: [zk, stark, proof-theory, linear-logic, soundness, verification, Curry-Howard, plonky3, resource-semantics, type-checking, symbolic-execution, evm]
category: "ZK Certification"
unique_contribution: "Four novel contributions: (1) auto-generating STARK verifier chips from declarative inference rule descriptors — one source of truth for proof search, forward execution, and ZK verification (no existing system does this); (2) the first ZK proof system for substructural logic derivations, with a precise correspondence between LogUp buses and ILL structural rules; (3) certified symbolic EVM execution — per-path STARK proofs covering all execution paths, where zkEVMs certify only concrete traces; (4) formalizing two certification levels (full derivation vs resource accounting) as distinct proof-theoretic judgments with an explicit strength/efficiency trade-off."
references:
  - "Ben-Sasson, Bentov, Horesh, Riabzev, 'Scalable, transparent, and post-quantum secure computational integrity', 2018 (STARKs)"
  - "Watkins, Cervesato, Pfenning, Walker, 'CLF', 2004"
  - "Andreoli, 'Logic Programming with Focusing Proofs', 1992"
  - "Girard, 'Linear Logic', TCS, 1987"
  - "Luick, Berzins, Barbosa, Ozdemir, 'ZKSMT: A VM for Proving SMT Theorems in Zero Knowledge', USENIX Security, 2024"
  - "Haböck, 'Multivariate lookups based on logarithmic derivatives', 2022 (LogUp)"
  - "Laufer, Ozdemir, Boneh, 'zkPi: Proving Lean Theorems in Zero-Knowledge', ACM CCS, 2024"
  - "Ozdemir, Wahby, Whyte, Boneh, 'CirC: Compiler infrastructure for proof systems', IEEE S&P, 2022"
  - "Necula, 'Proof-Carrying Code', POPL, 1997"
  - "Trabish, 'Enhancing Symbolic Execution with Machine-Checked Safety Proofs', CPP, 2026"
  - "ZK-ProVer, 'Proving Programming Verification in Non-interactive Zero-Knowledge Proofs', ePrint 2025/1152"
  - "Zinnia, 'Expressive, Efficient Zero-Knowledge Framework for General-Purpose Data Analytics', ePrint 2025/572"
  - "Cervesato, Pfenning, 'A Linear Logical Framework', Information and Computation, 2002"
---

# ZK Proof Certification as Proof Theory

CALC's ZK backend transforms ILL derivations into STARK proofs. This document articulates the proof-theoretic content of that transformation — what the buses mean, what the two certification levels prove, and where the novelty lies relative to existing ZK proof systems.

## Display Rules

The ZK pipeline expressed as inference rules. Read bottom-up: the conclusion of one rule feeds the premise of the next.

### ZK-Prove: derivation to STARK proof

```
         G
    ─────────────
    Δ ⊢ c : C                prove(c, Δ ⊢ C) = p
    ──────────────────────────────────────────────── ZK-Prove
                    ⟨Δ, C, p⟩ zk-cert
```

Given a derivation `G` witnessing `Δ ⊢ c : C`, the STARK prover produces a certificate `p`. The witness `c` is consumed — it does not appear in the conclusion. The public statement `(Δ, C)` and proof `p` are all that remain.

### ZK-Verify: STARK proof to certified derivability

```
    ⟨Δ, C, p⟩ zk-cert          verify(Δ, C, p) = true
    ──────────────────────────────────────────────────── ZK-Verify
                   ∃x. Δ ⊢ x : C                          [ε ≤ 2⁻¹⁰⁰]
```

If the STARK verifier accepts, then a proof term exists. The soundness error `ε` is the probability of a false positive — negligible but nonzero. The verifier sees only `(Δ, C, p)`, never `c`.

### ZK-Compose: recursive composition as cut

```
    ⟨Δ₁, C₁, p₁⟩ zk-cert       ⟨Δ₂, C₂, p₂⟩ zk-cert
    ──────────────────────────────────────────────────── ZK-Compose
             ⟨(Δ₁,C₁) ∘ (Δ₂,C₂), p'⟩ zk-cert
```

Two STARK proofs compose into one via recursive verification (STARK-in-STARK). The PV-binding buses enforce agreement at boundaries — the sequent exposed by one chunk's public values must match the next chunk's expectations. This is the cut matching condition.

### ZK-Flat: resource accounting certificate

```
    Δ = S₀ →_{r₁} S₁ →_{r₂} ⋯ →_{rₙ} Sₙ          prove_flat(trace, Δ ⊢ C) = p
    ──────────────────────────────────────────────────────────────────────────────── ZK-Flat
                              ⟨Δ, C, p⟩ zk-flat-cert
```

```
    ⟨Δ, C, p⟩ zk-flat-cert          verify_flat(Δ, C, p) = true
    ──────────────────────────────────────────────────────────── ZK-Flat-Verify
                     ∃trace. Δ →* C                                [ε ≤ 2⁻¹⁰⁰]
```

The flat path certifies multiset rewriting, not full derivation. Weaker judgment, ~10.5x fewer rows.

### ZK-Symbolic: certified exhaustive exploration

```
    explore(Γ; Δ) = {L₁, L₂, ..., Lₖ}       ∀i. prove(cᵢ, Δ ⊢ Cᵢ) = pᵢ
    ──────────────────────────────────────────────────────────────────────── ZK-Symbolic
                    ⟨Γ, Δ, {(Cᵢ, pᵢ)}ᵢ₌₁ᵏ⟩ zk-sym-cert
```

Exhaustive symbolic exploration produces the complete set of reachable terminal states `{L₁, ..., Lₖ}`. Each terminal state `Lᵢ` gets its own STARK proof `pᵢ` certifying that the path from `Δ` to `Cᵢ` is a valid derivation. The collection of proofs constitutes a certification of all execution paths. See §Certified Symbolic Execution below.

### The full pipeline composed

```
         G
    ─────────────
    Δ ⊢ c : C                prove(c, Δ ⊢ C) = p
    ────────────────────────────────────────────── ZK-Prove
    ⟨Δ, C, p⟩ zk-cert        verify(Δ, C, p) = true
    ────────────────────────────────────────────── ZK-Verify
                  ∃x. Δ ⊢ x : C
```

The top is expensive (proof search). The middle is deterministic (STARK proving). The bottom is cheap (STARK verification). Each layer reduces the trusted computing base: search bugs are caught by type-checking; type-checker bugs are caught by the STARK; the STARK's trust is mathematical.

## Proof-Theoretic Content

The STARK circuit checks `checkTerm(c, Δ ⊢ C)` — proof term type-checking, not proof search. Type-checking is linear in `|c|`; proof search is exponential. The ZK layer operates only on the efficient side of this boundary.

The proof `p` does not contain `c`. The verifier sees `(Δ, C)` as public values (PVs) and learns nothing about which derivation was used. This is the zero-knowledge property.

### Knowledge soundness, not just existence

STARKs provide an argument of knowledge: for any (possibly cheating) prover P* producing `p` with `verify(Δ, C, p) = true`, there exists a polynomial-time extractor E recovering a valid `c` from P*'s internal state. The guarantee is stronger than mere existence — the prover must have possessed the derivation.

## Buses as Structural Rules

The deepest proof-theoretic content is in the bus architecture. Each LogUp bus in the STARK corresponds to a structural property of ILL:

| Bus | Type | Proof-theoretic role |
|---|---|---|
| OBLIG_BUS | PermutationCheck | Every proof obligation is discharged exactly once — **derivation completeness** |
| CONTEXT_BUS | PermutationCheck | Every linear resource is consumed exactly once — **linearity** |
| FORMULA_BUS | Lookup | Formula decomposition is structurally faithful — **subformula property** |
| GAMMA_BUS | Lookup | Persistent hypotheses are available — **exponential zone** (!-rules) |
| DISCARD_BUS | Lookup | `zero_l` can discard only with permission — **controlled weakening** |
| SUBST_TREE_BUS | PermutationCheck | Per-node substitution matching — **substitution correctness** |
| FREEVAR_BUS | Lookup | Free variable bindings are consistent — **eigenvariable condition** |

The two bus types encode two kinds of structural constraint:

- **PermutationCheck** (LogUp multiset equality): enforces that the multiset of values *produced* equals the multiset *consumed*. This is exactly the resource discipline of linear logic — every resource introduced must be used exactly once. False positive probability: `<= n / |F_ext|` where `F_ext ~ 2^124` (BabyBear quartic extension).

- **Lookup** (LogUp inclusion): enforces that every demand has a matching supply in a preprocessed ROM committed at keygen. This encodes the *structural* parts of the calculus — formula decomposition, persistent zone membership, discard permissions — which are fixed by the sequent and the calculus definition.

The correspondence is not metaphorical. Each bus constraint IS the algebraic encoding of its structural rule. CONTEXT_BUS multiset equality is linearity. OBLIG_BUS multiset equality is derivation completeness. FORMULA_BUS lookup inclusion is the subformula property. The STARK proof verifies that all structural rules hold simultaneously.

## Calculus-Agnostic Chip Generation

The Rust verifier contains zero ILL-specific code. Verifier chips are generated from `RuleSpec` descriptors, which are themselves derived from `.rules` definitions:

```
.calc/.rules definitions  -->  deriveZkRuleSpecs()  -->  RuleSpec JSON  -->  generic RuleChip AIR
```

A `RuleSpec` declares which buses a rule interacts with:

```
{ oblig_receive, premises: [PremiseSpec], ctx_receive, ctx_sends: [CtxSend],
  formula_lookup, gamma_lookup, fact_lookup, is_identity }
```

The generic `RuleChip` reads this spec at runtime and emits polynomial constraints accordingly. Adding a new inference rule = adding a `RuleSpec` value. Defining a new calculus = running `deriveZkRuleSpecs` on its `.rules` file. The same compiled Rust binary verifies proofs from any calculus.

**This is the central novelty.** No existing ZK proof system derives verifier circuits from declarative inference rule definitions. The closest systems (§Relationship to Existing Work) all require either hand-written circuits per rule/opcode, fixed VM architectures, or type-system-specific encodings. CALC auto-generates the verifier from the same source that drives proof search — one source of truth for three backends (backward prover, forward engine, STARK verifier).

## Two Certification Levels

The same calculus definition yields two STARK certificate paths with different proof-theoretic content:

### Tree path: certified derivability

Verifies a full ILL derivation tree via ZK-Prove / ZK-Verify (see display rules above). 13+ chips, 14 buses. Every proof term node maps to one chip row. The STARK certifies `∃c. Δ ⊢ c : C`.

### Flat path: certified resource accounting

Verifies a forward execution trace via ZK-Flat / ZK-Flat-Verify. 5-7 chips, 6 buses. Each forward step maps to one row. ~10.5x fewer rows. Certifies `∃trace. Δ →* C` (multiset rewriting), not full derivation.

### The gap between them

```
(∃c. Δ ⊢ c : C)  ⟹  (∃trace. Δ →* C)       but NOT vice versa in general
```

The flat path certifies that resources are conserved and rules applied correctly, but does not produce a proof term. For CALC's forward engine (which is sound for ILL — see theory/0001), the gap is narrow: every forward trace corresponds to a valid ILL derivation via `guidedTerm`. But the flat STARK does not certify this correspondence.

The two paths represent a **trade-off axis between proof-theoretic strength and certification efficiency** that, to our knowledge, has not been formalized for any ZK proof system.

## Certified Symbolic Execution

CALC's forward engine performs exhaustive symbolic exploration: given an initial sequent `Γ; Δ ⊢ {C}`, it discovers ALL reachable terminal states by exploring every nondeterministic branch (additive disjunction ⊕ in ILL). The result is a complete exploration tree where each leaf `Lᵢ` represents one possible execution outcome.

For the EVM use case: a Solidity contract compiled to ILL rules produces a symbolic exploration tree where each leaf is one possible final EVM state (STOP, REVERT, etc.). The MultisigNoCall benchmark produces 31 leaves (31 execution paths through the contract).

### What is certified

Each leaf `Lᵢ` gets its own STARK proof `pᵢ`:

```
∀i ∈ {1..k}:  verify(Δ, Cᵢ, pᵢ) = true  ⟹  ∃xᵢ. Δ ⊢ xᵢ : Cᵢ     [ε ≤ 2⁻¹⁰⁰]
```

The collection `{(Cᵢ, pᵢ)}ᵢ₌₁ᵏ` certifies:
1. Each path `Lᵢ` is a valid derivation from the initial sequent
2. The set `{C₁, ..., Cₖ}` covers all terminal states reachable from `Δ`

Property (2) is guaranteed by the completeness of the exploration engine (theory/0001), not by the STARK itself — the STARK certifies individual paths, while completeness is a property of the search. This is a deliberate design: the STARK verifies "this path is valid" (cheap, per-path), not "all paths were found" (expensive, global).

### Why this differs from zkEVMs

All existing zkEVM projects (Polygon, Scroll, zkSync, Taiko, Linea) verify **concrete** execution traces: given one specific input, one specific transaction, prove the state transition is correct. They answer: "this particular execution happened correctly."

CALC's certified symbolic execution answers a categorically different question: "**for all inputs** (within the symbolic abstraction), the contract's behavior satisfies properties provable in ILL." Each STARK proof certifies one branch of the universal statement. Together they cover the complete behavior space.

```
zkEVM:   ∃ input. execute(contract, input) = result  ∧  STARK-valid
CALC:    ∀ paths P. reachable(contract, P) ⟹ ∃c. Δ ⊢_P c : C_P  ∧  STARK-valid
```

This is the difference between testing (one concrete trace) and verification (all symbolic paths). zkEVMs are inherently per-execution. CALC's certified symbolic execution is inherently per-contract.

### The ILL resource semantics bridge

The connection between EVM execution and ILL derivation is not superficial. CALC models EVM state as ILL linear resources:

- **Linear facts** = mutable EVM state (memory cells, storage slots, program counter, stack elements). Consumed and reproduced at each step — linearity enforces that each state element is accounted for exactly once.
- **Persistent facts** = immutable EVM data (contract code, deployed bytecode). Available via the `!` modality — can be used any number of times.
- **EVM opcodes** = ILL rules (loli formulas in Γ). Each opcode's preconditions and postconditions are the antecedent and consequent of a linear implication `A ⊸ {B}`.
- **Additive disjunction** (⊕) = nondeterministic branching (JUMPI, conditional paths). Each branch is an additive choice; the symbolic explorer takes both.

The STARK proof verifies that the ILL derivation is valid — and the ILL derivation faithfully encodes the EVM execution by construction (the `.rules` definitions are the EVM semantics). This is a verified compilation path:

```
EVM semantics  ──(.rules)──>  ILL inference rules  ──(deriveZkRuleSpecs)──>  STARK AIR chips
```

The `.rules` definitions serve simultaneously as: (1) the executable semantics for the forward engine, (2) the search specification for the backward prover, and (3) the AIR constraint generator for the STARK verifier.

## Recursive Composition as Cut

STARK-in-STARK recursive composition follows ZK-Compose (see display rules). Each chunk proof certifies a sub-derivation; the recursive verifier combines them. The PV-binding buses (OBLIG_PV_BIND_BUS, CTX_PV_BIND_BUS) enforce that chunks agree at boundaries — the cut formula matching condition: the sequent exposed by one chunk's public values must match what the next chunk expects.

The `init_active_count` PV prevents chunk re-injection (non-first chunks must have `init_active_count = 0`), encoding a structural constraint on cut composition: only the first chunk introduces the initial sequent.

## Certified Derivability as a Modality

The ZK layer introduces a new modality on judgments. Define:

```
ZK(Δ ⊢ C)  :=  ∃p. verify(Δ, C, p) = true
```

Properties:
- **Soundness:** `ZK(Δ ⊢ C) ⟹ ∃x. Δ ⊢ x : C` (with overwhelming probability)
- **Zero-knowledge:** `ZK(Δ ⊢ C)` reveals nothing about which `x` beyond existence
- **Succinctness:** verifying `ZK(Δ ⊢ C)` is sublinear in the size of the derivation
- **Composability:** `ZK(Δ₁ ⊢ C₁)` and `ZK(Δ₂ ⊢ C₂)` compose into `ZK(⟨Δ₁,C₁⟩ ∘ ⟨Δ₂,C₂⟩)` via ZK-Compose

This is analogous to the `□` (box) modality in modal logic — `ZK(J)` asserts `J` holds with cryptographic evidence but without exhibiting the witness. Unlike `□` in S4 (which asserts truth in all accessible worlds), `ZK` asserts existence of a proof in the current world, certified by a computational argument.

In Curry-Howard terms: if proofs are programs and types are propositions, then `ZK(Δ ⊢ C)` means "a program of type `C` exists given resources `Δ`, and I can prove I possess it without exhibiting it." For contract verification, this means proving a contract satisfies a spec without revealing the execution trace.

## The Proof-Theoretic Pipeline

Putting it together, CALC's full pipeline has three layers with decreasing trust requirements:

```
Layer 1: Proof Search (JS)
    Σ; Δ ⊢_search c : C
    Trust: the search algorithm (prover code)

Layer 2: Type Checking (JS)
    checkTerm(c, Δ ⊢ C) = true
    Trust: the type checker (small kernel)

Layer 3: ZK Certification (Rust STARK)
    prove(c, Δ ⊢ C) = p  ⟶  verify(Δ, C, p) = true
    Trust: mathematics (polynomial identity testing, FRI, Fiat-Shamir)
```

Each layer reduces the trusted computing base. Layer 1 can have bugs in search strategy — doesn't matter if Layer 2 catches them. Layer 2 can have bugs in the type checker — doesn't matter if Layer 3 catches them. Layer 3's trust is in the mathematical soundness of STARKs (well-studied, no trusted setup).

This is the **de Bruijn criterion** applied to ZK: separate proof search from proof checking, then make checking itself verifiable by a third party without trusting the checker.

## Relationship to Existing Work

### Detailed comparison

**ZKSMT** (Luick, Berzins, Barbosa, Ozdemir, USENIX Security 2024). A custom VM for verifying SMT proofs in zero knowledge. The VM has fixed phases per proof step (fetch, check rule, check cycle) and dispatches on a `RuleID` to select theory-specific checkers. Supports equality and linear integer arithmetic theories. The proof source is SMT solver output (cvc5, Z3).

*Difference from CALC:* ZKSMT's circuit is a fixed hand-designed VM with SMT-specific opcodes. CALC's circuit is auto-generated from declarative inference rule definitions. ZKSMT operates on classical logic (SMT theories); CALC on intuitionistic linear logic. ZKSMT verifies one proof system (SMT); CALC's calculus-agnostic design means new calculi get ZK verification without circuit changes. Both achieve "ZK proof of a formal proof," but at different levels of generality and with different architectural philosophies (fixed VM vs generated verifier).

**zkPi** (Laufer, Ozdemir, Boneh, ACM CCS 2024). The first zkSNARK for Lean proof terms. Encodes dependent type checking (CIC with inductive constructions) in a circuit. Given a Lean theorem T and proof P, produces a zkSNARK that P is valid without revealing P. Constant verification time. Works on 57.9% of Lean stdlib and 14.1% of mathlib.

*Difference from CALC:* zkPi is the closest existing work in spirit — both certify proof terms via ZK. The distinction is architectural: zkPi builds a circuit encoding for Lean's CIC type checker (a specific, complex type theory); CALC derives the circuit from declarative rule definitions (any sequent calculus). zkPi's circuit is Lean-specific and cannot verify proofs in other systems; CALC's verifier is calculus-agnostic. Additionally, Lean's CIC is structural (weakening and contraction are free); ILL is substructural (resource-sensitive), which creates a fundamentally different bus architecture — CONTEXT_BUS multiset equality has no analog in zkPi.

**ZK-ProVer** (ePrint 2025/1152). Certifies SAT/UNSAT verification results in ZK. For UNSAT results (property holds for all inputs), encodes the SAT solver's resolution proof as a PLONKish circuit. Hides the program being verified.

*Difference from CALC:* ZK-ProVer encodes opaque resolution proofs (propositional, classical). CALC encodes ILL derivation trees with explicit structural content (linearity via CONTEXT_BUS, controlled weakening via DISCARD_BUS). ZK-ProVer uses a fixed zkVM; CALC auto-generates the verifier. The proof objects are at different abstraction levels: resolution steps vs sequent calculus inference steps.

**Lurk** (Protocol Labs / Argument Computer Corp). A Turing-complete Lisp where any program gets a ZK proof of its evaluation via Nova IVC (later SuperNova/NIVC). A proof checker written in Lurk would get ZK certification "for free."

*Difference from CALC:* Lurk is a universal-interpreter approach — one circuit for Lisp evaluation, write anything in Lisp. CALC builds purpose-specific circuits from rule definitions. Lurk's overhead is the interpreter tax: a Lurk evaluation step is expensive in constraints because the circuit must handle any Lisp expression. CALC's per-rule chips are narrow and specialized (2-32 columns per rule type). For proof term type-checking specifically, CALC's approach is orders of magnitude more efficient.

**CirC** (Ozdemir, Wahby, Whyte, Boneh, IEEE S&P 2022). Shared compiler infrastructure mapping high-level languages (C, Python, Datalog) to multiple backends (R1CS for ZK-SNARKs, SMT for verification, ILP for optimization) via a unifying "Existentially Quantified Circuits" IR.

*Difference from CALC:* CirC compiles programs to circuits. CALC compiles *inference rules* to circuits. CirC's input is imperative code; CALC's input is a declarative sequent calculus specification. CirC could in principle compile a type-checker program to R1CS, but the resulting circuit would be a generic program circuit, not a rule-aware verifier with buses encoding structural properties.

**Zinnia** (ePrint 2025/572). ZK framework using symbolic execution as a *compiler* technique: the SE engine explores branches and merges them into a single circuit via conditional expressions. 21% smaller circuits, up to 5.8x speedup over zkVMs.

*Difference from CALC:* Zinnia's "symbolic execution" is a circuit compilation optimization — it produces one monolithic circuit for one fixed program. The SE is a means, not an end. CALC's symbolic exploration is the *object being certified*: each symbolic path through the ILL proof search is itself an artifact that receives a STARK certificate. Zinnia does not prove properties about all paths; it uses path merging to build efficient circuits for concrete execution.

**Certified Symbolic Execution** (Trabish, CPP 2026). Instruments KLEE (LLVM symbolic executor) to emit Rocq/Coq proof certificates alongside analysis. When SE is exhaustive and finds no bugs, a machine-checkable safety proof is generated.

*Difference from CALC:* The closest work in the "certified SE" space. Both produce certificates of exhaustive symbolic analysis. The certificate mechanism differs fundamentally: Trabish produces Coq proof objects checked by an interactive theorem prover (must trust the ITP installation); CALC produces STARK proofs checked by polynomial identity testing (trustless, no software dependency beyond field arithmetic). CALC's certificates are succinct (~200KB regardless of derivation size), composable (recursive STARK-in-STARK), and zero-knowledge. Coq certificates are transparent (reveal the proof) and linear in derivation size. For on-chain or cross-organizational verification, CALC's ZK certificates are deployable; Coq certificates require the counterparty to run a Coq installation.

**ZK-EVM projects** (Polygon zkEVM, Scroll, zkSync, Taiko, Linea). Verify concrete EVM execution traces via STARK/PLONK proofs. Hand-written circuits per EVM opcode.

*Difference from CALC:* See §Certified Symbolic Execution above. zkEVMs verify one concrete trace per proof. CALC verifies all symbolic execution paths. zkEVMs hand-write circuits per opcode; CALC auto-generates circuits from `.rules` definitions. The semantic level is different: zkEVMs encode EVM operational semantics directly as polynomial constraints; CALC encodes EVM semantics as ILL rules and verifies at the logic level. This indirection through ILL gives CALC composability with backward reasoning, type-checking, and other proof-theoretic machinery — at the cost of the encoding overhead.

**AirScript** (0xMiden/air-script). A DSL for writing AIR constraints for STARKs declaratively. Compiles transition functions and boundary constraints to Rust code.

*Difference from CALC:* AirScript operates at the AIR constraint level (state-machine transition rules). CALC operates at the sequent calculus level (inference rules with structural properties). AirScript requires the user to specify what polynomial identities hold on consecutive rows. CALC derives those polynomial identities automatically from declarations like "tensor_r has arity 2, consumes one obligation, produces two obligations, and looks up in FORMULA_BUS." The abstraction gap is significant: AirScript is a constraint DSL; CALC's `deriveZkRuleSpecs` is a proof-theory-to-constraints compiler.

**Runtime Verification / K Framework**. RV published a vision document (2023) proposing a ZK wrapper around their K-based proof checker. The idea: run the proof checker once locally, broadcast a ZK certificate. As of March 2026, this remains a vision document — no deployed system exists.

*Difference from CALC:* Same high-level goal (ZK certification of formal verification results), different status (deployed vs vision). RV's proposed approach would use the K Framework's proof checker as a guest program inside a zkVM — the universal-interpreter approach (like Lurk). CALC's approach avoids the interpreter tax by generating purpose-specific AIR chips from rule definitions.

### Summary table

| System | Proof object | Circuit source | Logic | Agnostic? | Symbolic? |
|---|---|---|---|---|---|
| **ZKSMT** (2024) | SMT proof steps | Hand-designed VM | Classical (SMT) | No | No |
| **zkPi** (2024) | Lean/CIC proof terms | CIC type-checker encoding | Dependent types (CIC) | No | No |
| **ZK-ProVer** (2025) | SAT resolution proofs | Fixed zkVM | Propositional | No | No |
| **Lurk** (2023) | Lisp evaluation | Universal interpreter | Untyped lambda calculus | Partially | No |
| **CirC** (2022) | Program executions | Compiled from source code | N/A (programs) | IR level | No |
| **Zinnia** (2025) | Program executions | SE-compiled circuit | N/A (programs) | No | Compiler only |
| **Certified SE** (2026) | Coq proof objects | N/A (not ZK) | First-order | No | Yes (Coq cert) |
| **ZK-EVM** (various) | Concrete EVM traces | Hand-written per opcode | N/A (operational) | No | No |
| **AirScript** (Miden) | N/A (constraint DSL) | User-written AIR | N/A | Constraint level | No |
| **CALC** | ILL derivation trees | Auto-generated from `.rules` | ILL (substructural) | **Yes** | **Yes (STARK cert)** |

CALC occupies a unique position: it is the only system that is simultaneously calculus-agnostic (verifier derived from declarative rules), substructural (buses encode linearity), and symbolic (per-path STARK proofs covering all execution branches). No other system combines any two of these three properties.

## Open Questions

### Q1: Formalize the modality

Is `ZK(Δ ⊢ C)` a well-behaved modality? Does it satisfy K (`ZK(A → B) → ZK(A) → ZK(B)`)? The recursive composition suggests it does, but the computational soundness error complicates the picture — K holds with probability `1 - 2ε` rather than certainly.

### Q2: Flat path soundness theorem

State and prove: for any flat STARK proof `p` with `verify_flat(Δ, C, p) = true`, there exists a sequence of forward rewriting steps `Δ = S₀ →_{r₁} S₁ →_{r₂} ⋯ →_{rₙ} Sₙ` where each step applies a valid rule from the calculus, and the final multiset `Sₙ` matches `C`. The proof should proceed by extracting the witness from CONTEXT_BUS + GAMMA_BUS + FORMULA_BUS constraints.

### Q3: ZK for extended calculi

The calculus-agnostic design means ZK certification extends to future calculi (multimodal ILL, muMALL, dependent types) without changes to the Rust verifier — only `deriveZkRuleSpecs` needs to handle new rule shapes. Formally characterize which class of sequent calculi admits this auto-generation (conjecture: any calculus whose rules are definable as bus interaction patterns over a content-addressed formula store).

### Q4: Certified symbolic exploration

Currently, each execution path gets its own STARK proof. The recursive composition combines them. An open question: can the exhaustive exploration tree (theory/0001) itself be certified as a single object? This would prove not just "path P_i is valid" for each i, but "ALL paths were explored and each is valid" — a universal statement rather than a conjunction of existentials.

### Q5: Relationship to proof-carrying code

Necula's proof-carrying code (PCC, POPL 1997) established that programs can carry lightweight certificates of safety checkable without trusting the producer. CALC's ZK certificates are a cryptographic analog: instead of a transparent logical proof (PCC), the certificate is a STARK proof (succinct, zero-knowledge, composable). Is there a formal relationship between PCC safety policies and the sequent `Δ ⊢ C` that CALC certifies? Can CALC's framework instantiate PCC-style safety checking for smart contracts — where the "code" is a contract, the "safety policy" is an ILL specification, and the "certificate" is a STARK proof?

### Q6: Completeness of the bus encoding

The bus architecture encodes ILL's structural rules (§Buses as Structural Rules). Is this encoding *complete* — does every structural rule of ILL have a corresponding bus constraint? The current 7 proof-theoretic buses cover linearity, derivation completeness, subformula property, exponentials, controlled weakening, substitution correctness, and eigenvariable condition. Are there structural properties of ILL that escape this encoding? A completeness theorem would strengthen the claim that STARK soundness implies derivation soundness.

## References

- Ben-Sasson, Bentov, Horesh, Riabzev (2018) — Scalable, transparent, and post-quantum secure computational integrity. IACR ePrint 2018/046 (STARKs)
- Haböck (2022) — Multivariate lookups based on logarithmic derivatives. IACR ePrint 2022/1530 (LogUp)
- Luick, Berzins, Barbosa, Ozdemir (2024) — ZKSMT: A VM for Proving SMT Theorems in Zero Knowledge. USENIX Security 2024
- Laufer, Ozdemir, Boneh (2024) — zkPi: Proving Lean Theorems in Zero-Knowledge. ACM CCS 2024; ePrint 2024/267
- ZK-ProVer (2025) — Proving Programming Verification in Non-interactive Zero-Knowledge Proofs. ePrint 2025/1152
- Zinnia (2025) — Expressive, Efficient Zero-Knowledge Framework for General-Purpose Data Analytics. ePrint 2025/572
- Ozdemir, Wahby, Whyte, Boneh (2022) — CirC: Compiler infrastructure for proof systems. IEEE S&P 2022
- Trabish (2026) — Enhancing Symbolic Execution with Machine-Checked Safety Proofs. CPP 2026
- Necula (1997) — Proof-Carrying Code. POPL 1997
- Girard (1987) — Linear Logic. TCS 50(1):1-102
- Watkins, Cervesato, Pfenning, Walker (2004) — CLF. Types for Proofs and Programs, LNCS 3085
- Cervesato, Pfenning (2002) — A Linear Logical Framework. Information and Computation 179(1):19-75
- Andreoli (1992) — Logic Programming with Focusing Proofs in Linear Logic. JLC 2(3):297-347
