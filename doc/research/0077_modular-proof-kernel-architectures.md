---
title: "Modular Proof Kernel Architectures"
created: 2026-03-03
modified: 2026-03-03
summary: "Survey of architectural patterns in proof assistants and logic engines: kernel separation, LCF/De Bruijn approaches, plugin systems, proof certificates, multi-logic frameworks, and minimalist design"
tags: [architecture, proof-theory, implementation, prover-architecture, focusing, logical-framework, kernel, LCF, proof-assistants, research, clf, Ceptre, Celf]
category: "Implementation"
---

## 1. Two Foundational Trust Models

### 1.1 The LCF Architecture (Milner, 1972)

**Core idea:** Represent theorems as values of an abstract ML type `thm`. The only way to construct a `thm` is through a fixed set of primitive inference rule functions. The language's type system enforces that no code outside the kernel can fabricate a theorem.

**Concrete pattern:**

```
(* kernel.ml — the ONLY module that can construct thm values *)
type thm = Thm of sequent          (* abstract outside this module *)

val axiom       : sequent -> thm              (* axiom introduction *)
val modusPonens : thm -> thm -> thm           (* A->B, A |- B *)
val instantiate : thm -> term -> thm          (* forall elimination *)
(* ... ~10 primitive rules total *)
```

Tactics, automation, decision procedures are all *untrusted* — they are ML functions of type `... -> thm` that must ultimately call kernel primitives. A buggy tactic cannot produce a false theorem; it can only fail or loop.

**Systems:** HOL Light (~400 LOC OCaml kernel, 3 axioms, 10 inference rules), HOL4, Isabelle/Pure, original LCF.

**Key property:** No proof objects stored in memory. The abstract type enforces correctness at construction time.

### 1.2 The De Bruijn Criterion (Automath, 1968)

**Core idea:** The prover produces explicit proof objects (proof terms). An independent, small checker verifies that each proof term is well-typed. The proof generator and the proof checker are completely separate programs.

**Concrete pattern:**

```
PROVER                          CHECKER
  |                                |
  | generates proof term t         |
  | for theorem P                  |
  +------> [ proof term t ] ------>|
                                   | type-checks: |- t : P
                                   | accept/reject
```

**Systems:** Coq/Rocq (kernel type-checks CIC terms), Lean (kernel type-checks CIC terms), Agda, Metamath.

**Key property:** Proof objects are persistent and checkable by independent implementations. Coq's kernel is ~10K LOC OCaml; MetaCoq has formally verified a checker in Coq itself.

### 1.3 Comparison

| Dimension | LCF | De Bruijn |
|---|---|---|
| Proof storage | No proof objects (only `thm` values) | Full proof terms |
| Trust boundary | Abstract type in one language | Interface between prover and checker |
| Independent verification | Requires re-proving | Re-check the term with any checker |
| Memory | Low — only theorems retained | Can be enormous (megabytes per proof) |
| Extensibility | Any ML function can be a tactic | Checker is fixed; prover is arbitrary |
| Bug in tactic | Cannot produce false `thm` | Proof term won't type-check |

Both approaches can coexist: Isabelle follows LCF but can optionally export proof terms. Lean follows De Bruijn but lazily evaluates proof terms and doesn't load them when importing modules.


## 2. How Specific Systems Separate Kernel from Optimization

### 2.1 Coq/Rocq

**Layered architecture:**

```
┌───────────────────────────────────┐
│  Vernacular / Ltac / Ltac2        │  ← untrusted tactic scripts
├───────────────────────────────────┤
│  Elaboration Engine               │  ← converts surface → CIC terms
│  (implicit arguments, unification,│
│   typeclass resolution, notation) │
├───────────────────────────────────┤
│  Kernel (~10K LOC OCaml)          │  ← type-checking + conversion
│  - typing rules                   │
│  - reduction (beta, delta, iota,  │
│    zeta, match, fix)              │
│  - universe consistency           │
└───────────────────────────────────┘
```

**Optimization toggle pattern — conversion strategies:**
- `simpl` / `cbn` — call-by-name reduction within kernel
- `vm_compute` — bytecode compilation, runs in OCaml VM (faster, but still kernel-level)
- `native_compute` — compiles to native OCaml code via the OCaml compiler (fastest, largest TCB)

These are interchangeable: the theorem statement is the same regardless of which conversion strategy is used. The kernel guarantees the result. However, `vm_compute` and `native_compute` extend the TCB because they rely on the OCaml compiler's correctness.

**Plugin system:** OCaml plugins extend Coq through three macros:
- `VERNAC COMMAND EXTEND` — new top-level commands
- `TACTIC EXTEND` — new tactic primitives
- `DECLARE PLUGIN` — plugin registration

Plugins can add new tactics and commands but cannot bypass the kernel — all proof terms must still type-check. Alternative: Coq-Elpi provides lambda-Prolog-based extension.

### 2.2 Lean 4

**Monad tower architecture:**

```
CoreM        — basic IO + environment read
  ↓ extends
MetaM        — metavariable context, unification, type inference
  ↓ extends
TermElabM    — term elaboration (surface syntax → kernel terms)
  ↓ extends
TacticM      — goal manipulation, proof state
  ↓ extends
CommandElabM — top-level command processing
```

Each monad layer extends the previous. Tactics live in `TacticM`, which extends `MetaM`, which can create metavariables and unify terms. The kernel is a separate type-checker that verifies elaborated terms.

**Extension mechanism:** Lean uses itself for metaprogramming. Macros are `Syntax → MacroM Syntax` functions. Elaborators register via attributes. No separate plugin language — everything is Lean code that runs at elaboration time.

**Kernel optimization:** Lean lazily evaluates proof terms and doesn't load them when importing modules. Proofs of user theorems are typically not needed after checking.

### 2.3 Isabelle

**Two-level architecture:**

```
┌───────────────────────────────────┐
│  Object Logics (HOL, ZFC, FOL)   │  ← defined in Pure
├───────────────────────────────────┤
│  Isar proof language              │  ← structured proofs
├───────────────────────────────────┤
│  Isabelle/Pure metalogic          │  ← ⟹ (meta-implication)
│  (abstract type thm)              │    ⋀ (meta-universal)
│                                   │    ≡ (meta-equality)
├───────────────────────────────────┤
│  ML-level kernel                  │  ← ~2K inference rules
└───────────────────────────────────┘
```

**Key distinction from HOL:** The kernel implements a *logical framework* (Pure), not a specific logic. Object logics (HOL, FOL, ZFC) are defined as theories within Pure. The abstract type `thm` operates at the framework level.

**ML-level extensions:** The simplifier has plug-in interfaces for extra procedures written in ML. Decision procedures, tactics, and proof methods are all ML functions that produce `thm` values through the kernel. The Isar framework provides explicit infrastructure for building derivative systems.

### 2.4 Agda

**Trusted Theory Base (TTB) vs Trusted Code Base (TCB):**

Traditional approach: trust the type-checker implementation (TCB). Agda Core's innovation: the type checker produces *evidence of well-typedness* according to formally specified rules. You need only trust the typing rules themselves (TTB), not the checker implementation.

**Architecture:**

```
Surface Agda → Elaboration → Agda Core (formally specified)
                                ↓
                         Type checker produces
                         derivation evidence
                                ↓
                         Independent checker
                         can verify the evidence
```

**Erasure annotations** (`@0` / `Erased`) separate specification from computation — scoping and typing evidence are erased at runtime.


## 3. CLF / Celf / LolliMon / Ceptre Architectures

### 3.1 CLF and Celf

Celf implements the Concurrent Logical Framework (CLF), which extends LF with linear types (state) and a monad (concurrency).

**Dual-mode execution:**

```
Goal type is ASYNCHRONOUS          Goal type is SYNCHRONOUS
        │                                   │
        ▼                                   ▼
  Backward chaining                   Forward chaining
  (goal-directed,                     (undirected,
   resembles Prolog,                   multiset rewriting,
   backtracking)                       committed choice)
```

Programs can switch between modes by entering/exiting the concurrency monad `{A}`. The monad boundary is the architectural separation point:

```
Γ; Δ ⊢ {S}          ← backward chaining computes Γ; Δ
                       then switches to forward mode for S
```

Inside the monad: forward chaining with committed choice (no backtracking). Outside: backward chaining with full search. This directly mirrors CALC's architecture where `prove.js` does backward chaining and `forward.js`/`symexec.js` do forward chaining.

**Implementation:** SML, uses Andreoli focusing to organize proof search, hereditary substitutions for canonical forms, explicit substitutions and logic variables.

### 3.2 LolliMon (Lopez, Pfenning, Polakow, Watkins)

Extends Lolli (linear logic programming in backward mode) with CLF's monad for forward chaining inside the monad. The connectives of ILL restricted to the monad get committed-choice forward semantics.

**Pattern:** Backward chaining for persistent/intuitionistic reasoning, forward chaining for linear state transitions. The monad `{A}` marks the boundary.

### 3.3 Ceptre (Martens)

**Stage-based architecture:**

```
┌─────────────────────────────┐
│  Stage 1                    │
│  ┌────────────────────────┐ │
│  │ Forward-chaining rules │ │
│  │ (linear multiset       │ │
│  │  rewriting)            │ │
│  └────────────────────────┘ │
│  Runs until QUIESCENCE      │
│  (no more rules apply)      │
└──────────┬──────────────────┘
           ▼
┌─────────────────────────────┐
│  Stage 2                    │
│  (different rule set)       │
│  Runs until QUIESCENCE      │
└──────────┬──────────────────┘
           ▼
          ...
```

**Key patterns:**
1. **Quiescence as phase boundary** — a stage runs until no rules fire, then control passes to the next stage. This enables programming with fixpoints (saturation).
2. **Stages are composable** — each stage has its own rule set. Stages can be interactive (user picks transition) or automatic (random/exhaustive).
3. **Linear vs persistent predicates** — linear predicates are consumed by rules; persistent predicates survive.
4. **Execution traces as proof terms** — program executions are recorded as traces with dependency information, interpreting gameplay as proof search.

**Relevance to CALC:** Ceptre's stage mechanism is analogous to CALC's forward engine running rules to quiescence. The linear/persistent predicate distinction maps directly to CALC's `State = { linear: FactSet, persistent: FactSet }`.


## 4. Foundational Proof Certificates (Miller)

### 4.1 Core Architecture

FPCs use focused sequent calculus (LKF for classical, LJF for intuitionistic) as the proof-checking kernel. The key insight: focusing already organizes proof search into deterministic phases (negative/async) and choice-point phases (positive/sync). Proof certificates encode exactly the choices made at choice points.

**Augmented sequent calculus LKFa:**

```
Standard LKF rule:     ──────────────
                       Γ; Δ ⊢ C

Augmented LKFa rule:   ──────────────
                       Ξ; Γ; Δ ⊢ C

where Ξ is the certificate term (guides choices)
```

### 4.2 The Clerk/Expert Pattern

```
NEGATIVE PHASE (deterministic)         POSITIVE PHASE (choice-required)
  │                                      │
  ▼                                      ▼
CLERK predicates                       EXPERT predicates
  - Store clerk: indexes a              - Decide expert: which formula
    formula when it moves                 to focus on (returns index)
    to the context                      - Initial expert: which stored
  - Conjunction clerk: splits             literal complements the
    certificate for branches              focused literal
  - No backtracking needed             - Quantifier expert: which
                                          witness term to use
```

**Clerks** handle the deterministic parts of proof checking (decomposing negative connectives, storing formulas). They compute — no choices needed.

**Experts** handle the non-deterministic parts (deciding which formula to focus on, choosing witnesses for existentials, selecting clauses). The certificate must provide enough information for the expert to make its choice without search.

### 4.3 Certificate Parameterization

Different proof formats correspond to different clerk/expert definitions:

| Proof Format | What the certificate encodes |
|---|---|
| Resolution proofs | Clause selections + unification witnesses |
| Expansion trees | Which instances of quantified formulas appear |
| Natural deduction | Assumption discharge patterns |
| Sequent calculus | Full rule-by-rule trace |
| "Oracle" / empty | Nothing — checker must search (degenerates to prover) |

The same LKFa kernel checks all formats. Only the clerk/expert specifications change.

### 4.4 Implementation

Implemented in lambda-Prolog, where higher-order unification and lambda-terms provide natural support for binding, substitution, and proof term manipulation. The FPC-Coq project uses ELPI (embeddable lambda-Prolog) to elaborate external proof evidence into Coq proofs.

**Relevance to CALC:** CALC's focusing infrastructure (L3 focused.js) already implements the synchronous/asynchronous phase structure. Proof certificates could be added by threading certificate terms through the focused proof search, with clerks for the invertible phase and experts for the focusing choices.


## 5. Multi-Logic Frameworks

### 5.1 Isabelle's Object Logic Approach

**Mechanism:** Isabelle/Pure provides three meta-level connectives:
- `⟹` (meta-implication) — encodes object-logic rules and discharges assumptions
- `⋀` (meta-universal quantification) — encodes object-logic quantifiers
- `≡` (meta-equality) — encodes definitions and rewrites

Object logics are defined as Isabelle theories that declare constants and axioms in terms of Pure's meta-connectives. Example for first-order logic:

```
consts
  Trueprop :: "o => prop"    (* lifts object-level to meta-level *)
  imp :: "o => o => o"
  all :: "('a => o) => o"

axiom mp: "Trueprop(imp P Q) ⟹ Trueprop P ⟹ Trueprop Q"
axiom allI: "(⋀x. Trueprop(P x)) ⟹ Trueprop(all(%x. P x))"
```

Different logics (HOL, FOL, ZFC) coexist as different theories with different axioms, all sharing the same kernel and proof infrastructure.

### 5.2 Twelf's Meta-Logic Approach

**Mechanism:** Twelf uses LF (the Edinburgh Logical Framework) with dependent types. Object logics are encoded using higher-order abstract syntax (HOAS) — object-level variables become LF variables.

```
tp : type.                          (* object-level types *)
tm : type.                          (* object-level terms *)
of : tm -> tp -> type.              (* typing judgment *)

app : tm -> tm -> tm.
lam : tp -> (tm -> tm) -> tm.       (* HOAS: binding = LF function *)

of/app : of (app E1 E2) T
       <- of E1 (arr T2 T)
       <- of E2 T2.
of/lam : of (lam T1 ([x] E x)) (arr T1 T2)
       <- ({x:tm} of x T1 -> of (E x) T2).
```

Twelf provides meta-theoretic reasoning (M2 meta-logic) for proving properties about encoded systems (e.g., type preservation, progress).

### 5.3 Dedukti's Rewriting Approach

**Mechanism:** Based on lambda-Pi-calculus modulo theory (lambda-Pi/≡). Extends LF with user-defined rewrite rules. Different logics are encoded as different sets of rewrite rules (shallow embeddings).

```
(* Encode simple type theory *)
Sort : Type.
prop : Sort.
Tm : Sort -> Type.

(* Rewrite rules for computation *)
[a, b] Tm (arr a b) --> (Tm a -> Tm b).
```

**Verified imports from:** Zenon, iProver, FoCaLiZe, HOL Light, Matita, Coq. Dedukti serves as a universal proof interchange format — translate into Dedukti from system A, translate out to system B.

### 5.4 Metamath Zero's Sort-Based Approach

**Mechanism:** Many-sorted first-order logic with user-declared sorts. The .mm0 specification declares sorts, terms, axioms. The axiom system is pluggable — you can encode PA, ZFC, HOL, or anything else.

```
sort wff;           -- formulas
sort class;         -- set theory classes
term wi: wff > wff > wff;   -- implication
axiom ax-mp: $ ph $ > $ ps $ > $ ph -> ps $;
```

**Trust model:** Only the .mm0 file is audited. Proof files are untrusted hints. The verifier is small enough to formally verify down to machine code.


## 6. Plugin / Extension Architectures

### 6.1 Pattern Catalog

| System | Extension Mechanism | Trust Impact |
|---|---|---|
| Coq | OCaml plugins (`VERNAC/TACTIC EXTEND`) | No kernel bypass — proofs still type-checked |
| Coq | Ltac / Ltac2 (tactic scripting) | Untrusted — produces proof terms |
| Coq | Coq-Elpi (lambda-Prolog embedding) | Untrusted — produces proof terms |
| Lean 4 | Lean metaprogramming (macros, elaborators, tactics) | Same language, untrusted |
| Lean 4 | Attribute registration (`@[simp]`, `@[ext]`, custom) | Configuration, not kernel extension |
| Isabelle | ML-level procedures (decision procs, simplifier plugins) | Must produce `thm` via kernel |
| Isabelle | Isar method combinators | Compose existing tactics |

### 6.2 Architectural Principle

**The "untrusted extension" pattern:** Extensions can do arbitrary computation but must produce values that pass through the kernel. In LCF systems, this means producing `thm` values via inference rules. In De Bruijn systems, this means producing proof terms that type-check.

This gives a clean separation: the kernel defines *what is valid*, extensions define *how to find it*.


## 7. Minimalist / "Suckless" Approaches

### 7.1 HOL Light

- **Kernel:** ~400 LOC OCaml
- **Axioms:** 3 (extensionality, choice, infinity)
- **Inference rules:** 10 primitive rules
- **Verified:** Candle project compiled HOL Light's kernel to verified machine code via CakeML
- Entire system is extensible via OCaml; new inference rules are derived, not primitive

### 7.2 Metamath / Metamath Zero

- **Metamath:** String-based substitution, ~300 LOC verifier possible
- **MM0:** Tree-based expressions, spec/proof separation, 195ms for 34K theorems
- **Design philosophy:** "Every feature costs 10x when formally proving it, resulting in no frills"
- Self-describing: MM0 specifies x86-64 and its own verification algorithm within PA

### 7.3 Design Principles

1. **Minimal axiom set** — fewer axioms = smaller attack surface
2. **Spec/implementation separation** — the specification is human-auditable; the implementation is machine-checked
3. **Process isolation** — verifier runs as separate process; OS boundaries enforce trust
4. **Verified stack** — verify the verifier, down to machine code if possible
5. **No implicit trust in tooling** — compilers, runtimes, and libraries are in the TCB unless verified


## 8. Patterns for Toggling Optimizations

### 8.1 Coq's Conversion Strategy Pattern

Multiple reduction strategies for the same logical operation:

```
(* Same theorem, different proof strategies: *)
Eval compute in (factorial 10).     (* kernel reduction *)
Eval vm_compute in (factorial 10).  (* bytecode VM *)
Eval native_compute in (factorial 10). (* native OCaml *)
```

All produce the same result; they differ in speed and TCB size. This is a clean "optimization toggle" — you can verify with the slowest/most-trusted strategy and run with the fastest.

### 8.2 Lean's Lazy Proof Terms

Proof terms are lazily evaluated and not loaded when importing modules. This is an optimization that doesn't affect correctness — if you want to re-check, you can force evaluation.

### 8.3 CCIC Pattern (Blanqui, Strub)

The Calculus of Congruent Inductive Constructions integrates external decision procedures into kernel conversion via proof certificates:

```
Kernel conversion check: t₁ ≡ t₂?
  │
  ├─ try: internal reduction
  │
  └─ try: ask external SMT solver for certificate
         └─ small checker verifies certificate
            └─ kernel accepts if certificate checks
```

The external solver is untrusted; only the certificate checker must be correct. This allows adding powerful arithmetic reasoning without enlarging the kernel.

### 8.4 The FFI-as-Optimization Pattern (relevant to CALC)

CALC already implements this: persistent predicates have both backward clause definitions (the semantics) and optional FFI fast-paths (the optimization). Turning FFI off falls back to clause resolution — slower but correct.

```
provePersistentGoals:
  1. Try FFI           ← optimization, can be disabled
  2. Try state lookup  ← core
  3. Try clause resolution ← core semantics (always correct)
```

This is analogous to Coq's conversion strategies: multiple implementation strategies for the same logical operation, differing in speed and trust.


## 9. Key Architectural Patterns Summary

### Pattern 1: Abstract Type Kernel (LCF)
Theorems as abstract type values. Extensions must produce values through kernel constructors. Type system enforces soundness.

### Pattern 2: Proof Certificate Kernel (De Bruijn / FPC)
Separate proof generation from proof checking. Certificates encode choices; a small checker verifies them against focused proof rules. Clerk/expert separation within the checker.

### Pattern 3: Logical Framework (Isabelle Pure / LF / Dedukti)
Define a meta-logic; encode object logics as theories within it. Multiple logics share one kernel. Rewriting (Dedukti) or HOAS (Twelf) for encoding.

### Pattern 4: Monad Boundary (CLF / Celf / LolliMon)
A monad `{A}` separates backward chaining (goal-directed, outside monad) from forward chaining (committed-choice, inside monad). The boundary is the architectural cut point.

### Pattern 5: Stage/Phase Organization (Ceptre)
Rules grouped into stages. Each stage runs to quiescence (saturation). Stages compose sequentially. Clean separation of rule sets.

### Pattern 6: Spec/Proof Separation (MM0)
Two files: human-auditable specification (axioms + theorem statements) and machine-consumed proof hints. The spec alone determines correctness.

### Pattern 7: Untrusted Extension with Kernel Gate
Any extension mechanism (plugins, tactics, macros, FFI) is untrusted. All results must pass through the kernel gate. Optimizations are interchangeable strategies behind the same logical interface.

### Pattern 8: TCB-to-TTB Shift (Agda Core / MetaCoq)
Instead of trusting the implementation (TCB), formally specify the typing rules and have the checker produce evidence of rule-following. Trust the theory (TTB), not the code.


## References

- Paulson, L.C. "The de Bruijn criterion vs the LCF architecture" (2022). https://lawrencecpaulson.github.io/2022/01/05/LCF.html
- Miller, D. "Foundational Proof Certificates" (2013-2014). https://www.lix.polytechnique.fr/Labo/Dale.Miller/ProofCert/
- Miller, D. "Checking foundational proof certificates for first-order logic" (2013). https://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/checking-fpc.pdf
- Carneiro, M. "Metamath Zero: Designing a Theorem Prover Prover" (2019). https://github.com/digama0/mm0
- Schack-Nielsen, A. and Schurmann, C. "Celf — A Logical Framework for Deductive and Concurrent Systems" (2008). https://clf.github.io/celf/
- Martens, C. "Ceptre: A Language for Modeling Generative Interactive Systems." https://www.cs.cmu.edu/~cmartens/thesis/4-ceptre_lang.pdf
- Cockx, J. "Agda Core: The Dream and the Reality" (2024). https://jesper.cx/posts/agda-core.html
- Pfenning, F. and Schurmann, C. "System Description: Twelf — A Meta-Logical Framework for Deductive Systems" (1999). https://www.cs.cmu.edu/~fp/papers/cade99.pdf
- Assaf et al. "Dedukti: a Logical Framework based on the lambda-Pi-Calculus Modulo Theory." https://deducteam.github.io/
- de Moura, L. and Ullrich, S. "The Lean 4 Theorem Prover and Programming Language" (2021). https://pp.ipd.kit.edu/uploads/publikationen/demoura21lean4.pdf
- Harrison, J. "HOL Light: An Overview." https://github.com/jrh13/hol-light
- Paulson, L.C. "From LCF to Isabelle/HOL" (2019). https://arxiv.org/pdf/1907.02836
- Lopez, P. et al. "Monadic concurrent linear logic programming" (2005). LolliMon.
- Sozeau, M. et al. "Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq" (2020).
