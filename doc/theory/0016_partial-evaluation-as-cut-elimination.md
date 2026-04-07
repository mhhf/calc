---
title: "Partial Evaluation as Cut Elimination in SELL"
created: 2026-04-07
modified: 2026-04-07
summary: "SELL subexponential grades are binding-time annotations. Grade-0 composition is partial evaluation via cut elimination. The first Futamura projection — specialize(interpreter, program) = compiled program — instantiates as composeGrade0(evm_rules, bytecode_facts) = per-PC specialized rules. Correctness is free from SELL cut admissibility. Multi-level PE generalizes via the grade semiring."
tags: [linear-logic, partial-evaluation, cut-elimination, graded-types, staging, forward-chaining, proof-theory, QTT, SELL, subexponentials, Futamura]
category: "Forward Chaining"
unique_contribution: "The identification of SELL subexponential grades with partial evaluation binding times, yielding the first Futamura projection for forward-chaining linear logic where specialization = cut elimination and correctness follows from cut admissibility. Distinguished from THY_0015 (which establishes grade-0 as staging) by the concrete PE correspondence: binding-time analysis = grade annotation, specialization = cut, residual program = composed rules, Futamura projections = iterated cut elimination."
references:
  - "THY_0014 — Compile-Time Evaluation of the Indexed Monad"
  - "THY_0015 — Grade-0 Staging and Stratified Cut Elimination"
  - "TODO_0156 — Grade-0 cut elimination (linear composition)"
  - "TODO_0162 — Grade-0 persistent composition (fact specialization)"
  - "TODO_0160 — First Futamura projection for ILL"
  - "Futamura (1971). Partial Evaluation of Computation Process — An Approach to a Compiler-Compiler."
  - "Jones, Gomard, Sestoft (1993). Partial Evaluation and Automatic Program Generation."
  - "Nigam, Miller (2009). Algorithmic Specifications in Linear Logic with Subexponentials. PPDP."
  - "Atkey (2018). Syntax and Semantics of Quantitative Type Theory. LICS."
  - "Davies (1996). A Temporal Logic Approach to Binding-Time Analysis. LICS."
  - "Glück, Jørgensen (1996). Multi-Level Specialization. Dagstuhl."
  - "Choudhury, Eades, Eisenberg, Weirich (2021). A Graded Dependent Type System with a Usage-Aware Semantics. POPL."
  - "Kovács (2023). Staged Compilation with Two-Level Type Theory. POPL."
  - "Abiteboul, Hull, Vianu (1995). Foundations of Databases."
---

# Partial Evaluation as Cut Elimination in SELL

## 1. The Correspondence

THY_0015 established that grade-0 is a staging annotation and that cut elimination stratifies by grade. This document identifies the precise correspondence with partial evaluation (PE) and derives the Futamura projections.

### 1.1 Grades as binding times

| PE concept | SELL realization |
|---|---|
| Static (known at specialization time) | Grade 0 (`!_0`) |
| Dynamic (known at execution time) | Grade ω (`!_ω`) / Grade 1 (linear) |
| Binding-time annotation (BTA) | Grade annotation on types/facts |
| Specialization | Cut elimination on grade-0 formulas |
| Residual program | Composed rules (grade-0 eliminated) |
| Unfolding a static call | Resolving a grade-0 persistent goal |
| Static data | Grade-0 clause facts (`!_0 P args.`) |
| Residual expression | Remaining metavariables in composed rule |

The key structural match: in offline PE, BTA marks each value as S (static) or D (dynamic), then the specializer evaluates S-parts and preserves D-parts. In our system, `!_0` marks facts as static, `composeGrade0` evaluates them via cut, and the remaining rule (with unresolved metavariables) is the residual.

### 1.2 Two modes of PE in cut elimination

Our system performs two kinds of grade-0 cut, corresponding to two PE operations:

**Linear composition** (`composePair`): a producer rule's grade-0 output is unified with a consumer rule's grade-0 input. This is **function unfolding** — inlining the producer into the consumer, eliminating the intermediate type.

```
Producer: Γ₁ -o {!_0 M(ā)}     Consumer: !_0 M(x̄) ⊗ Γ₂ -o {Δ}
────────────────────────────────────────────────────────────────── cut₀
                    Γ₁ ⊗ Γ₂[ā/x̄] -o {Δ[ā/x̄]}
```

**Persistent specialization** (`specializePersistent`): a grade-0 ground fact resolves a persistent goal in a rule. This is **constant folding** — substituting a known value into a parameterized rule.

```
Fact: !_0 P(c̄)     Rule: ... ⊗ !P(x̄) -o {Δ}
──────────────────────────────────────────────── dereliction₀
           ...[c̄/x̄] -o {Δ[c̄/x̄]}
```

The distinction is important: linear composition is multiplicative cut (both sides consumed), persistent specialization is exponential dereliction (fact shared across all consumers, each gets a specialized copy).

### 1.3 Correctness from cut admissibility

In traditional PE, correctness requires a separate proof: `⟦specialize(P, s)⟧(d) = ⟦P⟧(s, d)`. Our system gets this for free:

**Theorem (soundness of grade-0 PE):** For any initial state S containing no grade-0 resources:
```
reachable(S, composed_rules) = reachable(S, original_rules)
```

*Proof sketch:* Each grade-0 composition step is a cut on a grade-0 formula. By SELL cut admissibility (Nigam-Miller 2009), the composed sequent is derivable iff the original is. Since S has no grade-0 resources, the grade-0 types serve only as intermediate channels between rules — channels that cut elimination fuses. □

This is stronger than traditional PE correctness: it's not just input-output equivalence but full reachability equivalence — every state reachable by the original rules is reachable by the composed rules, and vice versa. The proof is a one-line appeal to cut admissibility rather than a custom argument.

## 2. The Futamura Projections

### 2.1 Setup

- **Interpreter** I = EVM forward rules (generic execution model)
- **Program** P = contract bytecode, encoded as grade-0 facts `!_0 arr_get bc PC OP`
- **Input** D = runtime state (stack, memory, gas, storage) — grade-1 and grade-ω resources
- **Specializer** S = `composeGrade0` (grade-0 cut elimination)

### 2.2 First projection: specialize(I, P) = compiled program

```
S(I, P) = composeGrade0(evm_rules ∪ bytecode_facts) → per-PC specialized rules
```

The result: for each reachable PC in the contract, a specialized rule with the opcode, gas cost, and immediate data hardcoded. No runtime bytecode lookup.

```ill
% Generic rule (interpreter):
evm/add: !_0 step 0x01 PC' 3 GAS' * stack [A, B | REST] -o { ... }.

% After composing with step/make + decode/raw + !_0 arr_get bc 2 0x01:
evm/add:step/make:decode/raw:bc[2]:
  pc 0x02 * gas GAS * !checked_sub GAS 3 GAS' * stack [A, B | REST]
  -o { pc 0x03 * gas GAS' * ... }.
```

This is implemented by TODO_0160 as a three-stage DAG:
1. `step` (linear composition via `composePair`)
2. `is_push/is_dup/is_swap` (persistent specialization via `specializePersistent`)
3. `arr_get` (persistent specialization, contract-specific facts)

### 2.3 Second projection: specialize(S, I) = compiler

Fixing the interpreter I (EVM rules), S becomes a function `P ↦ S(I, P)` — a **compiler** from EVM bytecode to specialized forward rules. No new machinery needed: the composition framework with EVM rules loaded is already this compiler.

### 2.4 Third projection: specialize(S, S) = compiler generator

This requires S to be expressible as data that S can operate on — reflection. The composition rules would need to be forward rules themselves, operating on rule representations. This is a tower of meta-levels. Future work, but the grade semiring provides the staging structure: grade-0 rules that compose grade-1 rules, meta-grade-0 rules that compose grade-0 rules, etc.

## 3. Multi-Level PE via Grade Extension

### 3.1 The standard two-level case

Traditional PE: S (static) and D (dynamic).
Our system: grade 0 (compile-time) and grade ω (runtime).

### 3.2 Three-level specialization

Extend the grade semiring to {0, 1, ω} with full staging semantics:

| Grade | Binding time | Known when | EVM example |
|---|---|---|---|
| 0 | Deploy-time | Contract deployed | Bytecode, is_push table |
| 1 | Transaction-time | Specific call | Calldata, msg.sender |
| ω | Symbolic | Explored | Storage, stack (post-branch) |

Three specialization stages, each cutting away one level:
1. **Deploy-time PE** (grade 0 → eliminated): specialize against bytecode → per-contract rules
2. **Transaction-time PE** (grade 1 → consumed): specialize against calldata → per-call rules
3. **Symbolic execution** (grade ω → explored): `explore.js` on remaining unknowns

This is multi-level PE (Glück-Jørgensen 1996) realized in SELL. The grade semiring provides the staging order; cut elimination at each grade is the specialization step.

### 3.3 Generalization to arbitrary grade semirings

The correspondence generalizes: for any grade semiring (R, +, ·, 0, 1) with a partial order ≤, grades below a threshold t are "static" and grades above are "dynamic." Stratified cut elimination by grade (THY_0015 §2) performs PE at each level.

This opens a design space: custom grade semirings for domain-specific staging. The natural numbers ℕ give unbounded staging levels. The tropical semiring (ℕ ∪ {∞}, min, +) gives cost-sensitive staging. The information flow lattice gives security-level-aware PE.

## 4. Novel Properties of Proof-Theoretic PE

### 4.1 Specialization preserves linearity

Traditional PE produces a residual program with no resource guarantees. Our PE produces residual forward rules that are still linear logic formulas — they still consume and produce linear resources correctly.

Gas accounting, stack manipulation, memory operations all remain sound after specialization because cut elimination preserves the logical structure. The specialized rule `evm/add:...:bc[2]` has the same resource behavior as the original — fewer metavariables, but identical consumption/production pattern on dynamic resources.

### 4.2 Dead code elimination as proof irrelevance

The closed-world assumption (CWA) on grade-0 facts: if a grade-0 fact database is complete (we have ALL grade-0 facts), then a rule whose grade-0 goal has no matching fact is **unreachable** — its antecedent has no proof.

Erasing such rules is weakening, which is sound for grade 0 (since 0 ∈ W in the SELL signature). DCE falls out of proof theory:
- Unreachable code = hypothesis with no proof
- Erasing it = weakening on grade-0
- Soundness = grade-0 membership in W

### 4.3 Compositional analysis from residual rules

The specialized per-PC rules are the contract's **control flow graph** (CFG) expressed as linear logic. Properties of the CFG become properties of the rule set:
- Dead code: rules with no proof of antecedent (§4.2)
- Basic blocks: maximal chains of rules with single successors
- Loops: back-edges in the rule dependency graph
- Dominance: standard dominator tree on the rule graph

No separate CFG construction needed — it's the residual rule set itself.

### 4.4 Staged computation via lax monad + grades

The lax monad `{A}` provides polarity shift (async → sync). Combined with grades:
- `{!_0 A}` = computation producing a compile-time fact
- Composing through `{!_0 A}` = staged computation

This embeds Davies-Pfenning λ○ (LICS 1996) into SELL: the `□` modality (code type) corresponds to `!_0`, and `letbox` (splice) corresponds to grade-0 cut. The lax monad handles the staging boundary.

## 5. Comparison with Prior Work

| System | Formalism | PE mechanism | Correctness |
|---|---|---|---|
| **Jones-Gomard-Sestoft (1993)** | λ-calculus | Symbolic evaluation | Custom proof |
| **Davies λ○ (1996)** | S4 modal λ | □-elimination | Modal normalization |
| **Kovács 2LTT (2023)** | Two-level TT | Level-0 evaluation | Operational |
| **weval (PLDI 2025)** | WebAssembly | Abstract interpretation | Empirical |
| **This work** | SELL (forward-chaining) | Grade-0 cut elimination | Cut admissibility |

Key distinctions:
- **Forward-chaining**: our rules are multiset rewriting rules, not λ-terms. PE operates on rule sets, not expressions.
- **Linear resources**: the residual program has resource guarantees (gas, stack, memory). No other PE framework preserves linearity.
- **Subexponential grades**: binding times live in the type system's modality structure, not in a separate annotation language.
- **Cut admissibility**: correctness is a corollary, not a theorem requiring custom proof.

## 6. Open Questions

### Automatic BTA via groundness analysis

Can we infer `!_0` automatically? A fact with no metavariables and no runtime dependencies is a candidate for grade-0 promotion. This is offline PE's BTA phase, but for linear logic rules. Novel aspect: **linear BTA**, where some static values are linear (consumed during specialization). No BTA literature addresses this.

### Cross-contract composition (link-time PE)

If contracts A and B are both specialized, compose A's CALL rule with B's entry point. This is link-time optimization — cross-module PE where each module is a specialized rule set. The SELL framework supports this via multi-stratum composition (THY_0013).

### The supercompilation connection

Grade-0 composition + explore = partial evaluation + driving = supercompilation (Turchin 1986, Sørensen-Glück-Jones 1996). Our system does exactly this: compose away known parts (PE), then explore all branches (driving). This is supercompilation for linear logic — with resource-awareness that traditional supercompilation lacks.

### Reflective PE (third Futamura projection)

Requires the composition rules to be expressible as linear logic formulas that the composition framework can operate on. Essentially: a linear logic interpreter for linear logic. The grade semiring provides the staging structure (meta-grade-0 for the self-application level), but the encoding is non-trivial.
