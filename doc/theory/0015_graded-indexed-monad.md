---
title: "The Graded Indexed Monad: QTT Quantities on Monadic Phases"
created: 2026-04-01
modified: 2026-04-01
summary: "The indexed monad {A}_a (THY_0013) carries a QTT quantity q ∈ {0,1,ω}, giving {A}_{q·a} — where grade 0 means compile-time-only (staging), grade 1 means linear runtime, and grade ω means persistent. Grade 0 is meaningful WITHOUT dependent types because it's a staging annotation, not a type-level annotation."
tags: [linear-logic, QTT, graded-types, forward-chaining, lax-monad, semiring, staging, subexponentials, cut-elimination]
category: "Forward Chaining"
unique_contribution: "The observation that QTT's grade-0 quantity is meaningful in forward-chaining ILL WITHOUT dependent types — as a staging annotation ('compile-time only, composed away') rather than a type-level annotation ('exists in types but not computation'). This reinterpretation unifies the indexed monad {A}_a (THY_0013), compile-time composition (THY_0014), and the existing {1,ω} linear/persistent split into a single graded indexed monad {A}_{q·a}."
references:
  - "THY_0013 — The Indexed Lax Monad"
  - "THY_0014 — Compile-Time Evaluation of the Indexed Monad"
  - "RES_0056 — QTT Sequent Calculus and Gap Analysis"
  - "RES_0054 — Graded Resource Analysis for Linear Logic"
  - "RES_0074 — QTT/Graded/Adjoint/SELL/MTDC Expressiveness Hierarchy"
  - "Atkey (2018). Syntax and Semantics of Quantitative Type Theory. LICS."
  - "McBride (2016). I Got Plenty o' Nuttin'."
  - "Brady (2021). Idris 2: QTT in Practice. ECOOP."
  - "Gaboardi, Katsumata, Orchard, Breuvart, Uustalu (2016). Combining Effects and Coeffects via Grading. ICFP."
---

# The Graded Indexed Monad: QTT Quantities on Monadic Phases

## 1. The Three Quantities Already Exist

CALC already implements the {0, 1, ω} semiring, but doesn't name it:

| QTT quantity | CALC concept | Code location |
|---|---|---|
| **1** (linear) | `state.linear` — consumed exactly once | `fact-set.js`, `consumeLinear` |
| **ω** (unrestricted) | `state.persistent` — never consumed, always available | `persistent.js`, `producePersistent` (idempotent) |
| **0** (erased) | `rule.preserved[]` — matched but not consumed or produced (net delta = 0) | `rule-analysis.js:analyzeDeltas`, `match.js:reserved` map |

The `$P` sugar (preserved resources) implements grade-0 at the **rule delta level** — a resource with zero net change per rule firing. But this is not the same as QTT's grade 0.

## 2. Two Interpretations of Grade 0

RES_0056 §10 states: *"Grade 0 requires dependent types to be meaningful. Without dependent types, there ARE no types to mention it in."*

This is correct for **QTT proper**, where grade 0 means "exists in types but not in computation" — you need dependent types for types to mention runtime-erased values.

But in forward-chaining ILL, grade 0 has a different, equally rigorous meaning:

| | QTT grade 0 | Forward-chaining grade 0 |
|---|---|---|
| **Meaning** | Type-level only, erased from computation | Compile-time only, erased from execution |
| **Requires** | Dependent types (types mention erased values) | Staging infrastructure (indexed monad, module algebra) |
| **Mechanism** | Type checker ensures 0-grade values don't appear in terms | Compiler composes away 0-grade types via cut elimination |
| **Violation** | Type error: "using erased variable at runtime" | Composition error: "abstract type M not fully eliminated" |
| **Example** | `id : (0 a : Type) -> a -> a` — `a` erased | `@abstract step : ... type.` — `step` composed away |

**The staging interpretation of grade 0 is meaningful without dependent types.** It needs only:
- The indexed monad `{A}_a` (THY_0013) — provides phases
- Compile-time composition (THY_0014) — evaluates the 0-phase
- Module algebra (TODO 151) — provides the staging infrastructure

## 3. The Graded Indexed Monad `{A}_{q·a}`

THY_0013 defines `{A}_a`: "forward-execute with rules at stratum a to quiescence, return A." We grade the stratum with a QTT quantity:

```
{A}_{0·a}  =  evaluate stratum a at COMPILE TIME, erase, return A
{A}_{1·a}  =  execute stratum a at RUNTIME (linear — consumed once), return A
{A}_{ω·a}  =  execute stratum a at RUNTIME (persistent — reusable), return A
```

This subsumes three constructs:

| Construct | Graded monad instance |
|---|---|
| THY_0013's indexed monad `{A}_a` (runtime execution) | `{A}_{1·a}` |
| THY_0014's compile-time monad (composition) | `{A}_{0·a}` |
| Persistent fact derivation (backward chaining) | `{A}_{ω·a}` (always-available knowledge) |

Two-phase staged execution with compile-time composition is:

```
{B}_{1·target}  ∘  {M}_{0·expansion}
```

The 0-quantity on the expansion phase says: this phase is evaluated at compile time. Its intermediate types are erased. The result feeds into the 1-phase (runtime linear execution).

## 4. Semiring Arithmetic Has Natural Staging Interpretations

The {0, 1, ω} semiring:

```
+  | 0  1  ω        ×  | 0  1  ω
───+────────        ───+────────
0  | 0  1  ω        0  | 0  0  0
1  | 1  ω  ω        1  | 0  1  ω
ω  | ω  ω  ω        ω  | 0  ω  ω
```

**Addition** (combining usages across sub-derivations):
- `0 + 0 = 0` — used at compile time + used at compile time = still compile-time
- `0 + 1 = 1` — compile-time + runtime = runtime (must survive to runtime)
- `1 + 1 = ω` — two linear uses = unrestricted (standard QTT)

**Multiplication** (scaling through binders / stratum boundaries):
- `0 × q = 0` — anything inside a 0-phase is compile-time only
- `1 × q = q` — linear nesting preserves the inner quantity
- `ω × 0 = 0` — persistent use of a compile-time thing is still compile-time
- `ω × 1 = ω` — persistent use of a linear thing = unrestricted

The multiplication rule `0 × q = 0` says: **resources used only through a compile-time phase are themselves compile-time.** This is exactly why composition through a 0-grade type eliminates all traces of that type — the resources "inside" the 0-phase are scaled by 0.

## 5. The QTT Cut Rule IS Composition

QTT's cut (substitution) rule:

```
Γ₁ ⊢ A       Γ₂, x :_ρ A ⊢ C
────────────────────────────────
    Γ₁ + ρ × Γ₂ ⊢ C
```

When ρ = 0 (the cut formula is used 0 times at runtime):
- The result's usage is `Γ₁ + 0 × Γ₂ = Γ₁`... but this isn't quite right for our setting.

For forward rule composition, the analogy is more precise at the **type level**:

- Expansion rule (produces M at grade 0): `Γ_E -o { M * Δ_E }`
- Target rule (consumes M): `M * Γ_T -o { Δ_T }`
- Cut on M (grade 0): the composed rule has `Γ_E * Γ_T -o { Δ_E * Δ_T }`

All resources in Γ_E and Γ_T keep their original grades (1 or ω). Only M (grade 0) disappears. The cut eliminates the 0-grade type and preserves everything else.

## 6. The `@abstract` Annotation = Grade 0 on Type Declarations

The practical syntax:

```ill
@abstract step : bin -> bin -> bin -> bin -> type.
```

This declares `step` as a grade-0 type. The compiler:

1. **Identifies** all rules producing/consuming `step` (from module membership)
2. **Composes** each (producer, consumer) pair via multiplicative cut
3. **Verifies** no `step` tokens remain in the composed rules
4. **Reports error** if `step` appears in initial states or goals (grade violation: using a 0-grade type at runtime)

Compared to the explicit `simplify(T, E)` syntax:
- `simplify` requires the user to separate rules into two groups (target, expansion)
- `@abstract` requires only a type annotation — the compiler finds the rules automatically
- Both produce the same result; `@abstract` is the declarative version

The two are equivalent when the abstract type has a single expansion module:
```
@abstract M  ≡  simplify(everything_consuming_M, everything_producing_M)
```

## 7. Reduction of Existing Concepts

| Existing concept | QTT {0,1,ω} reduction |
|---|---|
| Linear resource `P` | Grade-1 resource |
| Persistent fact `!P` | Grade-ω resource |
| `$P` preserved sugar | Grade-1 resource with net-zero delta per rule (NOT grade 0) |
| `@abstract M` type | Grade-0 type declaration |
| `simplify(T, E)` | Evaluate grade-0 types via cut elimination |
| `qui(X)` | Iterate grade-0 evaluation to fixed point |
| `{A}_a` indexed monad | `{A}_{1·a}` (grade-1 runtime phase at stratum a) |
| Compile-time monad (THY_0014) | `{A}_{0·a}` (grade-0 compile-time phase at stratum a) |
| Module union `A + B` | Grade-preserving rule set union |
| Module subtract `A - B` | Remove rules from active set |
| SELL subexponential `!_a` | Grade-ω resource at stratum a |

## 8. What New Doors Open

### 8.1 Cross-stage persistent fact specialization

Currently, `!arr_get BC PC OP` is resolved at runtime by backward chaining. If BC (the bytecode) is known at compile time (e.g., for a specific contract), the `!arr_get` facts could be resolved during composition, hardcoding the opcodes into the composed rules. This is **grade-0 evaluation of persistent facts** — a deeper form of partial evaluation where compile-time-known persistent facts participate in composition.

### 8.2 Multi-stage compilation towers

Not just 0→1 (compile→run), but 0→0'→1:

```ill
@abstract(priority=1) raw_opcode : bin -> type.     % eliminated first
@abstract(priority=2) step : bin -> bin -> type.     % eliminated second

% Stage 0a: raw_opcode → step (compose opcodes into dispatch steps)
% Stage 0b: step → base types (compose dispatch into final rules)
% Stage 1: execute composed rules
```

Multiple grade-0 phases form a **tower of compile-time stages**, each eliminating one layer of intermediate types. The priority/dependency order determines the composition sequence (DAG condition from THY_0014 guarantees termination).

### 8.3 Grade-aware dead code detection

If a type is declared `@abstract` (grade 0) but no rule consumes it, the expansion rules producing it are dead code. Grade analysis detects this statically.

### 8.4 Affine and bounded-reuse resources (future)

The {0,1,ω} semiring extends naturally:
- **Affine** (grade ≤ 1): resource can be dropped but not duplicated
- **Bounded reuse** (grade n): resource can be used exactly n times
- **Interval bounds** [lo, hi]: resource used between lo and hi times

These require engine changes (RES_0054) but the conceptual framework is the same semiring.

## 9. Interaction with SELL (TODO 151)

THY_0013's indexed monad `{A}_a` is indexed by stratum label a (from SELL). The graded monad adds a second index q (from QTT). These are orthogonal:

- **Label a** (SELL): which rules are visible (structural: which zone of the proof state)
- **Quantity q** (QTT): how the type is used (0 = compile-time, 1 = linear, ω = persistent)

A forward rule carries BOTH: its label (from `@module` / `@label`) and the quantity of its types (from `@abstract` / `!` / default-linear).

In the Glad system (Hanukaev & Eades, TyDe 2023), each mode (= SELL label) carries its own graded semiring. Our system is simpler: one semiring {0,1,ω} shared across all strata, with labels providing the structural partitioning.

## 10. Open Questions

### Is grade 0 the right staging mechanism?

Grade 0 gives us a clean binary: compile-time (0) or runtime (1/ω). But real staging systems often have more than two levels (MetaOCaml: arbitrary nesting of brackets). Is there a natural extension where grades from a richer semiring give multi-level staging? The tower of 0-phases (§8.2) is one approach, but it requires explicit priority ordering.

### How does grade 0 interact with focusing?

Andreoli focusing partitions connectives by polarity. A grade-0 type is "compile-time positive" — it can be focused on during composition but doesn't participate in runtime focusing. Does a grade-aware focusing discipline exist? This is open (noted in RES_0054 §9).

### Can grades be inferred from rule structure?

Given a set of forward rules, can we automatically detect which types should be grade 0? This is a form of **binding-time analysis** (BTA). The sufficient condition: a type M is inferrably grade-0 if (1) no rule both produces and consumes M, and (2) M doesn't appear in initial states or goals. This is the bipartite condition from THY_0014.

### What about grade-0 persistent facts?

A persistent fact `!P` at grade 0 would be a compile-time-only axiom — available for backward chaining during composition but erased before runtime. This could model compile-time assumptions: "for this contract, slot 0 always holds the owner address." The backward chainer resolves `!storage(0, owner)` during composition, hardcoding the result.

## 11. References

- THY_0013 — The Indexed Lax Monad
- THY_0014 — Compile-Time Evaluation of the Indexed Monad
- RES_0054 — Graded Resource Analysis for Linear Logic
- RES_0056 — QTT Sequent Calculus and Gap Analysis (§10 corrected here)
- RES_0074 — QTT/Graded/Adjoint/SELL/MTDC Expressiveness Hierarchy
- Atkey, "Syntax and Semantics of Quantitative Type Theory" (LICS 2018)
- McBride, "I Got Plenty o' Nuttin'" (2016)
- Brady, "Idris 2: QTT in Practice" (ECOOP 2021)
- Gaboardi, Katsumata, Orchard, Breuvart, Uustalu, "Combining Effects and Coeffects via Grading" (ICFP 2016)
- Moon, Eades, Orchard, "Graded Modal Dependent Type Theory" (ICFP 2021)
- Hanukaev & Eades, "Combining Dependency, Grades, and Adjoint Logic" (TyDe 2023)
- Cockett, "Deforestation, Program Transformation, and Cut-Elimination" (ENTCS 2001)
- Vollmer, Marshall, Eades, Orchard, "A Mixed Linear and Graded Logic" (CSL 2025)
