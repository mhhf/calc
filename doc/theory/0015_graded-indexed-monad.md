---
title: "The Graded Indexed Monad: QTT Quantities on Monadic Phases"
created: 2026-04-01
modified: 2026-04-01
summary: "The {0,1,ω} semiring grades resource types independently of the indexed monad — grade 0 means compile-time-only (staging), grade 1 means linear runtime, grade ω means persistent. When combined with the indexed monad {A}_a, this gives {A}_{q·a}. The graded semiring stands alone; the indexed monad is orthogonal. Grade 0 is meaningful WITHOUT dependent types as a staging annotation."
tags: [linear-logic, QTT, graded-types, forward-chaining, lax-monad, semiring, staging, subexponentials, cut-elimination, proof-theory]
category: "Forward Chaining"
unique_contribution: "Three contributions: (1) QTT's grade 0 is meaningful in forward-chaining ILL WITHOUT dependent types — as a staging annotation, not a type-level annotation. (2) The graded semiring {0,1,ω} on type declarations is standalone — it does not require the indexed monad's phase structure, only a compiler that eliminates grade-0 types via cut. The indexed monad adds orthogonal phase/stratum structure. (3) Stratified cut elimination: grade-0 cuts are eliminated at compile time, grade-1 at runtime, grade-ω never — a novel phased procedure not named in the literature (see RES_0102)."
references:
  - "THY_0013 — The Indexed Lax Monad"
  - "THY_0014 — Compile-Time Evaluation of the Indexed Monad"
  - "RES_0056 — QTT Sequent Calculus and Gap Analysis"
  - "RES_0054 — Graded Resource Analysis for Linear Logic"
  - "RES_0074 — QTT/Graded/Adjoint/SELL/MTDC Expressiveness Hierarchy"
  - "RES_0102 — Stratified and Phased Cut Elimination (literature survey)"
  - "Atkey (2018). Syntax and Semantics of Quantitative Type Theory. LICS."
  - "McBride (2016). I Got Plenty o' Nuttin'."
  - "Brady (2021). Idris 2: QTT in Practice. ECOOP."
  - "Gaboardi, Katsumata, Orchard, Breuvart, Uustalu (2016). Combining Effects and Coeffects via Grading. ICFP."
  - "Girard, Scedrov, Scott (1992). Bounded Linear Logic. TCS."
  - "Vollmer, Marshall, Eades, Orchard (2025). A Mixed Linear and Graded Logic. CSL."
  - "Baillot, Mazza (2010). Linear Logic by Levels. TCS."
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
| **Requires** | Dependent types (types mention erased values) | Type declarations with quantity annotations + a compiler that eliminates grade-0 types |
| **Mechanism** | Type checker ensures 0-grade values don't appear in terms | Compiler composes away 0-grade types via cut elimination |
| **Violation** | Type error: "using erased variable at runtime" | Composition error: "abstract type M not fully eliminated" |
| **Example** | `id : (0 a : Type) -> a -> a` — `a` erased | `@abstract step : ... type.` — `step` composed away |

**The staging interpretation of grade 0 is meaningful without dependent types.** It needs only:
1. **Type declarations with grade annotations** — `@abstract M : ... type.` declares M as grade-0
2. **A compilation step** that performs cut elimination on grade-0 types (composing producer/consumer rule pairs)
3. **A static check** that no grade-0 types remain after compilation

Note: the graded semiring {0,1,ω} on type declarations is **standalone**. It does not require the indexed monad `{A}_a` (THY_0013) or its phase/stratum structure. The indexed monad adds an orthogonal dimension (which rules fire when); the semiring adds another (which types survive to runtime). They compose naturally (§3) but neither depends on the other.

## 3. The Graded Indexed Monad `{A}_{q·a}`

The graded semiring (§2) and the indexed monad (THY_0013) are orthogonal:

| Dimension | Source | What it governs |
|---|---|---|
| **Quantity q ∈ {0,1,ω}** | QTT semiring | *When* a type exists: compile-time (0), linear runtime (1), persistent (ω) |
| **Stratum label a** | SELL / indexed monad | *Where* rules are visible: which phase/module/scope |

When combined, they give `{A}_{q·a}`: "execute rules at stratum a with quantity q."

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

## 5. Proof Theory of the Graded Semiring

### 5.1 Graded Cut Rule

The graded cut rule for forward-chaining ILL. A cut on type M at grade q:

```
Γ₁ ⊢ M ⊗ Δ₁       M ⊗ Γ₂ ⊢ Δ₂
─────────────────────────────────── cut_q(M)
        Γ₁ ⊗ Γ₂ ⊢ Δ₁ ⊗ Δ₂
```

The grade q determines **when** the cut is performed:

| Grade | Cut behavior | When eliminated |
|---|---|---|
| **0** | M is erased — entire sub-derivation producing M is composed away | Compile time |
| **1** | M is consumed linearly — standard multiplicative cut | Runtime (forward execution) |
| **ω** | M is persistent — available to all consumers, never consumed | Never (persists as axiom) |

Grade-0 cut corresponds to the **weakening** case in BLL (Girard-Scedrov-Scott 1992): the cut formula is used 0 times, so both the producer and consumer derivations are "fused" without the intermediate type. In standard ILL this is forbidden (no weakening on linear types), but grade 0 explicitly permits it — it is a type that was only ever meant to be an intermediate.

### 5.2 Stratified Cut Elimination (Novel)

**Claim:** Cut elimination in graded ILL can be performed in phases, stratified by grade:

1. **Phase 0 (compile time):** Eliminate all cuts on grade-0 types. Each grade-0 cut composes a producer rule with a consumer rule, yielding a rule that doesn't mention the grade-0 type. After phase 0, no grade-0 types remain.

2. **Phase 1 (runtime):** Eliminate grade-1 cuts by forward execution — the standard multiset rewriting semantics. Each rule firing consumes grade-1 resources and produces new ones.

3. **Phase ω (persistent):** Grade-ω resources are never cut-eliminated. They persist as axioms available to all derivations.

**Invariant:** At each phase boundary, the proof is cut-free at all lower grades. After phase 0, no grade-0 types exist. After phase 1, all linear resources are consumed. Grade-ω facts remain.

**Termination by phase:**
- Phase 0 terminates when the internal-type dependency graph is a DAG (THY_0014 §4). The bipartite condition (grade-0 types are only produced by expansion rules, only consumed by target rules) guarantees one round.
- Phase 1 terminates when the forward rule set reaches quiescence (application-dependent, same as standard forward chaining).
- Phase ω trivially "terminates" — nothing to eliminate.

**Novelty:** RES_0102 surveys all known work on stratified cut elimination. No paper states this as a named theorem. The closest results:
- Baillot-Mazza (2010): level-indexed cut elimination for light logics — motivated by complexity bounds, not staging
- Davies (1996): "normalization can be done in stage order" — an observation about λ-calculus, not a sequent calculus theorem
- Kovács 2LTT (2022): two-phase staging algorithm — algorithmic, not proof-theoretic
- BLL (1992): grade-bounded duplication — complexity, not phased elimination

### 5.3 Soundness of Phase-0 Elimination

Grade-0 cut elimination is sound (produces equivalent reachable states) when:

1. **Completeness:** Every grade-0 type M is fully eliminated — no M tokens remain in the composed rule set. (If not, composition error.)
2. **Conservative extension:** The grade-0 types don't appear in initial states or goals. (If they did, erasing them changes the problem.)
3. **Determinism of composition:** For each (producer, consumer) pair, the multiplicative cut has a unique result. (Guaranteed by linearity — each M token is consumed exactly once.)

Under these conditions, for all base-type initial states S:

> reachable(S, composed_rules) = reachable(S, original_rules)

This is the compile-time analog of the standard cut-elimination theorem for ILL: eliminating cuts doesn't change what is provable.

### 5.4 Grade-ω as Structural Rule

Grade ω corresponds to the exponential `!` in standard ILL. The structural rules (weakening, contraction) are permitted exactly for grade-ω resources:

- **Weakening:** A grade-ω resource can be ignored (not consumed) — standard `!`-weakening
- **Contraction:** A grade-ω resource can be used multiple times — standard `!`-contraction

The graded semiring unifies these: `ω + ω = ω` (contraction is idempotent), `0 · ω = 0` (compile-time scaling erases even persistent resources).

## 6. Proof Theory of the Indexed Monad

### 6.1 Monadic Let as Cut

The indexed monad's bind operation `{A}_a >>= f` is a form of cut:

```
Γ₁ ⊢ {M}_a       M, Γ₂ ⊢ {B}_b
──────────────────────────────────── monadic cut (bind)
        Γ₁ ⊗ Γ₂ ⊢ {B}_b
```

The intermediate state M is produced by executing stratum a to quiescence, then consumed by stratum b. This is cut on M, mediated by the monad.

### 6.2 Grade-0 Bind = simplify

When the first phase has grade 0:

```
Γ₁ ⊢ {M}_{0·a}       M, Γ₂ ⊢ {B}_{1·b}
────────────────────────────────────────── grade-0 bind
        Γ₁ ⊗ Γ₂ ⊢ {B}_{1·b}
```

The grade-0 bind says: evaluate stratum a at compile time, obtain M, feed it to stratum b. The result is a single-phase runtime computation. This is exactly `simplify(b, a)` from THY_0014.

**Grade-0 bind elimination:** The compiler eliminates grade-0 binds by composing the rules of stratum a into the rules of stratum b. After elimination, stratum a's rules are gone, M doesn't exist at runtime, and stratum b's rules directly compute from base types to results.

### 6.3 How the Two Dimensions Compose

The graded semiring and the indexed monad compose via the product `(q, a)`:

```
{A}_{q·a}  where  q ∈ {0,1,ω}  and  a ∈ Labels
```

Each dimension has its own cut structure:
- **Grade cut** (§5.1): eliminates a type M by fusing producer/consumer — determined by q
- **Stratum cut** (monadic bind, §6.1): sequences two phases a,b — determined by a

The combination: a grade-0 stratum cut (§6.2) is eliminated at compile time. A grade-1 stratum cut is a runtime phase boundary.

## 7. The QTT Cut Rule IS Composition

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

## 8. The `@abstract` Annotation = Grade 0 on Type Declarations

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

## 9. Reduction of Existing Concepts

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

## 10. What New Doors Open

### 10.1 Cross-stage persistent fact specialization

Currently, `!arr_get BC PC OP` is resolved at runtime by backward chaining. If BC (the bytecode) is known at compile time (e.g., for a specific contract), the `!arr_get` facts could be resolved during composition, hardcoding the opcodes into the composed rules. This is **grade-0 evaluation of persistent facts** — a deeper form of partial evaluation where compile-time-known persistent facts participate in composition.

### 10.2 Multi-stage compilation towers

Not just 0→1 (compile→run), but 0→0'→1:

```ill
@abstract(priority=1) raw_opcode : bin -> type.     % eliminated first
@abstract(priority=2) step : bin -> bin -> type.     % eliminated second

% Stage 0a: raw_opcode → step (compose opcodes into dispatch steps)
% Stage 0b: step → base types (compose dispatch into final rules)
% Stage 1: execute composed rules
```

Multiple grade-0 phases form a **tower of compile-time stages**, each eliminating one layer of intermediate types. The priority/dependency order determines the composition sequence (DAG condition from THY_0014 guarantees termination).

### 10.3 Grade-aware dead code detection

If a type is declared `@abstract` (grade 0) but no rule consumes it, the expansion rules producing it are dead code. Grade analysis detects this statically.

### 10.4 Affine and bounded-reuse resources (future)

The {0,1,ω} semiring extends naturally:
- **Affine** (grade ≤ 1): resource can be dropped but not duplicated
- **Bounded reuse** (grade n): resource can be used exactly n times
- **Interval bounds** [lo, hi]: resource used between lo and hi times

These require engine changes (RES_0054) but the conceptual framework is the same semiring.

## 11. Interaction with SELL (TODO 151)

THY_0013's indexed monad `{A}_a` is indexed by stratum label a (from SELL). The graded monad adds a second index q (from QTT). These are orthogonal:

- **Label a** (SELL): which rules are visible (structural: which zone of the proof state)
- **Quantity q** (QTT): how the type is used (0 = compile-time, 1 = linear, ω = persistent)

A forward rule carries BOTH: its label (from `@module` / `@label`) and the quantity of its types (from `@abstract` / `!` / default-linear).

In the Glad system (Hanukaev & Eades, TyDe 2023), each mode (= SELL label) carries its own graded semiring. Our system is simpler: one semiring {0,1,ω} shared across all strata, with labels providing the structural partitioning.

## 12. Open Questions

### Is grade 0 the right staging mechanism?

Grade 0 gives us a clean binary: compile-time (0) or runtime (1/ω). But real staging systems often have more than two levels (MetaOCaml: arbitrary nesting of brackets). Is there a natural extension where grades from a richer semiring give multi-level staging? The tower of 0-phases (§10.2) is one approach, but it requires explicit priority ordering.

### How does grade 0 interact with focusing?

Andreoli focusing partitions connectives by polarity. A grade-0 type is "compile-time positive" — it can be focused on during composition but doesn't participate in runtime focusing. Does a grade-aware focusing discipline exist? This is open (noted in RES_0054 §9).

### Can grades be inferred from rule structure?

Given a set of forward rules, can we automatically detect which types should be grade 0? This is a form of **binding-time analysis** (BTA). The sufficient condition: a type M is inferrably grade-0 if (1) no rule both produces and consumes M, and (2) M doesn't appear in initial states or goals. This is the bipartite condition from THY_0014.

### What about grade-0 persistent facts?

A persistent fact `!P` at grade 0 would be a compile-time-only axiom — available for backward chaining during composition but erased before runtime. This could model compile-time assumptions: "for this contract, slot 0 always holds the owner address." The backward chainer resolves `!storage(0, owner)` during composition, hardcoding the result.

### Is there a graded focusing theorem?

No focused proof system for semiring-graded ILL exists in the literature. The standard Andreoli focusing + the graded semiring would yield a system where focus phases respect grades — e.g., grade-0 focus phases are compile-time only. Proving cut elimination for such a system is open.

## 13. References

- THY_0013 — The Indexed Lax Monad
- THY_0014 — Compile-Time Evaluation of the Indexed Monad
- RES_0054 — Graded Resource Analysis for Linear Logic
- RES_0056 — QTT Sequent Calculus and Gap Analysis (§10 corrected here)
- RES_0074 — QTT/Graded/Adjoint/SELL/MTDC Expressiveness Hierarchy
- RES_0102 — Stratified and Phased Cut Elimination (literature survey)
- Atkey, "Syntax and Semantics of Quantitative Type Theory" (LICS 2018)
- McBride, "I Got Plenty o' Nuttin'" (2016)
- Brady, "Idris 2: QTT in Practice" (ECOOP 2021)
- Gaboardi, Katsumata, Orchard, Breuvart, Uustalu, "Combining Effects and Coeffects via Grading" (ICFP 2016)
- Moon, Eades, Orchard, "Graded Modal Dependent Type Theory" (ICFP 2021)
- Hanukaev & Eades, "Combining Dependency, Grades, and Adjoint Logic" (TyDe 2023)
- Girard, Scedrov, Scott, "Bounded Linear Logic" (TCS 1992)
- Baillot, Mazza, "Linear Logic by Levels and Bounded Time Complexity" (TCS 2010)
- Vollmer, Marshall, Eades, Orchard, "A Mixed Linear and Graded Logic" (CSL 2025)
- Cockett, "Deforestation, Program Transformation, and Cut-Elimination" (ENTCS 2001)
- Kovács, "Staged Compilation with Two-Level Type Theory" (POPL 2023)
- Davies, "A Temporal Logic Approach to Binding-Time Analysis" (LICS 1996)
