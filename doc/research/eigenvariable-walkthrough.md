---
title: "Eigenvariable Approach: Step-by-Step Walkthrough"
created: 2026-02-20
modified: 2026-02-21
summary: "Detailed trace of how eigenvariables flow through forward-chaining execution: basic mechanism, chained operations, branching, late resolution, and scale analysis."
tags: [symexec, eigenvariable, CLF, forward-chaining, walkthrough]
---

# Eigenvariable Approach: Step-by-Step Walkthrough

## 1. The Mechanism

When a forward rule needs to prove `!plus(A, B, C)` and the proof fails (A is symbolic), instead of failing the rule, we:

1. **Generate a fresh parameter** α_n (monotonic counter)
2. **Bind C = α_n** in the consequent substitution
3. **Emit the constraint** `!plus(A, B, α_n)` as a persistent fact in the state
4. **Continue execution** — the rule fires normally, α_n flows as a value

The constraint is a regular persistent fact. It says: "α_n is the value satisfying plus(A, B, α_n)." If A later becomes ground, the constraint can be **resolved**: re-prove plus(A', B, C) via FFI, get concrete C, substitute α_n → C everywhere.

**What changes in the engine:**
- Fresh name generation: `let evarCounter = 0; function freshEvar() { ... }` (~5 LOC)
- In `tryMatch`/`provePersistentGoals`: when backward proving fails, instead of returning null, generate fresh evar and record constraint (~15 LOC)
- Constraint index: map from evar hash → list of constraint facts (~20 LOC)
- Propagation: when an evar resolves, substitute everywhere and re-check dependent constraints (~50 LOC)

Total: ~90 LOC engine changes. Zero .ill changes (no new constructors or catch-all clauses).

---

## 2. Scenario 1: Simple Symbolic ADD

**Bytecode:** `CALLDATALOAD, PUSH 1, ADD`

### Step 0: CALLDATALOAD

CALLDATALOAD pushes an unknown 256-bit value. In the current concrete engine, this is a known value from actual calldata. In symbolic execution, this is a **free parameter** — let's call it `?D`.

```
State: {
  pc(0), code(0, 0x35), code(1, 0x60), code(2, 0x01), code(3, 0x01),
  sh(s(0)), stack(0, ?D),
  !codeByPC(...)
}
```

Note: `?D` itself is already an eigenvariable — it represents "whatever calldata value was provided." The CALLDATALOAD rule would ideally use ∃ to introduce it. Currently it's a concrete value from input; in symbolic mode it would be a fresh parameter.

### Step 1: PUSH 1

Pushes concrete `binlit(1)`.

```
State: {
  pc(2), sh(s(s(0))),
  stack(1, ?D), stack(0, binlit(1)),
  ...
}
```

### Step 2: ADD

The ADD rule:
```
pc(PC) * code(PC, 0x01) * sh(s(s(SH))) * stack(s(SH), A) * stack(SH, B)
  * !inc(PC, PC') * !plus(A, B, C)
  -o { code(PC, 0x01) * pc(PC') * sh(s(SH)) * stack(SH, C) }
```

Matching: PC=2, A=?D, B=binlit(1), SH=0.

**Proving persistent antecedents:**
- `!inc(2, PC')` → FFI: PC' = 3. Success.
- `!plus(?D, binlit(1), C)` → FFI: binToInt(?D) fails. State lookup: no match. Backward clauses: no match.

**Eigenvariable mechanism kicks in:**
- Generate fresh: α₀
- Bind: C = α₀
- Emit constraint: `!plus(?D, binlit(1), α₀)` as persistent fact

**State after ADD:**
```
State: {
  pc(3), sh(s(0)),
  stack(0, α₀),
  !plus(?D, binlit(1), α₀),     ← constraint
  ...
}
```

Execution continues. The stack has α₀. The next opcode can fire because pc(3) exists.

---

## 3. Scenario 2: Chained Arithmetic

**Bytecode:** `CALLDATALOAD, PUSH 3, ADD, PUSH 5, ADD, PUSH 2, MUL`

After CALLDATALOAD + PUSH 3:
```
State: { pc(2), stack(1, ?D), stack(0, binlit(3)), ... }
```

### ADD 1: ?D + 3

- `!plus(?D, binlit(3), C)` → fails → α₀, emit `!plus(?D, binlit(3), α₀)`

```
State: { pc(3), stack(0, α₀), !plus(?D, binlit(3), α₀), ... }
```

### PUSH 5 + ADD 2: α₀ + 5

- `!plus(α₀, binlit(5), C)` → FFI: binToInt(α₀) fails → α₁, emit `!plus(α₀, binlit(5), α₁)`

```
State: {
  pc(6), stack(0, α₁),
  !plus(?D, binlit(3), α₀),
  !plus(α₀, binlit(5), α₁),
  ...
}
```

### PUSH 2 + MUL: α₁ * 2

- `!mul(α₁, binlit(2), C)` → fails → α₂, emit `!mul(α₁, binlit(2), α₂)`

```
State: {
  pc(9), stack(0, α₂),
  !plus(?D, binlit(3), α₀),     ← α₀ = ?D + 3
  !plus(α₀, binlit(5), α₁),     ← α₁ = α₀ + 5 = ?D + 8
  !mul(α₁, binlit(2), α₂),      ← α₂ = α₁ * 2 = (?D + 8) * 2
  ...
}
```

**Constraint graph:**
```
?D ──plus(?,3)──→ α₀ ──plus(?,5)──→ α₁ ──mul(?,2)──→ α₂
```

**Observations:**
- 3 eigenvariables for 3 symbolic operations. Linear growth: O(symbolic_ops).
- Constraints are flat — each references at most one other evar.
- The constraint graph is a DAG (directed acyclic — evars only reference earlier evars).
- **No constant folding happened.** With Skolem + AC-norm, `(?D + 3) + 5` would become `?D + 8`. With eigenvariables, the two additions remain as separate constraints. To merge them, you'd need a constraint simplification rule (P3 territory).

---

## 4. Scenario 3: Branching on Symbolic Value

**Bytecode:** `CALLDATALOAD, PUSH 0, EQ, PUSH target, JUMPI`

After CALLDATALOAD + PUSH 0:
```
State: { pc(2), stack(1, ?D), stack(0, binlit(0)), ... }
```

### EQ: compare ?D with 0

EQ is a **boolean predicate** — it's not a total function. It succeeds (pushes 1) or fails (pushes 0). Eigenvariables DON'T apply here (we can't introduce a fresh parameter for a boolean — that would be unsound for the same reason catch-all clauses are unsafe for partial relations).

**This is where ⊕ branching handles it** (already implemented):

```
⊕ Branch A: eq(?D, 0) holds
  State: { pc(3), stack(0, binlit(1)), !eq(?D, binlit(0)), ... }

⊕ Branch B: neq(?D, 0) holds
  State: { pc(3), stack(0, binlit(0)), !neq(?D, binlit(0)), ... }
```

### JUMPI on each branch

**Branch A:** stack top = 1 (true) → jump to target
```
State: { pc(target), !eq(?D, binlit(0)), ... }
```

**Branch B:** stack top = 0 (false) → fall through
```
State: { pc(4), !neq(?D, binlit(0)), ... }
```

**Key point:** Eigenvariables and ⊕ branching work TOGETHER naturally. Eigenvariables handle functional computation (arithmetic). ⊕ handles boolean branching. They compose without interference.

---

## 5. Scenario 4: Chained Arithmetic + Branching + Late Resolution

**Bytecode:** `CALLDATALOAD, PUSH 3, ADD, PUSH 0, EQ, PUSH target, JUMPI`

After CALLDATALOAD + PUSH 3 + ADD:
```
State: { pc(4), stack(0, α₀), !plus(?D, binlit(3), α₀), ... }
```

### EQ: compare α₀ with 0

⊕ branching:

**Branch A: eq(α₀, 0) holds**
```
State: {
  pc(5), stack(0, binlit(1)),
  !plus(?D, binlit(3), α₀),
  !eq(α₀, binlit(0)),
  ...
}
```

Now something interesting: we have BOTH `!plus(?D, 3, α₀)` AND `!eq(α₀, 0)`.

**Propagation (if active):**
1. `!eq(α₀, 0)` means α₀ = 0
2. Substitute into `!plus(?D, 3, α₀)` → `!plus(?D, 3, 0)`
3. Re-prove: `plus(?D, 3, 0)` — this means ?D + 3 = 0, so ?D = 2²⁵⁶ - 3 (modular arithmetic)
4. Substitute ?D → binlit(2²⁵⁶ - 3) everywhere in state
5. All remaining evars that depend on ?D can now be resolved too

**Result:** On Branch A, ALL eigenvariables are resolved to concrete values. The branch represents the specific execution where calldata = 2²⁵⁶ - 3.

**Branch B: neq(α₀, 0) holds**
```
State: {
  pc(5), stack(0, binlit(0)),
  !plus(?D, binlit(3), α₀),
  !neq(α₀, binlit(0)),
  ...
}
```

Here `!neq(α₀, 0)` means α₀ ≠ 0. We know α₀ is NOT zero, but we don't know what it IS. No resolution. α₀ remains an eigenvariable.

We DO learn something: since α₀ = ?D + 3 and α₀ ≠ 0, we know ?D ≠ 2²⁵⁶ - 3. This is a **domain constraint** — useful for future reasoning but doesn't fully resolve anything.

**Key insight:** Eigenvariable resolution is ASYMMETRIC. Equality constraints (`eq`) fully resolve evars (cascading substitution). Inequality constraints (`neq`) only narrow domains (no substitution). This is the same as CLP(FD) behavior.

---

## 6. Scenario 5: Without vs With Propagation

### Without propagation (just accumulate)

The simplest eigenvariable implementation does NO propagation. Constraints accumulate. Evars never resolve. The final quiescent state contains:

```
State: {
  pc(stuck), stack(0, α₇),
  !plus(?D, 3, α₀),
  !plus(α₀, 5, α₁),
  !mul(α₁, 2, α₂),
  !plus(α₂, 7, α₃),
  !eq(α₃, 0),           ← from ⊕ branching
  !plus(α₃, 1, α₄),
  ...
}
```

This is still USEFUL. The constraint store is a complete description of the computation. You can:
- Export it to an SMT solver: `(assert (= (+ d 3) a0)) (assert (= (+ a0 5) a1)) ...`
- Print it as a symbolic trace
- Compare constraint stores across branches for path conditions

**Cost:** O(symbolic_ops) constraints, O(1) per step. No propagation overhead. Total: O(n) space, O(n) time for n steps.

### With propagation (resolve when possible)

Richer: when an `!eq(αᵢ, v)` constraint appears (from ⊕ branching or late grounding), substitute αᵢ → v everywhere and re-check:

1. Find all constraints mentioning αᵢ
2. Replace αᵢ with v in each
3. For each updated constraint, re-try proving via FFI
4. If provable → the constraint's output evar gets a concrete value → recurse

**Cost:** Each resolution is O(constraints_mentioning_αᵢ). Worst case: cascading resolution through all evars → O(n). But this is rare — typically only happens on equality branches.

**Implementation:**
- Evar→constraints index: `Map<evarHash, [constraintFact, ...]>` (~20 LOC)
- On resolution: `propagate(evar, value, state)` walks the chain (~30 LOC)
- Can be lazy: only propagate when explicitly asked (e.g., at quiescence)

---

## 7. Scenario 6: Scale Analysis

### 100 symbolic arithmetic operations (no branching)

```
Constraint store: 100 entries
  !plus(?D, 3, α₀)
  !plus(α₀, 5, α₁)
  !mul(α₁, 2, α₂)
  ... (100 total)
Eigenvariables: α₀ through α₉₉
```

**Memory:** 100 persistent facts × ~32 bytes each = ~3.2 KB. Negligible.
**Time:** 100 fresh evar generations + 100 constraint emissions = O(100). Negligible.
**Constraint graph:** linear chain of length 100. If ?D becomes ground, full resolution takes O(100) FFI calls — each O(1) BigInt arithmetic = O(100) total.

### 100 operations with 5 branches (= 32 leaves)

Each branch point creates ⊕ with 2 children. 5 branch points = 32 leaves. Each leaf has ~100/5 = 20 operations per segment.

```
Per leaf: ~100 constraints (inherited from all ancestors + own segment)
Total: 32 × 100 = 3200 constraints across all leaves
```

With mutation+undo (current architecture), constraints on ancestor branches are shared. Only the per-segment delta is unique to each leaf. Actual memory: ~100 (shared) + 32 × 20 (unique) = ~740 constraint facts.

### 1000 operations, 50 branches

```
Per leaf: ~1000 constraints
Leaves: up to 2⁵⁰ (but most branches die — typical: ~100-1000 live leaves)
```

At 1000 live leaves × 1000 constraints: ~1M constraint facts. With mutation+undo and shared ancestors: much less. The dominant cost is backward proving (FFI calls) per step, same as today.

**Comparison with Skolem at scale:**

| Metric | Eigenvariable | Skolem |
|---|---|---|
| Per-step cost | O(1) fresh + constraint emit | O(1) term construction |
| Memory per step | +1 persistent fact (~32 bytes) | +1 Store node (~24 bytes) |
| After 1000 steps | 1000 flat constraints | 1 nested tree of depth 1000 |
| Late resolution | O(chain_length) propagation | O(1) if ground-folded at construction |
| SMT export | Direct (constraints are flat) | O(tree_size) flattening |
| Constant folding | Needs constraint simplification rules | Free at Store.put (AC-norm) |
| State hashing | O(1) per new constraint | O(1) per new Store node |

**The key efficiency difference:** Skolem terms grow as nested trees but normalize at construction time (constant folding is free). Eigenvariable constraints stay flat but DON'T fold constants (need explicit simplification rules for `plus(X, 3, Y), plus(Y, 5, Z) → plus(X, 8, Z)`).

Both approaches have O(n) growth per n symbolic operations. The constant factor is similar. The difference is WHERE the information lives (in the term structure vs in flat constraints).

---

## 8. How Eigenvariables Interact with P2 and P3

### P2 (Witness Representation)

With eigenvariables, P2 is minimal:
- `evar(N)` — a Store node with tag `evar` and one child (the counter value as binlit)
- That's it. No expression constructors, no catch-all clauses, no ground folding.

The constraint store is just the persistent context (already exists). No new data structure.

### P3 (Simplification → Constraint Propagation)

Without P3: constraints accumulate, evars never resolve. Still useful (SMT export, symbolic traces).

With P3: three levels of increasing sophistication:

**Level 0: Equality resolution**
When `!eq(αᵢ, v)` appears, substitute αᵢ → v everywhere. This is the minimum useful propagation. ~30 LOC.

**Level 1: FFI re-check**
When a constraint's inputs all become ground, re-prove via FFI and resolve the output evar. E.g., `!plus(binlit(5), binlit(3), α₀)` → FFI gives 8 → α₀ = 8. ~20 LOC on top of Level 0.

**Level 2: Chain simplification**
Detect constraint chains and merge: `!plus(X, 3, Y), !plus(Y, 5, Z)` → `!plus(X, 8, Z)`. Delete intermediate evar Y. This is the eigenvariable analogue of AC-normalization. ~100 LOC. Requires constraint pattern matching.

**Level 3: Domain propagation**
Track intervals: `!neq(α₀, 0)` → domain(α₀) = [1, 2²⁵⁶-1]. `!plus(?D, 3, α₀), domain(α₀) = [1, ...]` → domain(?D) = [2²⁵⁶-2, ...]. ~200 LOC. CLP(FD) territory.

---

## 9. How Eigenvariables Interact with Downstream TODOs

### TODO_0028 (Confluence)
Not needed for eigenvariables. Confluence is a Skolem concern (ground folding). Eigenvariables don't have the "two paths to same hash" problem — evars are always unique by construction.

### TODO_0005 (Simplification)
Becomes constraint propagation instead of term rewriting. Different techniques (CLP vs Knuth-Bendix) but same structural role. Could be done via CHR-style propagation rules.

### TODO_0006 (Lax Monad Integration)
∃ in the monad (CLF-style) IS the eigenvariable mechanism made explicit. If we add ∃ as a connective, then eigenvariable generation during forward chaining becomes ∃R in the monadic decomposition. Clean fit — this is exactly what CLF was designed for.

### TODO_0029-0032 (Verification: properties, invariants, reachability, counterexamples)
Eigenvariable constraint stores export DIRECTLY to SMT:
```
(declare-const d (_ BitVec 256))
(assert (= (bvadd d #x03) a0))
(assert (= (bvadd a0 #x05) a1))
(assert (= (bvmul a1 #x02) a2))
(check-sat)
```
No flattening needed (unlike Skolem expression trees). The constraint store IS the SMT problem. This is a significant advantage for the verification pipeline.

### Forward optimization (stages 1-11)
Eigenvariable generation is O(1) per step — a counter increment + Store.put + persistent fact emission. Compatible with all existing optimizations (strategy stack, disc-tree, compiled matching, mutation+undo). The constraint index is a small addition to the state index infrastructure.

---

## 10. The ∃ Connective and Its Relationship to Eigenvariables

### What ∃ means

∃ is the existential quantifier as a connective in linear logic:

```
∃x:A. B(x)     "there exists an x of type A such that B(x)"
```

### Proof rules

```
  Γ; Δ ⊢ B[t/x]
  ─────────────── ∃R  (right introduction: provide a witness t)
  Γ; Δ ⊢ ∃x.B

  Γ; Δ, B[a/x] ⊢ C         a fresh
  ──────────────────────────── ∃L  (left elimination: open and bind)
  Γ; Δ, ∃x.B ⊢ C
```

### Focusing behavior

∃ is **positive** (synchronous), same polarity class as ⊗, 1, ⊕:
- Invertible on the LEFT (always decompose — ∃L is always safe)
- Focusable on the RIGHT (must choose witness — ∃R requires a decision)

### How ∃ maps to eigenvariables in forward chaining

In CLF, forward chaining happens inside the monad `{A}`. When the consequent of a forward rule contains ∃:

```
rule: antecedents -o { ∃C. (stack(SH, C) * !plus(A, B, C) * ...) }
```

The monadic decomposition encounters `∃C` and:
1. Generates a fresh parameter α for C
2. Continues decomposing `{stack(SH, α) * !plus(A, B, α) * ...}`
3. Adds all resulting facts (including the constraint) to the state

**This IS the eigenvariable approach.** Adding ∃ makes it explicit in the logic rather than implicit in engine code.

### What changes in CALC if we add ∃

**Without ∃ (current + eigenvariable hack):**
- Forward rules have implicit universal quantification over all variables
- The engine detects "backward proving failed" and generates a fresh evar
- This is an engine-level workaround, not a logical mechanism
- The constraint emission is ad-hoc (engine code, not rule-specified)

**With ∃ (CLF-style):**
- Forward rules explicitly declare which consequent variables are existentially quantified
- The forward engine has a case for ∃ in monadic decomposition
- Fresh parameter generation is a logical operation (∃R), not a hack
- The constraint appears naturally as part of the rule consequent

### Example: ADD rule with ∃

**Current (implicit):**
```
evm/add: pc(PC) * stack(1, A) * stack(0, B) * !inc(PC, PC') * !plus(A, B, C)
         -o { pc(PC') * stack(0, C) }
```
C is determined by proving !plus(A, B, C). If proof fails, engine hacks in a fresh evar.

**With ∃ (explicit):**
```
evm/add: pc(PC) * stack(1, A) * stack(0, B) * !inc(PC, PC')
         -o { exists C. (pc(PC') * stack(0, C) * !plus(A, B, C)) }
```
C is fresh (∃R). The constraint !plus(A, B, C) is part of the consequent — it's emitted alongside the value. If the constraint IS immediately provable (FFI succeeds), C gets bound to the concrete result. If not, C stays as a fresh parameter.

### The beautiful part

With ∃, the rule DOESN'T NEED to prove plus in the antecedent at all. The plus constraint moves to the CONSEQUENT:
- Antecedent: only linear matching (pc, stack) + inc (always succeeds for ground PC)
- Consequent: ∃C + constraint + state facts

This means:
- No backward chaining needed for arithmetic during rule firing
- The constraint is part of the monadic output, not a precondition
- For ground inputs: the constraint `!plus(3, 5, C)` is immediately resolved by FFI → C = 8
- For symbolic inputs: C stays fresh, constraint accumulates

**This cleanly separates matching (antecedent) from computation (consequent).** The rule fires whenever its pattern matches. The computation is deferred to constraint resolution.

### Tradeoffs of adding ∃

**What we gain:**
- Theoretically clean: standard CLF, not engine hack
- Rule-level control: author decides which variables are existential
- Natural constraint emission: constraints are consequent facts, not engine artifacts
- CLF/Celf/Ceptre compatibility
- Foundation for dependent types (TODO_0011)
- Foundation for fresh name generation (protocols, nonces)

**What we lose:**
- Simplicity: one more connective through every layer
- Current rule format: rules would need rewriting (move plus from antecedent to consequent)
- Backward prover also needs ∃ handling (∃R: introduce logic variable, ∃L: open and bind)

**Risks:**
- Variable binding in the grammar (need `exists X. A` syntax) — adds complexity to tree-sitter grammar
- Scoping: ∃ inside ⊗ vs ∃ outside ⊗ matters — need to track scope correctly
- If done wrong, can break content-addressing (fresh names must be handled carefully in the Store)

**If we DON'T add ∃:**
- Engine-level eigenvariable generation works but is ad-hoc
- Can't express protocols with fresh nonces in .ill rules
- Dependent types (TODO_0011) become harder
- We lose CLF compatibility

**If we DO add ∃:**
- ~200 LOC across all layers (grammar ~10, parser ~20, rules ~20, forward engine ~30, backward prover ~30, focusing ~5, convert ~20, Store ~5, tests ~60)
- One-time effort, then all future rules can use it
- The eigenvariable approach becomes a LOGICAL MECHANISM, not a hack

---

## 11. Assessment

### Eigenvariable strengths
- **Theoretically clean:** standard CLF ∃-introduction. No theory extension, no redundant axioms.
- **Flat constraints:** SMT-ready. No tree flattening needed.
- **Natural composition with ⊕:** eigenvariables handle arithmetic, ⊕ handles branching.
- **Late resolution:** when evars become ground, cascading propagation resolves the chain.
- **No simplification required:** works without any normalization (just grows constraints).

### Eigenvariable weaknesses
- **No free constant folding:** `!plus(X, 3, α₀), !plus(α₀, 5, α₁)` stays as two constraints. Need Level 2 simplification to merge to `!plus(X, 8, α₁)`.
- **Opaque values:** `α₇` tells you nothing. Must consult constraint store for meaning.
- **No deduplication:** identical computations at different steps produce different evars.
- **Engine changes:** ~90 LOC (vs 0 for Skolem catch-all clauses).

### The honest comparison

| Concern | Skolem | Eigenvariable |
|---|---|---|
| Theory | Dirty (redundant axioms, fallback ordering) | Clean (standard CLF ∃R) |
| Engine changes | 0 | ~90 LOC |
| Constant folding | Free at Store.put | Needs constraint simplification |
| SMT export | O(tree_size) flattening | O(1) per constraint (already flat) |
| Deep inference needed? | Possibly (K-framework concern) | No (constraints stay flat) |
| Slippery slope | → K-framework (lose backward chaining) | → CLP (extend backward chaining) |
| With ∃ connective | N/A (Skolem doesn't use ∃) | Becomes a logical mechanism |
| Foundation | Rewriting logic (Maude/K) | CLF (Celf/Ceptre) |

### The deep question

Skolem leads toward **rewriting logic** (Maude, K): terms + simplification rules, deep inference, eventually replace backward chaining entirely.

Eigenvariable leads toward **constraint logic programming** (CLP, CHR): flat constraints + propagation, extend backward chaining with constraint stores, keep the CLF foundation.

These are different research directions. Not wrong vs right — different foundations. The question is which foundation CALC wants to build on long-term.

---

## 12. Multimodal Predicates and Mode-Agnosticism

The `plus` predicate is used in multiple modes across EVM rules:

| Rule | Obligation | Mode | Semantics |
|------|-----------|------|-----------|
| ADD | `!plus A B C` | `+ + -` | C = A + B |
| SUB | `!plus C B A` | `- + +` | C = A - B |
| Gas | `!plus 10 GAS GAS'` | `+ + -` | GAS' = 10 + GAS |

With ∃, the constraint is just emitted — resolution depends on the **solver**, not on ∃ itself. If both inputs are ground, FFI resolves immediately. If one input is symbolic, the constraint accumulates.

Example: SUB with symbolic B.
```
stack(1, binlit(3)), stack(0, α₇)
Constraint: !plus(α₈, α₇, binlit(3))   — "α₈ + α₇ = 3"
```
Two unknowns → can't resolve. When α₇ later resolves to v, re-check in mode `- + +`: α₈ = 3 - v.

The `+ - +` mode (A and C known, find B = C - A) requires either multi-mode FFI or a constraint rewriting rule. This is P3 (constraint propagation), orthogonal to ∃.

**Key principle:** ∃ changes **when** solving happens (accumulate instead of block). It does NOT change **what** is solvable.

---

## 13. Relationship to the CLF Monad `{A}`

CALC's `{...}` in rule consequents IS the CLF monad, implemented implicitly:

| CLF monad operation | CALC implementation |
|---|---|
| ⊗ decomposition | `expandItem` splits into individual facts |
| ∃ introduction | **Missing** — this is the gap ∃ fills |
| ⊕ branching | `expandItem` forks into children |
| ⊸ suspension | Loli stays in state, `matchLoli` fires when guard provable |
| ! annotation | Fact added to `state.persistent` |

The implementation is **incomplete**, not dirty. Adding ∃ fills the main gap and completes the monadic decomposition. If we wanted "proper CLF," we'd also add type-level tracking of the monadic boundary — but that's not needed for symbolic execution.

---

## 14. Branch Pruning Mechanics

### Concrete case: A=0, B=0

The EQ rule (evm.ill:186) fires, producing:
```
{ ((!neq 0 0 ⊸ { stack SH 0 }) ⊕ (!eq 0 0 ⊸ { stack SH 1 })) }
```

`expandItem` hits ⊕, forks:

**Branch L:** `!neq(0, 0) ⊸ { stack(0, 0) }`
- `matchLoli` tries `neq(0, 0)` → FFI: 0 ≠ 0? **False.** Definitive failure.
- Loli guard fails → **dead leaf** (no facts emitted)

**Branch R:** `!eq(0, 0) ⊸ { stack(0, 1) }`
- `matchLoli` tries `eq(0, 0)` → FFI: 0 = 0? **True.**
- Loli fires → `stack(0, 1)` emitted → execution continues

Result: 3 nodes (fork + dead leaf + live continuation). 1 dead leaf.

### Symbolic case: A=α₀, B=α₁

**Branch L:** `!neq(α₀, α₁) ⊸ { stack(0, 0) }`
- FFI: not ground → null. No state match. No backward clause match.
- Loli stays **suspended**. Branch survives with path condition `!neq(α₀, α₁)`.

**Branch R:** `!eq(α₀, α₁) ⊸ { stack(0, 1) }`
- Same: can't evaluate. Survives with path condition `!eq(α₀, α₁)`.

Both branches survive — sound, since we don't know if α₀ = α₁.

**Late resolution:** If α₀ → 0, α₁ → 0:
- Branch L: re-check `neq(0, 0)` → false → **prune**
- Branch R: re-check `eq(0, 0)` → true → loli fires, continues

### Dead-node cost

Every ⊕ creates at least 3 nodes (fork + 2 children), even if one immediately dies. Possible optimization: **guard-first evaluation** — eagerly check guards before forking, skip branches with definitively false guards. Collapses the fork when exactly one guard succeeds. For EVM: saves ~5 dead leaves in a 63-node tree (negligible). For programs with hundreds of branch points: measurable.

---

## 15. ⊕ Beyond Exclusive Binary Guards

EVM uses ⊕ exclusively as `P ⊕ ¬P` (decidable, exclusive, exhaustive). General ⊕ is broader.

**Unguarded choice (no loli):**
```
coin -o { heads ⊕ tails }
```
Both branches always explored. Models non-determinism.

**Non-exclusive guards:**
```
classify(X) -o {
  (!gt X 0 ⊸ { positive(X) }) ⊕ (!lt X 10 ⊸ { small(X) })
}
```
For X=5: both guards succeed, both branches survive.

**N-ary via nesting:**
```
traffic -o { (red ⊸ {stop}) ⊕ ((yellow ⊸ {slow}) ⊕ (green ⊸ {go})) }
```
`expandItem` decomposes recursively: fork → left, right; right forks again → three branches.

**Non-exhaustive guards:**
```
token(X) -o { (!isAdmin X ⊸ {admin_panel}) ⊕ (!isUser X ⊸ {user_panel}) }
```
For a guest: both guards fail, both branches die → stuck state.

| Pattern | Both die? | Both survive? |
|---------|-----------|---------------|
| `P ⊕ ¬P` (EVM) | No (exactly one lives) | No |
| Overlapping guards | Yes | Yes |
| Unguarded | No | Always |
| Non-exhaustive | Yes | Yes |

The eigenvariable approach composes with all these patterns: ∃ handles fresh values, ⊕ handles branching, loli guards filter. The mechanisms are orthogonal.

---

## References

- Watkins, Cervesato, Pfenning, Walker (2004). CLF. LNCS 3085
- Simmons (2012). Substructural Logical Specifications. PhD thesis, CMU
- Jaffar, Maher (1994). Constraint Logic Programming: A Survey. JLP
- Holzbaur (1992). Attributed Variables. PLILP
- Barichard, Stephan (2025). QCHR. ACM TOCL 26(3)
- Fages, Ruet, Soliman (2001). Linear Concurrent Constraint Programming. I&C 165(1)
- Rocha, Meseguer (2013). Rewriting Modulo SMT. NASA/TM-2013-218033
