---
title: "CHR/CHR∨ ↔ Linear Logic: Soundness Mapping for CALC"
created: 2026-02-19
modified: 2026-02-20
summary: "Apply Betz & Frühwirth's CHR ↔ linear logic results to CALC: formal soundness proof for forward engine, CHR∨ soundness for ⊕ in consequents, confluence analysis, compilation techniques"
tags: [CHR, linear-logic, soundness, forward-engine, oplus, theory]
type: research
status: in progress
priority: 10
depends_on: []
required_by: [TODO_0042]
---

# CHR/CHR∨ ↔ Linear Logic Mapping

## Why This Matters

CALC's forward engine IS a CHR engine (simpagation rules with guards). Betz & Frühwirth (2005-2018) proved soundness and completeness results mapping CHR to linear logic. These results transfer to CALC, giving us formal guarantees essentially for free.

CHR∨ (CHR with disjunction) maps disjunctive rule bodies to `⊕` in linear logic. CALC's `⊕` in forward-chaining consequents is exactly this. The CHR∨ soundness result formally justifies our `⊕` extension.

---

## 1. Formal Mapping: CALC Forward Rules ↔ CHR Simpagation

### 1.1 The Betz/Frühwirth Translation (-)^L

The translation maps CHR constructs to ILL:

| CHR construct | ILL translation |
|---|---|
| User-defined constraint `c(t̄)` | `c(t̄)` (linear atom) |
| Built-in constraint `b(t̄)` | `!b(t̄)` (banged/persistent) |
| Conjunction `C₁ ∧ C₂` | `C₁^L ⊗ C₂^L` (tensor) |
| True (⊤) | `1` (unit) |
| Disjunction `C₁ ∨ C₂` | `C₁^L ⊕ C₂^L` (additive disjunction) |
| State `⟨U; B; V⟩` | `∃₋ᵥ.(U^L ⊗ B^L)` |

**Simpagation rule translation** (Definition 4.4 in TOCL 2013):

For rule `r @ H₁ \ H₂ ⟺ G | B_b ∧ B_u` with local variables `ȳᵣ`:

```
H₁^L ⊗ H₂^L ⊗ G^L  ⊢  H₁^L ⊗ ∃ȳᵣ.(B_b^L ⊗ B_u^L ⊗ G^L)
```

- `H₁` = kept head (persistent antecedent) → appears on both sides
- `H₂` = removed head (linear antecedent) → consumed on left
- `G` = guard (built-in, banged) → present on both sides via contraction
- `B_u` = user-defined body → produced
- `B_b` = built-in body (banged)
- `∃ȳᵣ` = existential over local body variables

### 1.2 CALC Rule Format → CHR Simpagation

A CALC forward rule (from `.ill` file):

```ill
evm/add:
  pc PC * code PC 0x01 * !inc PC PC' * sh (s (s SH)) *
  stack (s SH) A * stack SH B * !plus A B C
  -o { code PC 0x01 * pc PC' * sh (s SH) * stack SH C }.
```

After `flattenTensor`, this becomes:

```
antecedent.linear:      [pc(PC), code(PC, 0x01), sh(s(s(SH))), stack(s(SH), A), stack(SH, B)]
antecedent.persistent:  [inc(PC, PC'), plus(A, B, C)]
consequent.linear:      [code(PC, 0x01), pc(PC'), sh(s(SH)), stack(SH, C)]
consequent.persistent:  []
```

**CHR simpagation form:**

```
evm_add @ inc(PC,PC'), plus(A,B,C)  \  pc(PC), code(PC,0x01), sh(s(s(SH))), stack(s(SH),A), stack(SH,B)
  ⟺
  code(PC,0x01), pc(PC'), sh(s(SH)), stack(SH,C)
```

- **Kept head H₁:** `inc(PC,PC'), plus(A,B,C)` — persistent antecedents (proved via FFI)
- **Removed head H₂:** `pc(PC), code(PC,0x01), sh(s(s(SH))), stack(s(SH),A), stack(SH,B)` — linear antecedents (consumed)
- **Guard G:** trivial (built-in guard check is embedded in persistent antecedent proving — `inc` and `plus` are FFI functions that serve as both guards AND kept heads)
- **Body B_u:** `code(PC,0x01), pc(PC'), sh(s(SH)), stack(SH,C)` — produced facts

**ILL translation:**

```
!inc(PC,PC') ⊗ !plus(A,B,C) ⊗ pc(PC) ⊗ code(PC,0x01) ⊗ sh(s(s(SH))) ⊗ stack(s(SH),A) ⊗ stack(SH,B)
  ⊢
!inc(PC,PC') ⊗ !plus(A,B,C) ⊗ code(PC,0x01) ⊗ pc(PC') ⊗ sh(s(SH)) ⊗ stack(SH,C)
```

This is exactly the sequent CALC's rule represents as `antecedent -o {consequent}`, since the persistent antecedents appear on both sides (via contraction on banged formulas).

### 1.3 CALC's Guard = CHR's Built-in Constraint + Kept Head

CALC merges the CHR guard and kept-head roles: persistent antecedents like `!inc PC PC'` serve as BOTH:
1. **Guard** — the FFI call to `inc` must succeed (guards the rule)
2. **Kept head** — the fact `!inc(PC, PC')` is not consumed (persistent)

In CHR, guards and kept heads are syntactically distinct. In CALC, they coincide because persistent facts (`!A`) are never consumed and must be provable (via FFI, state lookup, or backward chaining).

This is sound because the linear logic translation treats both identically: banged atoms are available for contraction, so they appear on both sides of the sequent regardless of whether they are "guard" or "kept head."

### 1.4 Preserved Patterns = Kept Head Optimization

CALC's `analysis.preserved` field detects patterns appearing identically on both antecedent and consequent sides (e.g., `code(PC, 0x01)` in `evm/add`). The engine skips consuming and re-producing these facts.

In CHR terms, this is recognizing that some "removed" head entries are immediately re-added in the body. CALC optimizes this by treating them as "kept" at the implementation level (reserved, not consumed). The ILL semantics is unchanged — both the consume-produce and the skip paths yield the same resulting state.

---

## 2. Soundness Transfer (Theorem 4.8)

### 2.1 Statement of Theorem 4.8

**Theorem 4.8 (Soundness, Betz & Frühwirth TOCL 2013):** Let P be a program, CT a constraint theory, Σ = Σ_P ∪ Σ_CT ∪ Σ_=. For arbitrary states S, T:

```
S ↦* T  ⟹  S^L ⊢_Σ T^L
```

Every operational derivation (sequence of state transitions) corresponds to a valid deduction in the linear logic theory. Every reachable state is logically entailed by the initial state.

### 2.2 Transfer to CALC

**Claim: Theorem 4.8 transfers to CALC's forward engine.**

Proof sketch — we must verify the preconditions:

**(a) Rule format:** CALC forward rules are simpagation rules (Section 1.2 above). Each rule `antecedent -o {consequent}` maps directly to the CHR simpagation form. ✓

**(b) Guard semantics:** CALC's `provePersistentGoals` implements guard checking via three phases:
1. FFI direct (arithmetic functions) — these are deterministic built-in constraint evaluators
2. Persistent state lookup (pattern matching) — checks if a persistent fact already exists
3. Backward chaining (logical deduction) — proves the guard via clauses

All three are sound w.r.t. the constraint theory CT: they only succeed when the guard is logically entailed by the current state. FFI implements ground evaluation of built-in relations (inc, plus, neq, etc.). State lookup checks membership. Backward chaining derives from axioms. ✓

**(c) State representation:** CALC's state `{ linear: {h: count}, persistent: {h: true} }` is a multiset of linear facts plus a set of persistent facts, exactly matching CHR's `⟨U; B; V⟩` where U = linear facts, B = persistent facts. ✓

**(d) Transition:** `mutateState` consumes linear antecedent facts and produces consequent facts, exactly matching the CHR Apply transition. The mutation+undo mechanism doesn't affect semantics (it's an implementation strategy for tree exploration). ✓

### 2.3 Gaps and Conditions

**Gap 1: Loli-in-monad (CALC extension).** CALC allows `A -o B` in rule consequents. This is NOT present in standard CHR. However, a loli continuation is just a one-shot rule added to the state. The `matchLoli` function fires it by consuming the loli fact and its trigger, then producing the body. This is itself a simpagation step: the loli and its trigger are the removed head, the body is produced. Soundness holds because loli-left is a valid ILL derivation rule.

**Gap 2: Loli as delayed simpagation.** When a rule produces `(!G -o {B})`, this creates a pending rule that will fire when `G` becomes provable. The CHR equivalent would be adding a new simpagation rule to the program dynamically. CHR doesn't support dynamic rule addition. However, from the ILL perspective, producing `!G -o B` in the state and later applying loli-left to consume it and `!G` to produce `B` is a valid sequence of ILL steps. The soundness theorem applies to each step individually. ✓

**Gap 3: FFI as constraint theory.** CALC's FFI functions (inc, plus, neq, mul, etc.) constitute the constraint theory CT. For soundness, they must be:
- Sound: `ffi.inc(n, m)` succeeds iff `m = n + 1`
- Deterministic for ground inputs
- Pure (no side effects)

This is satisfied by CALC's FFI implementation (`lib/engine/ffi/arithmetic.js`). ✓

**Gap 4: Existential quantification.** Fresh variables in consequents (e.g., `PC'` in `evm/add` bound by `!inc PC PC'`) correspond to the `∃ȳᵣ` in the rule translation. CALC handles this through unification: the persistent goal `!inc(PC, PC')` binds `PC'` as an output. This is semantically equivalent to existential introduction. ✓

### 2.4 Soundness Theorem for CALC

**Theorem (CALC Forward Soundness):** Let R be a set of compiled forward rules, CT be the FFI constraint theory, and S₀ be an initial state. For any state S reachable from S₀ by a sequence of forward steps (rule applications + loli firings):

```
S₀^L ⊢_{Σ_R ∪ Σ_CT} S^L
```

where Σ_R encodes R as CHR simpagation axioms and Σ_CT encodes the FFI functions.

**Proof:** By induction on the derivation length, applying Theorem 4.8 to each step. Each step is either:
1. A compiled forward rule application (covered by simpagation translation)
2. A loli continuation firing (covered by loli-left + simpagation of the pending rule)

Both are sound ILL derivation steps. ∎

---

## 3. CHR∨ Disjunction ↔ CALC's ⊕ in Consequents

### 3.1 CHR∨ Disjunction Translation

From Betz & Frühwirth (TOCL 2013, Section 5):

```
(B₁ ; B₂)^L = B₁^L ⊕ B₂^L
```

For CHR∨ rule `r @ H₁ \ H₂ ⟺ G | (B₁ ; B₂)`:

```
H₁^L ⊗ H₂^L ⊗ G^L  ⊢  H₁^L ⊗ (∃ȳ₁.B₁^L ⊕ ∃ȳ₂.B₂^L) ⊗ G^L
```

The ⊕ (internal choice / "producer decided") is correct because the system decides which branch applies.

### 3.2 CALC's ⊕ in Consequents

CALC's `evm/eq` rule:

```ill
evm/eq:
  pc PC * code PC 0x14 * !inc PC PC' * gas GAS * !plus 2 GAS GAS' *
  sh (s (s SH)) * stack (s SH) X * stack SH Y
  -o {
    pc PC' * gas GAS' * code PC 0x14 * sh (s SH) *
    ((!neq X Y -o { stack SH 0 }) + (!eq X Y -o { stack SH 1 }))
  }.
```

The consequent contains `A + B` (plus), which is ILL's ⊕. After `expandConsequentChoices`, this produces two alternatives:

**Alt 0:** `[pc(PC'), gas(GAS'), code(PC,0x14), sh(s(SH)), loli(bang(neq(X,Y)), monad(stack(SH,0)))]`
**Alt 1:** `[pc(PC'), gas(GAS'), code(PC,0x14), sh(s(SH)), loli(bang(eq(X,Y)), monad(stack(SH,1)))]`

### 3.3 Correspondence Verification

**CHR∨ transition:** `⟨(B₁ ; B₂) ++ G, S, B, T⟩ₙ → ⟨Bᵢ ++ G, S, B, T⟩ₙ` for i ∈ {1,2}

**CALC transition (symexec):** When `findAllMatches` returns a match with `consequentAlts.length > 1`, `explore()` creates a branch node and explores each alternative. For each alternative `i`:
1. `mutateState(state, consumed, theta, alts[i].linear, alts[i].persistent, ...)` — consume antecedents, produce alternative i's facts
2. Recursively explore the resulting state

**Semantic match:**
- CHR∨'s disjunction transition nondeterministically picks one branch → CALC's symexec explores ALL branches (exhaustive ≥ CHR∨'s nondeterministic)
- CHR∨'s `Bᵢ` = CALC's `alts[i]` (the specific choice alternative)
- The loli-in-plus pattern `(!G -o {B₁}) + (!G' -o {B₂})` is a *nested* combination: disjunction at the outer level, then guarded continuation within each branch. CHR∨ handles this as disjunction of guarded rules.

**Soundness extends:** The TOCL 2013 soundness theorem covers CHR∨. Since CALC's ⊕-in-consequent maps exactly to CHR∨ disjunction, and the disjunction transition maps to ⊕ in ILL, soundness transfers. ✓

### 3.4 Semantic Correctness of ⊕ vs &

CALC correctly uses ⊕ (not &) for EVM branching because:
- `⊕` = internal choice = "producer decided" = the system (EVM comparison result) decides which branch
- `&` = external choice = "consumer decided" = the client chooses

For `evm/eq`, the comparison `eq(X,Y)` or `neq(X,Y)` is system-determined. In concrete execution, exactly one branch is taken. In symbolic execution, both branches are explored because the system hasn't decided yet (symbolic values). This is precisely CHR∨'s model: nondeterministic choice that must be exhaustively explored.

---

## 4. Confluence Analysis

### 4.1 Definitions

A CHR program is **confluent** if for every state, all derivations lead to equivalent final states. For terminating programs, confluence is decidable via critical pair analysis (Abdennadher, Frühwirth, Meuss, CP 1996).

Two rules **overlap** if they share a head constraint (both could fire on the same set of facts). The **critical pair** is the pair of states reachable by applying either rule to the overlap.

### 4.2 EVM Rules: Ground Execution

For concrete (non-symbolic) EVM execution:

**Observation:** EVM rules are parameterized by opcode (`code(PC, OPCODE)`). At any state with a single `pc(PC)` fact, at most ONE rule's opcode matches (since the code is fixed). Therefore:

- **No critical pairs from opcode dispatch.** Two different opcode rules never overlap.
- **Loli continuations are one-shot.** After a rule produces a loli `(!G -o {B})`, the loli is consumed when it fires. No overlap.
- **Determinism:** Ground EVM execution is deterministic — exactly one rule fires at each step.

**Theorem (EVM Ground Confluence):** For ground initial states (all values concrete), the EVM rule set is confluent (trivially, since execution is deterministic).

### 4.3 EVM Rules: Symbolic Execution

For symbolic execution, confluence does NOT hold:
- `evm/eq` produces `(!neq(X,Y) -o ...) + (!eq(X,Y) -o ...)` — the ⊕ creates a choice point
- Both branches lead to different final states (stack 0 vs stack 1)
- This is intentional: symbolic execution explores all branches

**This is expected.** CHR∨ programs with disjunction are inherently non-confluent (disjunction introduces don't-know nondeterminism). The execution tree represents ALL possible outcomes, not a single deterministic result.

### 4.4 Critical Pairs: Helper Rules

CALC's helper rules (e.g., `concatMemory/z`, `concatMemory/s`, `calldatacopy/z`, `calldatacopy/s`) could have critical pairs:
- `concatMemory/z` fires when `Pos = To`, `concatMemory/s` fires when `Pos ≠ To`
- The guards `!neq Pos To` and the structural match `concatMemory X X Z` are mutually exclusive

**No critical pairs.** The guard/structural conditions make the helper rules mutually exclusive.

### 4.5 Conclusion

| Execution mode | Confluent? | Reason |
|---|---|---|
| Ground (concrete values) | Yes | Opcode dispatch is deterministic; guards are ground-decidable |
| Symbolic (unknown values) | No (by design) | ⊕ creates choice points; execution tree enumerates all branches |
| Helper rules | Yes | Guards are mutually exclusive |

---

## 5. Compilation Techniques

### 5.1 What CHR Compilation Offers

| CHR technique | Description | CALC equivalent |
|---|---|---|
| **Occurrence indexing** | Per-constraint procedure; try each rule occurrence | Strategy stack (fingerprint → disc-tree → predicate) |
| **Join ordering** | Reorder heads by selectivity; match most selective first | Partial: deferral for persistent deps; no selectivity ordering |
| **Guard scheduling** | Interleave guard tests with partner search | Partial: `tryFFIDirect()` inlines FFI; deferred patterns wait for persistent bindings |
| **Constraint indexing** | Hash-table on argument positions | `stateIndex` (predicate-grouped), `_byKey` (secondary), disc-tree |
| **Continuation optimization** | Skip further occurrences after removed head fires | N/A (CALC's rules are one-shot: consumed = done) |
| **Propagation history** | Prevent re-firing on same constraint IDs | N/A (linear consumption prevents re-firing) |
| **Active constraint** | Drive execution from newly added constraints | Not yet: CALC re-scans all candidates per step |

### 5.2 What CALC Already Has Beyond CHR

| CALC optimization | CHR equivalent |
|---|---|
| **Fingerprint layer** (O(1) opcode lookup) | First-argument indexing (but CALC's is cross-rule, based on auto-detected discriminator) |
| **Disc-tree** (pattern trie) | More sophisticated than standard CHR hash indexing; handles variable patterns |
| **Delta bypass** (direct child extraction) | No CHR equivalent; exploits content-addressed store for O(1) binding |
| **Preserved-skip** | No CHR equivalent; recognizes kept+removed overlap |
| **Compiled substitution** | Some CHR compilers do this (JCHR, CCHR); not standard |
| **Mutation+undo** | CHR systems use trailing for backtracking; CALC's flat undo log is more efficient |

### 5.3 Concrete Improvements Available

**Join ordering (priority: medium, at scale):** CALC's `tryMatch` matches linear patterns in declaration order (with deferral for unbound deps). CHR join ordering suggests: at compile time, reorder patterns by estimated selectivity (fewer matching facts → try first). For 44 EVM rules this matters little (strategy stack handles it). At 400+ rules with complex multi-head joins, it would reduce failed match attempts.

**Active constraint / delta-driven activation (priority: high, at scale):** CHR's refined semantics activates rules from newly added constraints. CALC currently re-scans all candidates per step. Adopting delta-driven activation (only try rules whose trigger predicates overlap with changed facts) would give TREAT-style dirty tracking:

```
// After mutateState, track which predicates changed
changedPreds = {preds from consumed facts ∪ preds from produced facts}
// Only re-evaluate rules whose triggerPreds ∩ changedPreds ≠ ∅
```

This is already sketched in `doc/research/forward-chaining-networks.md` as the TREAT optimization. At 44 rules with ~3-4 predicates changing per step, this would skip ~80% of rule evaluations.

**Guard scheduling (priority: low):** CALC already has `tryFFIDirect()` which inlines FFI checks. The remaining opportunity: for rules with multiple persistent antecedents, try the cheapest/most-selective guard first. Currently CALC proves persistent goals in declaration order. Reordering by: (1) FFI-provable goals first (O(1)), (2) state-lookup goals second, (3) backward-chaining goals last, would short-circuit faster on guard failures. This is already approximately what happens due to `provePersistentGoals`'s try-FFI-first strategy, but the pattern ordering could be optimized at compile time.

---

## 6. Research Tasks

- [x] Read Betz & Frühwirth CP 2005, TOCL 2013 papers (key results extracted)
- [x] Map CALC's specific rule format to CHR simpagation translation (Section 1)
- [x] Verify Theorem 4.8 soundness transfers — transfers with identified gaps (Section 2)
- [x] Map CHR∨ disjunction to CALC's `⊕` in consequents (Section 3)
- [x] Analyze confluence for EVM rule set (Section 4)
- [x] Extract concrete compilation improvements (Section 5)
- [ ] Integrate findings into `doc/theory/exhaustive-forward-chaining.md`
- [ ] Write ANKI flashcards for key results

## References

- `doc/research/chr-linear-logic.md` — comprehensive CHR survey
- `doc/theory/exhaustive-forward-chaining.md` — CALC's theoretical position
- `doc/research/forward-chaining-networks.md` — production system algorithms
- Betz & Frühwirth (2005) "A Linear-Logic Semantics for CHR" CP 2005
- Betz & Frühwirth (2013) "CHR with Disjunction" ACM TOCL 14(1) — [arXiv 1009.2900](https://arxiv.org/abs/1009.2900)
- Stéphan (2018) "A New Proof-Theoretical Linear Semantics for CHR" ICLP 2018
- Betz (2014) PhD thesis: unified framework
- Simmons & Pfenning (2008) "Linear Logical Algorithms" ICALP 2008 — [PDF](https://www.cs.cmu.edu/~fp/papers/icalp08.pdf)
