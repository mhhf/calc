# Exhaustive Forward Chaining in MALL with the Lax Monad

CALC's forward engine extends CLF in ways that constitute a novel theoretical position. This document articulates what that position is, where it departs from existing theory, and what remains to be formalized.

## CLF Baseline

CLF (Watkins, Cervesato, Pfenning, Walker 2002-2004) integrates forward and backward chaining via the lax monad `{A}`:

- **Outside monad:** backward chaining (goal-directed, backtracking)
- **Inside monad:** forward chaining (data-driven, committed choice)
- **Monad restriction:** only atoms, `tensor`, `1`, `!`, `exists` inside `{A}` — no lolis, no additives
- **Termination:** quiescence (no rules can fire)
- **Nondeterminism:** don't-care (commit to one rule, no backtracking)

Implementations: Celf (Standard ML), LolliMon (Lolli + monad), Ceptre (simplified CLF for games, adds stages).

## CALC's Three Extensions

### 1. Lolis Inside the Monad (Guarded Continuations)

CLF forbids `loli` inside `{A}`. CALC allows it:

```ill
evm/iszero: ... -o {
  ... * ((!eq V 0 -o { stack SH 1 }) + (!neq V 0 -o { stack SH 0 }))
}.
```

A loli `A -o B` in the state is a **latent rule** / **continuation** — it fires when its trigger becomes available (matched in state or proved via backward chaining). This is theoretically the loli-left rule applied to facts in state. See [TODO_0041](../todo/0041_unified-rule-matching.md) for the implementation unification.

**Why CLF forbids this:** lolis in the monad create "dormant rules" needing a separate scheduling/firing mechanism. CLF avoids this complexity. Monadic let (`{A} tensor (A -o {B}) -o {B}`) provides sequencing between rules, making in-monad lolis redundant for sequencing. But CALC needs them for **conditional production** — "if guard holds, produce these facts" — which monadic let doesn't express within a single rule's consequent.

**Theoretical status:** the firing mechanism for loli-in-state is just loli-left. The extension is sound provided lolis compete equally with compiled rules (the TODO_0041 priority bug violates this). After unification, the operational semantics is: at each step, select any fireable rule OR any fireable loli continuation.

**Linearity safety:** a loli `!A -o B` produced by a rule consequent is LINEAR — it fires once and is consumed. The concern that `!A -o B` could behave like `!(A -o B)` (persistent, infinite firing) is prevented by bang_r's promotion rule, which requires the linear context to be empty. Since `!A -o B` = `loli(bang(A), B)` is itself a linear formula (not bang-wrapped), it occupies the linear context, blocking promotion. The derivation `!A -o B |- !(A -o B)` is not valid in ILL. Only the converse holds (dereliction). This structural guarantee is what makes loli-in-monad sound without risk of infinite resource production.

### 2. Additives (plus) in Forward Consequents

CLF's monad excludes additives. CALC uses `plus` (internal choice) in forward-chaining consequents:

```ill
evm/eq: ... -o { ... * ((stack SH 0 * !neq X Y) + (stack SH 1 * !eq X Y)) }.
```

This means: the rule produces a disjunction. Both branches must be explored because the result depends on symbolic values (or is undecidable at this point).

**plus-left is invertible** — case-split eagerly. In the forward engine, `expandItem` forks into alternatives. Each alternative gets the full shared context (no linear resource duplication — branches are alternatives, not parallel).

**Semantic fit:** `plus` (internal choice / "producer decided") is correct for deterministic comparisons — the system has decided, the consumer handles both cases. `with` (external choice / "consumer decides") is correct for interactive/nondeterministic choice.

**Existing related work:**
- Forum (Miller 1996): full linear logic specification logic including additives — proof-theoretic, not operational
- CHR-disjunction (Betz & Fruhwirth 2013): disjunctive rule heads in CHR, mapped to linear logic via `plus`. Soundness and completeness proved. This is the closest existing result — their semantics could give a direct soundness proof for CALC's `plus`-in-forward
- No practical system (CLF, Celf, LolliMon, Ceptre) puts additives in forward chaining

### 3. Exhaustive Exploration (Don't-Know Nondeterminism)

CLF uses committed choice: pick one applicable rule, fire it, no backtracking. The execution produces a single trace.

CALC's symexec explores **all** execution paths, building an execution tree. At each state:
- If multiple rules can fire → branch on all of them
- If a rule produces `plus` → fork into alternatives
- If a state was seen before → cycle (back-edge)
- If no rules can fire → quiescent leaf

This is don't-know nondeterminism over don't-care nondeterminism. The execution tree is the **universal quantification** over all possible rule selections: CLF gives `exists trace. S ->* Q`; symexec gives the full tree `T` where every path from root to leaf is a valid trace.

**Connection to model checking:** the execution tree IS a Kripke structure. Properties over leaves are CTL queries. Cycle detection (via `pathVisited` hash set) provides bounded completeness for finite-state systems.

## The Layered Extension

```
Layer 0: ILL (Girard 1987)
  | add lax monad
Layer 1: CLF (Watkins+ 2004) — backward + forward, committed choice
  | add exhaustive exploration
Layer 2: Symexec — don't-know nondeterminism over forward steps
  | add plus in consequents
Layer 3: Case-splitting execution trees — symbolic branching
  | add guarded continuations (loli in monad)
Layer 4: Guarded conditional branching — the full picture
  | add expression simplification / constraint accumulation
Layer 5: Symbolic arithmetic — the practical completion
```

Layers 0-1: established theory. Layer 2: working implementation, no formalization. Layer 3: added with `plus` connective. Layer 4: TODO_0041. Layer 5: TODO_0002.

## Formal Judgment (Proposed)

The execution tree judgment: `Sigma; Delta |-_fwd T : A`

- `Sigma` = persistent rules (compiled forward rules)
- `Delta` = linear state (multiset of linear facts, including loli continuations)
- `T` = execution tree
- `A` = goal type (or unconstrained for exhaustive exploration)

Tree constructors:
- `leaf(Delta_q)` — quiescent state (no rules fire)
- `step(r, theta, T')` — deterministic step: rule `r` with substitution `theta`, continuing to `T'`
- `fork(T_1, T_2)` — plus case split (from `plus` in consequent)
- `branch(r_1, T_1, ..., r_n, T_n)` — nondeterministic branch (multiple rules can fire)
- `cycle(Delta)` — back-edge to previously seen state
- `bound(Delta)` — depth limit reached

**Soundness theorem (to prove):** every leaf `Delta_q` in `T` is reachable from the initial `Delta` by a sequence of valid forward steps.

**Completeness theorem (for finite states):** every reachable quiescent state appears as a leaf in `T`.

## Key Correspondences

| Linear Logic | Forward Engine | Symexec |
|---|---|---|
| `!(A -o {B})` | Compiled rule (persistent) | Strategy stack + tryMatch |
| `A -o B` in state | Loli continuation (linear) | Same pipeline (after TODO_0041) |
| `A plus B` in consequent | Fork alternatives | Branch node in tree |
| `!P` in antecedent | Backward proving / FFI | Phase 2 of tryMatch |
| Quiescence | No rules fire | Leaf node |
| Multiset rewriting | mutateState / undoMutate | Mutation+undo pattern |
| Focusing (Andreoli) | Strategy stack layers | Fingerprint -> disc-tree -> predicate |

| CHR | CALC | ILL |
|---|---|---|
| Simplification `H <=> B` | Linear antecedent, linear consequent | `H^L ⊢ ∃ȳ.B^L` |
| Propagation `H ==> B` | Persistent antecedent, linear consequent | `!H^L ⊢ !H^L ⊗ ∃ȳ.B^L` |
| Simpagation `H1 \ H2 <=> G \| B` | Persistent + linear ante, guard (FFI), consequent | `H₁^L ⊗ H₂^L ⊗ G^L ⊢ H₁^L ⊗ ∃ȳ.B^L ⊗ G^L` |
| CHR∨ disjunction `H <=> B1 ; B2` | `plus` in consequent | `H^L ⊢ B₁^L ⊕ B₂^L` |
| Guard `G` | FFI / backward proving | `!G^L` (banged, appears both sides) |
| Propagation history | N/A (linear consumption prevents re-fire) | — |
| Active constraint | Strategy stack | — |

## Open Theoretical Questions

### Q1: Existentials in the Monad

CLF allows `exists` inside `{A}` — forward rules can create fresh names. CALC doesn't have this yet. For symexec, eigenvariables (symbolic values) ARE existentially quantified. Making `exists` explicit would:
- Give clean semantics to fresh symbolic values
- Connect to Skolemization (TODO_0002's R1 approach)
- Enable the "loli-freeze" pattern (TODO_0002's R2) with proper quantifier scoping

### Q2: Semi-Naive Evaluation for Linear Logic

No published work addresses Datalog-style semi-naive evaluation when facts can be consumed. CALC's strategy stack (indexing, not incrementality) sidesteps the problem. For very large state spaces, incremental matching would matter. This is an open research problem where CALC could contribute.

### Q3: Soundness via CHR-Disjunction ✓ (Resolved — TODO_0043)

Betz & Frühwirth (2013) proved soundness for CHR∨ with disjunction mapped to ILL via ⊕. CALC's forward engine maps directly to CHR simpagation, and ⊕-in-consequent maps to CHR∨ disjunction. **Theorem 4.8 (Soundness) transfers:** every CALC forward derivation `S₀ ↦* S` implies `S₀^L ⊢_Σ S^L` in ILL.

Key points:
- CALC forward rules = CHR simpagation (persistent ante = kept head, linear ante = removed head, FFI = guard)
- `⊕` in consequent = CHR∨ disjunction `(B₁ ; B₂)^L = B₁^L ⊕ B₂^L`
- Loli-in-monad = dynamic simpagation rule (sound via loli-left + per-step induction)
- EVM rules are confluent for ground execution (deterministic opcode dispatch)
- See [TODO_0043](../todo/0043_chr-linear-logic-mapping.md) for full analysis

### Q4: Relationship to Focusing

The strategy stack (fingerprint -> disc-tree -> predicate) is a manually constructed focused proof search strategy for the forward fragment. Andreoli's focusing says: apply invertible rules eagerly (inversion phase), then choose a formula and decompose synchronously (focus phase). The strategy stack does exactly this — it's focusing compiled into indexing. Formalizing this connection would explain why the strategy stack is correct.

### Q5: Execution Trees as Proofs

Is the execution tree itself a proof object? In what logic? Possibilities:
- A proof in branching-time linear logic (CTL over ILL states)
- A proof in muMALL (MALL with fixed points) — the tree's finite depth witnesses termination
- A metaproof about the object-level ILL program

## References

**Foundational:**
- Girard (1987) — Linear Logic. TCS 50(1):1-102
- Andreoli (1992) — Focusing Proofs in Linear Logic. JLC 2(3):297-347
- Watkins, Cervesato, Pfenning, Walker (2004) — CLF. Types for Proofs and Programs, LNCS 3085
- Lopez, Pfenning, Polakow, Watkins (2005) — LolliMon. PPDP 2005

**Forward chaining:**
- Simmons, Pfenning (2008) — Linear Logical Algorithms. ICALP 2008
- Simmons (2012) — Substructural Logical Specifications. PhD thesis, CMU-CS-12-142
- Martens (2015) — Programming Interactive Worlds with Linear Logic. PhD thesis, CMU

**CHR connection:**
- Betz, Fruhwirth (2005) — Linear-Logic Semantics for CHR. CP 2005
- Betz, Fruhwirth (2013) — CHR with Disjunction. ACM TOCL 14(1)

**Focusing and polarity:**
- Chaudhuri, Pfenning, Price (2006) — Forward and Backward Chaining in the Inverse Method. IJCAR 2006
- Liang, Miller (2009) — Focusing and Polarization. TCS 410(46):4747-4768
- Chang, Chaudhuri, Pfenning (2003) — Judgmental Analysis of Linear Logic. CMU-CS-03-131R

**Multiset rewriting:**
- Cervesato, Scedrov (2009) — State-Based and Process-Based Concurrency. I&C 207(10):1044-1077
- Cruz, Rocha, Goldstein, Pfenning (2014) — Linear Meld. TPLP 14(4-5):493-507

**Symbolic execution:**
- Miller (1996) — Forum: A Multiple-Conclusion Specification Logic
- Berdine, Calcagno, O'Hearn (2005) — Symbolic Execution with Separation Logic. APLAS 2005
