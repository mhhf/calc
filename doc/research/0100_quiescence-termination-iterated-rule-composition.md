---
title: "Termination of Iterated Rule Composition (qui)"
created: 2026-03-31
modified: 2026-03-31
summary: "Conditions under which the iterated rule-composition fixpoint operation qui(X) terminates, with analysis of the four canonical cases and the key structural invariant."
tags: [linear-logic, forward-chaining, cut-elimination, termination, quiescence, proof-theory, multicategory, multiset-rewriting]
category: "Forward Chaining"
---

# Termination of Iterated Rule Composition (`qui`)

## The `qui` Operation

`qui(X)` takes a set of ILL forward rules `X` and repeatedly composes pairs of rules that share an *internal* resource type (one not in the module's external interface), until no new distinct composed rules can be added. The result is a new rule set whose rules only mention external types.

Formally, for a set of rules `R` and a set of internal types `I`:

```
qui₀(X) = X
quiₙ₊₁(X) = quiₙ(X) ∪ { R₁;R₂ | R₁,R₂ ∈ quiₙ(X), R₁;R₂ not yet in quiₙ(X),
                              the cut type is in I }
qui(X) = lfp(X)   (least fixpoint)
```

The central question: does this fixpoint always exist (does the sequence stabilise)?

---

## Why Single-Step Cut Elimination Always Terminates

A single application of the cut rule on a specific type `M` in a pair of rules `(R₁, R₂)` always produces a finite result. The composed rule has:
- antecedent = (antecedent of R₁) ∪ (antecedent of R₂) \ {M-slot}
- consequent = (consequent of R₁) ∪ (consequent of R₂) \ {M-slot}

This is a finite syntactic operation. It terminates trivially.

The non-trivial question is whether the *iteration* terminates — whether the set of generated rules is finite.

---

## The Four Cases

### Case 1: Acyclic Internal Types — Terminates

If no rule both produces and consumes the same internal type, the dependency graph on internal types is acyclic. Order types by topological distance from the "all-base" level. Each composition step strictly reduces the maximum depth of internal types present in any rule's consequent. The sequence stabilises in at most `d` rounds, where `d` is the depth of the longest chain of internal types.

**Example (EVM):** `step` is produced by `step/make` (from base types) and consumed by `evm/add`, `evm/sub`, etc. (producing base types). No rule both produces and consumes `step`. The type graph is a DAG. After one round of composition, all composed rules are over base types. `qui` terminates in 1 round.

This is the normal case for well-structured modular encodings. It corresponds to the conservative extension conditions in RES_0099: the internal type is a "pure internal wire" with no feedback.

### Case 2: Self-Consuming Rule — Terminates

```
r2: foo X -o { foo (s X) }.
```

Here `foo` both appears in the antecedent and consequent of the same rule. After composing `r2` with itself:

```
r22: foo X -o { foo (s (s X)) }.
```

This produces a new rule (different term structure in the consequent). Composing `r22` with `r2` gives:

```
r222: foo X -o { foo (s (s (s X)) }.
```

**This does NOT terminate.** Each round generates a genuinely new rule because the term structure in the consequent grows unboundedly. The fixpoint is infinite (contains rules for all nesting depths of `s`).

This is Case 3 from the problem statement — the "productive cycle." See below for the full characterisation.

### Case 3: Cycles Through Distinct Types — Terminates When No Growth

```
r1: A -o { foo X }.
r2: foo X -o { bar Y }.
r3: bar Y -o { foo Z }.
r4: foo Z -o { B }.
```

Compositions: `(r1,r2) → r12: A -o {bar Y}`, `(r2,r3) → r23: foo X -o {foo Z}`, `(r3,r4) → r34: bar Y -o {B}`, `(r12,r3) → r123: A -o {foo Z}`, `(r1, r23) → r123': A -o {foo Z}` (same as `r123` up to content-addressing), `(r12,r34) → r1234: A -o {B}`, etc.

The key question is: do `r23` and `r123` compose with themselves or each other to produce anything new?
- `r23: foo X -o {foo Z}` — both consumes and produces `foo`. Composing `r23` with itself: `r23;r23: foo X -o {foo Z'}`. But this is the *same* rule as `r23` (the variable names differ but the structure `foo _` → `foo _` is identical up to alpha-equivalence and content-addressing). So `r23;r23 ≡ r23`. **No new rule.**

Why? Because the terms inside `foo` in this example are free variables — they have no internal structure. The composition just renames variables. When the composed consequent and the original consequent are alpha-equivalent, the content-addressed hash is the same, and the fixpoint stabilises.

**This terminates** because: although there is a cycle (`foo → bar → foo`), the compositions through the cycle produce rules with the same *type structure* as existing ones. No new shapes appear.

### Case 4: Productive Cycle — Does Not Terminate

```
r1: A -o { inc (s X) }.      -- produces inc with a successor
r2: inc X -o { inc (s X) }.  -- consumes inc, produces inc with deeper nesting
```

Round 1: `(r1,r2) → r12: A -o { inc (s (s X)) }`
Round 2: `(r12,r2) → r122: A -o { inc (s (s (s X))) }`
Round 3: ...

Each round produces a rule with a strictly deeper term `s(s(...s(X)...))`. These are all distinct content-addressed hashes. The fixpoint is infinite.

**The distinguishing property:** In Case 4, the output term of the composed rule is *strictly larger* than the output term of either input rule. The composition is "productive" — it generates new shapes, not just renamings of old ones.

---

## The Decidable Termination Criterion

`qui(X)` terminates if and only if the internal-type dependency graph is **non-productive**, defined as follows:

**Definition.** The *composition graph* has one node per forward rule. There is an edge from `R₁` to `R₂` (labelled by internal type `M`) iff the consequent of `R₁` contains `M` and the antecedent of `R₂` contains `M`. A cycle in this graph is *productive* if traversing the cycle generates a composed rule whose consequent term is strictly larger (in a well-founded term order) than the corresponding consequent term of any rule in the cycle.

**Theorem (informal, from TRS termination literature).** `qui(X)` terminates iff there is no productive cycle.

**Sufficient condition for termination (practical):** If every internal type `M` is such that no rule both produces and consumes `M` in a way that strictly increases the term structure of `M`, then `qui(X)` terminates. In particular:

1. **No internal type appears in both the antecedent and consequent of the same rule.** (Strongest sufficient condition; rules out all self-loops in the composition graph.)
2. **Every rule that produces M from M does so with a substitution that is not "deeper" (the output term is no larger than the input term in a fixed simplification order).** (Weaker; allows cycles but bans growth.)

The EVM case satisfies condition 1: `step` is produced by `step/make` and consumed by `evm/*` rules; no rule consumes `step` and produces `step`.

---

## The Critical Insight: Internal Types as Internal Wires

From the categorical perspective (RES_0099, Meseguer-Montanari 1990), an internal type `M` is an **internal wire** in a string diagram. Composition plugs wires together. The fixpoint stabilises when all internal wires have been eliminated.

A productive cycle corresponds to a **feedback loop** in the string diagram — a wire that feeds back into the same box (or chain of boxes that form a cycle). Feedback loops do not terminate naturally; they require a separate fixpoint semantics (traced monoidal categories, Conway operators, etc.).

**Petri net translation:** Map each rule to a transition, each type to a place. A productive cycle corresponds to a **strongly connected component** where a transition `T` both removes tokens from place `P` and adds tokens to place `P` with a strictly larger multiplicity (bounded by term structure depth). Series-place reduction (Berthelot 1987) terminates for *series places* — places that are on no cycle in the Petri net. This is exactly condition 1 above.

**Term Rewriting System (TRS) connection:** Each internal-type elimination step is a rewrite. The system terminates iff there exists a *reduction order* (monotone well-founded order) that orients every rewrite step strictly downward. This is exactly the standard TRS termination problem (Dershowitz 1987). The termination criteria for TRS (lexicographic path ordering, Knuth-Bendix ordering, polynomial interpretations) all apply.

---

## Standard Results from the Literature

### Cut Elimination Termination in Proof Theory

Gentzen's original proof of cut elimination for LK (1935) uses a measure (cut degree + height) and shows strict decrease at each step. The measure terminates because cut degree is finite and decreases. This works for *single* cut eliminations, not iterated composition of a rule set.

Girard (1987) extends this to ILL. The termination measure for linear logic cut elimination involves the *size* of the cut formula and the *height* of the derivation. For multiplicative ILL (no `!`), the CEP is PTIME-complete (Mairson-Terui 2003) — polynomial cost. For `!`, it is non-elementary in general.

**Key: these results address one fixed derivation tree, not an open-ended rule composition fixpoint.**

### Partial Deduction Termination

Partial deduction (Lloyd-Shepherdson 1991, Leuschel 1997) faces exactly the analogous problem for classical logic programs. Unfolding a clause (composing two rules) can produce an infinite sequence if the program is recursive.

The standard solution is a **well-quasi-order (WQO) test**: before unfolding, check if the resulting specialised clause is subsumed by an existing one. If so, don't add it. The process terminates iff the sequence of new clauses is *WQO-bounded* — no infinite antichain exists.

For linear logic programs, Küngas-Matskin (DALT 2004) adapt this: they require the intermediate atom to appear in *exactly one* rule's body (no recursion through the intermediate). This is precisely condition 1.

**Global control** (Leuschel-Bruynooghe 1991): a well-known technique for partial deduction termination, using a WQO on clause instances to ensure the set of generated clauses is finite. For the `!`-Horn fragment of linear logic, the same technique applies: stop composing when the new rule is subsumed by an existing one.

### CHR Termination

Termination of CHR programs (Frühwirth 1998, Voets et al. 2007) is undecidable in general but has decidable sufficient conditions. For *simplification rules* (all heads removed), there is a natural reduction order: the *multiset ordering* on the head multiset. If every rule strictly reduces the multiset, the program terminates.

Translating to `qui`: each composition step eliminates one token of an internal type and adds tokens of other types. The program terminates if there is a monotone ordering on type tokens under which every composition step is decreasing. When internal types are not produced by any rule in the *composed* set (condition 1), they can only decrease, guaranteeing termination.

### Petri Net Liveness and Termination

A Petri net is **terminating** iff it has no infinite firing sequence. Termination is decidable (Hack 1976) but EXPSPACE-hard. For the special case of *conflict-free nets* (every place has at most one output transition) with internal places only reachable from initial marking, termination follows from acyclicity of the place-transition graph.

For the composition fixpoint: each internal type is a place. Each composition step fires two transitions and removes the intermediate place. The process terminates iff there are no persistent internal places — i.e., no place that survives all composition steps. This holds iff the composition graph is acyclic (condition 1 again).

---

## The EVM Case: Termination Proof

**Claim:** For the EVM rule set in CALC, `qui(X)` terminates in at most 2 rounds.

**Proof sketch:**
1. The internal types are `step` (and potentially `dispatch`, `dispatch_re`, etc.).
2. For each internal type `M`, examine the rule set:
   - `step` is produced by `step/make` from base types (`bytecode`, `pc`, `gas`, `!arr_get`, `!inc`, `!checked_sub`).
   - `step` is consumed by `evm/add`, `evm/sub`, ..., `evm/mstore`, etc., producing base types.
   - **No rule both produces and consumes `step`.** The composition graph for `step` is bipartite (producers on one side, consumers on the other). No cycles.
3. After one composition round: `step/make ; evm/X` for each `evm/X`. The resulting rules contain no `step`. They may contain `dispatch_re` (if present).
4. If `dispatch_re` appears: same analysis — one producer (`dispatch/expand` or the composition above), multiple consumers, no cycles. One more round eliminates it.
5. After 2 rounds at most, all composed rules are over base types. The fixpoint is the original rules plus the composed rules. No further compositions are possible (no internal types in any rule). `qui` terminates.

The number of rules generated is bounded by (number of producers × number of consumers) per internal type. For `step`: 1 producer × ~100 consumers = ~100 composed rules. All finite.

---

## Characterisation Summary

| Structure | Terminates? | Condition |
|---|---|---|
| No rule produces an internal type from an internal type | Yes | Type graph is a DAG (bipartite producer-consumer split) |
| Cycle through distinct internal types, no term growth | Yes | Alpha-equivalent compositions collapse to existing rules |
| Self-consuming rule, variables only (no term structure) | Depends | If composition is idempotent modulo renaming → yes |
| Self-consuming rule, strictly growing terms | No | Productive cycle; generates infinite new rules |
| Any rule consumes and produces M with strictly larger terms | No | Standard non-termination |

**Practical sufficient condition for termination of `qui(X)`:**

> For each internal type `M`: the set of rules that both consume and produce `M` (when composed transitively) must not create terms that grow strictly in any well-founded order on the structure of `M` arguments.

**Simplest sufficient condition (used for EVM):**

> No rule in `X` both consumes and produces the same internal type (i.e., `M` never appears on both sides of any single rule, and `M` is not produced by any composed rule that also consumes `M`).

Equivalently: the composition graph restricted to internal types has no directed cycles.

---

## Design Implication for CALC

To guarantee termination of `qui(X)` statically at compile time:

1. **Annotate internal types** (e.g., types defined in the module but not exported).
2. **Check** that the composition dependency graph on internal types is a DAG (polynomial-time graph cycle detection).
3. **If DAG:** `qui(X)` terminates; proceed with composition.
4. **If cycle detected:** Report an error. The user must either:
   - Break the cycle (restructure the rules)
   - Mark the cycle as intentional (leave it uncomposed — the engine handles it at runtime)
   - Bound the composition depth manually

This check is sound (never says "terminates" when it doesn't), but not complete (may reject some terminating productive cycles — conservative). For the EVM use case, it always passes.

---

## References

### Termination of Rule Rewriting / Partial Deduction
- Dershowitz, N. (1987). "Termination of Rewriting." *Journal of Symbolic Computation*, 3(1-2):69-116. — standard termination orderings (LPO, KBO, polynomial)
- Lloyd, J.W. and Shepherdson, J.C. (1991). "Partial Evaluation in Logic Programming." *Journal of Logic Programming*, 11(3-4):217-242.
- Leuschel, M. and Bruynooghe, M. (1991). "Logic Program Specialisation through Partial Deduction: Control and Correctness." *Theory and Practice of Logic Programming*, 2(4-5):461-515. — global control for PD termination
- Küngas, P. and Matskin, M. (2004). "Partial Deduction for Linear Logic." *DALT 2004*, LNCS 3476.

### Petri Net Termination and Series-Place Reduction
- Hack, M. (1976). "Decidability Questions for Petri Nets." MIT LCS TR-161.
- Berthelot, G. (1987). "Transformations and Decompositions of Nets." *Advances in Petri Nets*, LNCS 254.
- Meseguer, J. and Montanari, U. (1990). "Petri Nets Are Monoids." *Information and Computation*, 88(2):105-155.

### CHR Termination
- Frühwirth, T. (1998). "Theory and Practice of Constraint Handling Rules." *Journal of Logic Programming*, 37(1-3):95-138.
- Voets, D. et al. (2007). "Automatic Termination Analysis of CHR Programs." *ICLP 2007*.

### Cut Elimination
- Gentzen, G. (1935). "Untersuchungen über das logische Schließen." *Math. Z.*, 39:176-210, 405-431.
- Girard, J.-Y. (1987). "Linear Logic." *Theoretical Computer Science*, 50(1):1-102.
- Mairson, H. and Terui, K. (2003). "On the Computational Complexity of Cut-Elimination in Linear Logic." *ICTCS 2003*, LNCS 2841.

### Categorical and String-Diagram Perspective
- Baez, J. and Stay, M. (2009). "Physics, Topology, Logic and Computation: A Rosetta Stone." arXiv:0903.0340. — traced monoidal categories handle feedback
- Joyal, A., Street, R., and Verity, D. (1996). "Traced Monoidal Categories." *Math. Proc. Cambridge Philos. Soc.*, 119(3):447-468. — formal treatment of feedback in monoidal categories

### Well-Quasi-Order and Finite Fixpoints
- Higman, G. (1952). "Ordering by Divisibility in Abstract Algebras." *Proc. London Math. Soc.*, 2(2):326-336.
- Kruskal, J.B. (1960). "Well-Quasi-Ordering, the Tree Theorem, and Vazsonyi's Conjecture." *Trans. AMS*, 95(2):210-225. — Kruskal's tree theorem; term structures are WQO under embedding
