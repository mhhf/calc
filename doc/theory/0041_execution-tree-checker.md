---
title: "The Execution-Tree Judgment, Machine-Checked"
created: 2026-09-10
modified: 2026-09-10
summary: "The forward twin of the backward kernel: a checker (lib/prover/forward-check.js) that verifies a WHOLE explore() tree against the ⊢_fwd judgment (THY_0035) with all eight typed constructors, re-deriving every firing from the program rule data under the recorded substitution θ and threading the linear multiset Δ and persistent set Φ down the tree. It makes ⊢_fwd checkable at the TREE level, not just per settle-run (certifyRun) — generalizing the timed face's elaborate-trace to untimed exhaustive exploration. Soundness (every leaf is reachable) is discharged per-tree with θ as the only trusted witness; completeness (quiescence, justified pruning, all-rules-present) is the irreducible oracle residue and stays with TODO_0042."
tags: [forward-chaining, engine-metatheory, certificates, multiset-rewriting, proof-theory, execution-tree]
category: "Engine metatheory"
unique_contribution: "A TREE-level forward-chaining certificate checker. CLF/Ceptre/SLS state a forward judgment for a single committed-choice trace and trust their interpreter; the timed face's certifyRun checks ONE settle run elaborated into a backward proof. This checks the whole exhaustive execution tree — a game tree with ⊕-fork and rule-branch nodes — as one object, re-deriving each of the eight constructors' edges from the declarative rule patterns with the substitution θ as the sole witness. The precise result is the honest trust-boundary split realized in code: whole-tree SOUNDNESS is certificate-checkable (the leaf set is exactly the derivable reachable set), while the tree's three COMPLETENESS claims — a leaf's quiescence, a dead node's justified prune, a branch's all-rules-present — are negative/universal assertions no certificate can witness, so they are named as the oracle residue (findAllMatches + the pruner) rather than papered over."
references:
  - "THY_0035 (the parametric ⊢_fwd judgment Σ;Φ ⊢_fwd T : Δ ⇒ 𝔏 and its typed term language — this checker's object; §7's 'branch nodes are the object' is what is now checked)"
  - "TODO_0045 (this deliverable: §2 the eight constructors, §3.3 Approach B — per-path certificates — here generalized to the whole tree; §5.4 the completeness-needs-an-oracle argument realized as the checker's stated boundary)"
  - "TODO_0042 (the completeness follow-on: explore() adequacy via the QCHR ω^{∃∀} game-tree correspondence — the negative the checker cannot witness)"
  - "TODO_0294/0295 (the timed twin: certifyRun / elaborate-trace, @fire trees, SLD certificates — the per-run checker this generalizes; checkGoalCert and programFromCalc are shared)"
  - "THY_0039 (the eigenvariable/mode discipline under which step re-derivation is well-defined — A3 of THY_0035)"
  - "lib/prover/kernel.js (the backward twin: verifyTree threads the same lazy-delta leftover discipline over a backward proof)"
---

# The Execution-Tree Judgment, Machine-Checked

## 1. What this adds

THY_0035 gives the judgment `Σ; Φ ⊢_fwd T : Δ ⇒ 𝔏` and its typed term
language `T` — the eight constructors `explore()` builds. This document is
the **checker** for that judgment: `lib/prover/forward-check.js`
(`checkForwardTree`), the forward twin of `lib/prover/kernel.js`. It takes a
whole execution tree and verifies it, re-deriving every firing from the
program's declarative rule data with the recorded substitution θ as the sole
witness — the untimed, whole-tree generalization of the timed face's
per-run `certifyRun` (§4).

The point is that `⊢_fwd T` becomes **checkable at the tree level**, not just
definable, and not just checkable one committed-choice trace at a time. The
tree is a game tree (∀ over rule choices, ∃ over ⊕ alternatives); the checker
treats it as one object.

## 2. The eight constructors and how each is discharged

`explore()` emits the judgment's term implicitly: every non-terminal is a
`branch` node whose child edges each carry the fired rule, an optional ⊕
`choice`, and (under `evidence:true`) a **step witness** `{θ, alt, loliHash}`.
The checker threads the linear multiset Δ (a `Map hash→count`) and the
persistent set Φ down the tree.

| Constructor | Edge/node | Checked how |
|---|---|---|
| `step(r,θ,T')` | single branch edge | consume patterns of `r` ground under θ must be present in Δ (removed); persistent goals provable (§3); produced facts = consequent ground under θ (added). Δ ⇒ Δ'. |
| `fork(T₁…Tₖ)` | edges sharing `r`, distinct `alt` | each is a `step` on the SAME Δ using the ⊕-alternative `alt` of `r`'s consequent; `alt` must index an existing alternative. |
| `branch(r₁…rₙ)` | edges with distinct rules | each is an independent `step` from the SAME parent Δ. |
| `leaf(Δ_q)` | terminal | the recorded state equals the threaded Δ/Φ (the reachable-state consistency check). |
| `cycle` / `bound` / `memo` | terminal | recorded state equals the threaded state; no leaf claim (soundness vacuous). |
| `dead` | terminal (child of a pruned edge) | skipped: contributes no leaf, hence no reachable state — vacuously sound (§5). |

Loli continuations (the D component of THY_0035 — a state-resident linear
implication fired as a rule) are re-derived from the consumed token's own
structure (`deriveLoliRecord`); the token hash is the witness (`loliHash`).

## 3. What is trusted

The trust boundary is exactly `checkForwardTree` plus the equational-theory
canon and the clause layer — mirroring the backward kernel. `explore()`,
`findAllMatches`, `tryMatch`, the strategy stack, mutation+undo, the
constraint solver: **none are trusted**. The only witness carried into the
check is θ (and the ⊕ index and the loli token). Consumed and produced
multisets are NOT read from the trace — they are re-derived from the rule's
antecedent/consequent patterns and checked against the threaded Δ. A step
that consumes an absent fact, produces a fact the rule does not license, or
guards on an unprovable persistent goal is rejected.

Persistent goals are discharged by Φ-membership or by a **clause-only SLD
certificate** (`checkGoalCert`) the checker re-derives independently: the
search for the certificate is untrusted (the engine backchainer), the check
is trusted, and the numeric FFI never touches the verification path — the
same discipline as the timed `@fire` checker (TODO_0295).

## 4. Relation to the timed face

The timed `certifyRun` (`elaborate-trace.js`) certifies ONE settle run by
elaborating its event trace into a backward `@fire` proof tree and calling
the backward kernel. This checker is the untimed, whole-tree generalization:
- **untimed** — the step re-derivation is `checkFireData` with the stamp
  algebra removed (no activation/done/before/after/join); it shares
  `programFromCalc`, `deriveLoliRecord`, `checkGoalCert`.
- **whole-tree** — it verifies the ∀/∃ branching structure (`fork`,
  `branch`, `dead`) as one object, not a single committed trace.

## 5. Soundness is certificate-checkable; completeness is not

The tree's **soundness** claim is: *every `leaf` is reachable from Δ₀ by a
sequence of valid forward steps.* The verified per-edge re-derivation plus
the threaded Δ establishes exactly this — each root→leaf path is a valid
derivation, and the terminal state-consistency check binds each recorded
reachable state to the derivation that reaches it. Adding a `dead`, `cycle`,
`bound`, or `memo` node introduces no leaf, so it cannot introduce an unsound
reachable state; those are terminal.

The tree's **completeness** claims are the three negative/universal
assertions a certificate cannot witness (TODO_0045 §5.4):
- a `leaf` asserts *no rule fires* — trusts `findAllMatches`;
- a `dead` asserts *the pruned alternative was genuinely infeasible* —
  trusts the constraint solver (a wrong prune loses a live branch:
  completeness, never soundness);
- a `branch` asserts *every applicable rule is present* — trusts
  `findAllMatches`.

These are the irreducible oracle residue. The checker names them rather than
verifying them; establishing them is TODO_0042 (explore() adequacy via the
QCHR ω^{∃∀} game-tree correspondence). This is the honest position of §5 of
TODO_0045, now realized in code: **the forward engine is a proof system whose
soundness is machine-checked and whose completeness is a stated, bounded
trust in the matcher.**
