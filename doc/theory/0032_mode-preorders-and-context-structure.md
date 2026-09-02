---
title: "Mode Preorders and Context Structure: Two-Zone Site Map for TODO_0285 Phase 4"
created: 2026-09-02
modified: 2026-09-02
summary: "The contextStructure record (consumableZone / copySource / zone properties) derived at load from the family's @position_modes + @structural declarations is exactly a two-mode preorder instance — cartesian > linear, with contraction+weakening at C and neither at L, reproducing Benton's LNL — and the backward prover has seven independent sites that hardcode the two-zone assumption. Grades annotate formula content within the linear zone and are orthogonal to zone structure. For the current four two-zone calculi the load-time fence plus this site map is the chosen discipline; generalization to a mode preorder has negative expected ROI."
tags: [linear-logic, proof-theory, architecture, adjoint-logic, structural-rule, lnl, graded-types]
category: "Proof Theory"
unique_contribution: "Precise identification of the seven independent two-zone hardcoding sites in the backward prover (rule-interpreter.js ×3, generic.js, focused.js, bridge.js, fact-set.js engine constants) that must change atomically if the load-time fence is ever relaxed; the reframing of the derived contextStructure as a two-mode preorder instance in the Licata–Shulman–Riley sense; and the argument that timed content annotation (labels.js stamps) is orthogonal to zone structure and would not be absorbed by a mode-preorder generalization. Together these constitute the design-disposition record for TODO_0285 Phase 4."
references:
  - "Licata, Shulman & Riley (2017). A Fibrational Framework for Substructural and Modal Logics. FSCD 2017, LIPIcs vol. 84, art. 25."
  - "Pruiksma, Chargin, Pfenning & Reed (2018). Adjoint Logic. CMU technical report."
  - "Benton (1994). A Mixed Linear and Non-Linear Logic. CSL 1994."
  - "Orchard, Rice & Eisenberg (2019); Moon, Eades III & Orchard (2021). Graded-adjoint lines of work — decomposing graded modalities via adjunctions. Not CALC's shipped design; the unification with substructural logics is deferred literature."
  - "TODO_0285 Phase 4 (zones-as-modes). TODO_0086 (deriveContextStructure, shipped)."
---

# Mode Preorders and Context Structure

**Scope.** Design-disposition record for TODO_0285 Phase 4. Decision:
do not implement mode preorders now; maintain the load-time fence and
this site map as the enforced discipline.

## 1. The derived mechanism

`deriveContextStructure` (lib/calculus/index.js:125–169) reads the family's
`@role sequent` constructor for `@position_modes` and the `@structural`
declarations (contraction / weakening / exchange with `@position`) to produce:

```
{ zones, properties, consumableZone, copySource, copyTarget }
```

For `lnl.family`: `@position_modes "cartesian linear linear"` gives context
zones `["cartesian", "linear"]` (the last position is the succedent, dropped).
`cart_contraction @position 1` marks "cartesian" as copy source; no contraction
at position 2 makes "linear" the unique consumable zone.

**Load-time fence** (lib/calculus/index.js:152–158): `consumable.length !== 1`
or `copySources.length > 1` throws — silently proving under the wrong
discipline is not an option. Bare `.calc` files fall back to
`DEFAULT_CONTEXT_STRUCTURE` (lib/kernel/sequent.js) with the same two-zone
layout.

## 2. The mode-preorder reframing

Licata–Shulman–Riley (2017) parametrize sequent calculi by a **mode theory** —
a preorder of modes with structural rules holding at each mode. A two-mode
preorder L < C, contraction+weakening at C and neither at L, recovers Benton's
LNL exactly. The derived `contextStructure` is this instance:

| zone | mode | contraction | weakening |
|------|------|-------------|-----------|
| cartesian | C (copy source) | yes | yes |
| linear | L (consumable) | no | no |

The `lnl.family` header states: "The F ⊣ G adjunction connects the modes. For
ILL, this gives ! = G ∘ F." In adjoint-logic presentations (Pruiksma–Pfenning)
structural rules are generated from the preorder; here they are declared in the
`.family` file and derived into the same record.

**Grades and timestamps are orthogonal to zone structure.** `at(A, t)` labels
and stamp rows in labels.js annotate formula *content* within the linear zone;
a mode-preorder generalization would not absorb them. Similarly, graded
modalities decompose into adjunctions (Orchard / Eades III line of work), but
bang-grading and zone structure are currently independent — that independence is
load-bearing for simplicity.

## 3. Two-zone site map (atomic-change set for TODO_0285 Phase 4)

| Site | Lines | Hardcoded two-zone assumption |
|------|-------|-------------------------------|
| lib/calculus/index.js fence | 152–158 | throws if consumable zone not unique or >1 copy source |
| lib/prover/rule-interpreter.js | 144–148 | loli/monad premises: `{consumableZone: lin, copySource: cart}` |
| lib/prover/rule-interpreter.js | 159–162 | structural premise: same two-key `Seq.seq` |
| lib/prover/rule-interpreter.js | 187–190 | connective premises: same |
| lib/prover/generic.js | 26 | extracts only `CZ`; further zones invisible |
| lib/prover/focused.js | 29–30 | destructures only `CZ` + `SZ` |
| lib/prover/bridge.js | 49–57 | `sequentToState`: consumableZone → `linear`, copySource → `persistent` (engine-constant keys in fact-set.js `State`) |

The `Seq.seq({[cs.consumableZone]: …, [cs.copySource]: …})` pattern at the
three rule-interpreter sites silently drops any third zone — wrong sequent,
no error. The fence prevents this from being reachable.

## 4. Disposition

All four current calculi (ill / till / gill / will) are two-zone. Expected ROI
of a general mode preorder is negative: the implementation cost is not offset by
any current need. The fence + site map is the enforced discipline. TODO_0285
Phase 4 owns the decision of extending vs. a minimal zone-generic State when a
third zone is first needed.
