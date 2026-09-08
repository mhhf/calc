---
title: "The Adjoint Bridge: Re-evaluating the Mode-Preorder Surgery"
created: 2026-09-08
modified: 2026-09-08
summary: "TODO_0309 P5: the decision document that re-evaluates THY_0032's 'negative expected ROI' verdict on generalizing CALC's zone machinery to a full mode preorder (big_next branch 2), in light of everything that landed since it was written. The seven-site atomic-change set is ALREADY PAID (TODO_0285 P4 installed pool routing at every site); the 1-mode (sax, copySource null) and n-zone (sill, linear-policy aux) instances exist; the family interface is axiomatized code-side (RES_0143 F1 cc port) and theory-side (THY_0035 𝔉-axioms). The remaining frontier is exactly three gaps — G1 per-zone structural policies beyond linear (an affine aux zone is refused loudly today), G2 multiple contraction zones, G3 succedent modes + the independence principle — pinned executable in tests/engine/adjoint-frontier.test.js. The five modal mechanisms map onto adjoint ingredients, and one payoff is concrete: will's drawn_l2 ghost is a hand-rolled affine mode: a G1 zone policy deletes the rule and its token-class keying, absorbing the discharge machinery as the policy's general implementation. Verdict: upgrade from 'negative ROI' to STAGED-POSITIVE — Stage A (G1 affine zone policy + the adjoint-sax instance exercising it) is now cheap enough to be worth it when will's token machinery next grows; Stage B (G3 succedent modes, the true adjoint core) remains gated on a driving calculus; G2 stays refused until one exists. The adjoint-sax bridge instance is SPECIFIED here (modes, shifts, what it exercises) so branch-2 Stage A starts from a design, not a blank page."
tags: [adjoint-logic, linear-logic, proof-theory, architecture, structural-rule, lnl, sax, engine-metatheory]
category: "Proof Theory"
unique_contribution: "The staged re-evaluation itself: (1) the accounting that THY_0032's cost side collapsed — its seven-site atomic-change set was retired by TODO_0285 P4's routing, leaving exactly three named gaps (G1-G3) whose refusal boundaries are now EXECUTABLE pins rather than prose; (2) the mechanism-to-ingredient map — CALC's five modal mechanisms (graded !, graded lax monad, haul comonad, located zone wrapper, drawn tokens) each identified with the adjoint ingredient it hand-rolls, including the observation that will's drawn_l2 '@affine ghost' IS an affine mode implemented for one token class, so G1's payoff is consolidation (the rule and its token-class keying delete; the discharge machinery generalizes), not new capability; (3) the specified-but-not-built adjoint-sax bridge instance (U ≥ L with explicit ↓ from the SNAX pointer type — tying P4's factorization theorem into the bridge: the ↓A cells of MFPS 2022 are the shift the instance would make first-class) — converting branch 2's opening move from surgery into an instance-as-probe of the SAME kind that P1 used to force the family interface honest."
references:
  - "THY_0032 (the disposition this supersedes: two-zone site map + 'negative ROI'; its §3 table is now the inventory of installed routing, not live assumptions)"
  - "THY_0033 (routed zones — why the pool threading is zone-count-agnostic), THY_0035 (the 𝔉-axioms: which axiom each mode-structure component discharges), THY_0037 (SNAX ↓A — the shift the bridge instance makes first-class)"
  - "tests/engine/adjoint-frontier.test.js (the executable frontier: LNL/sax/sill shapes derive; affine aux + second copy source refuse loudly)"
  - "Pruiksma, Chargin, Pfenning & Reed (2018), Adjoint Logic (CMU TR); Pfenning 15-836 adjoint lecture notes — shift modalities generalizing Benton's LNL and subexponentials"
  - "Licata, Shulman & Riley (FSCD 2017) — the mode-theory framing THY_0032 adopted"
  - "Benton (CSL 1994) — LNL, the two-mode instance lnl.family implements (! = G∘F, declared in its header)"
  - "DeYoung–Pfenning (MFPS 2022) — ↓A 'from the downshift of adjoint logic' as SNAX's pointer type"
  - "TODO_0012 (multi-type display calculus: cut elimination per instance via Belnap — the metatheory companion if Stage B proceeds), TODO_0064 Axis 2, big_next branch 2"
---

# The Adjoint Bridge: Re-evaluating the Mode-Preorder Surgery

## 1. What THY_0032 decided, and what has changed

THY_0032 (2026-09-02) reframed the derived `contextStructure` as a
two-mode preorder instance and concluded: generalizing to arbitrary
mode preorders has **negative expected ROI** — the cost was the
seven-site atomic-change set, and no calculus needed it.

Every input to that verdict has since moved:

- **The seven sites are paid.** TODO_0285 P4 installed pool routing at
  all of them (THY_0033); THY_0032's own disposition note records the
  table as "the inventory of where routing was installed, not of live
  assumptions."
- **Two non-LNL instances exist.** sax is the 1-mode instance
  (copySource null — A2 of THY_0035 vacuous by instance); sill is the
  n-zone instance (linear-policy aux zones, wrapper-routed).
- **The interface is axiomatized twice.** Code-side: the cc port
  (RES_0143 F1) declares the family record; theory-side: THY_0035's
  𝔉 = (CS, P, D, X) with per-instance axiom status. A mode-preorder
  generalization now has a DECLARED seam to land in, on both sides.

## 2. The remaining frontier: three gaps, pinned

What `deriveContextStructure` refuses today — loudly, by design — is
the exact boundary the bridge would move
(tests/engine/adjoint-frontier.test.js):

- **G1 — per-zone structural policies beyond linear.** An affine aux
  zone (weakening without contraction — the middle mode of U ≥ A ≥ L)
  is refused: "aux consumable zones must be linear-policy." Lifting G1
  means per-zone weakening admissibility in the prover (root-leftover
  discharge, with_r balancing) and kernel accounting.
- **G2 — multiple contraction zones.** A second cartesian-like mode is
  refused: "at most one copy source." Lifting G2 means plural
  promotion targets and per-mode copy discipline.
- **G3 — succedent modes + the independence principle.** The succedent
  carries no mode; nothing enforces Γ ≥ m for ⊢ A@m, and promotion
  (bang_r) hardcodes the one copySource restriction. G3 is the true
  adjoint core: shifts ↑ᵐₖ/↓ᵐₖ with context restriction at ↑R.

Not gaps: n-ary zones (exist), zone routing (zone-count-agnostic),
structural-rule declaration (the .family syntax already carries
per-position properties — adjoint presentations GENERATE rules from
the preorder, but declaring them is equivalent and suckless).

## 3. The mechanism-to-ingredient map

CALC currently implements five modal mechanisms piecewise. Each names
the adjoint ingredient it hand-rolls:

| mechanism | adjoint reading | gap it touches |
|---|---|---|
| `!` (graded bang) | ↓↑ comonad over C > L (declared in lnl.family: ! = G∘F) | none — the shipped instance |
| graded `{A}` (lax monad) | graded ↑↓ monad at L | G3 for the general form; shipped as the bridge special case |
| `!!_d` haul (gill) | graded comonad along a dist mode — "the monad's spatial dual" | G3 (mode-indexed, not zone-indexed today) |
| `loc A @@ L` (sill) | ↓ into the located mode; wrapper-routing IS the shift's zone membership | none for membership; G1/G3 for its structural policy |
| `drawn` tokens + `drawn_l2` ghost (will) | an AFFINE mode for one token class — "@affine … weakening restricted to the token class" | **G1 exactly** |

The last row is the concrete payoff: will's ghost rule, its
last-resort focus ordering, and its boundary discharge are a
hand-rolled affine zone policy. A G1 affine aux zone would let the
token class live in a declared mode: the drawn_l2 RULE is deleted
outright, while the ~50 lines of discharge machinery in focused.js
(last-resort ordering, dischargeAffine, root-leftover, additive
balancing) become the zone policy's GENERAL implementation — replaced
by declared structure, not removed (the same trade the audit made
everywhere else: declared structure over ad-hoc mechanism, with the
token-class-specific keying as the part that actually disappears).

## 4. The bridge instance, specified

The adjoint-sax instance (branch 2's opening probe, the P1 pattern:
an instance forces the interface honest):

- **Modes:** U ≥ L (cartesian over linear) — sax's single zone plus a
  cartesian mode, i.e. the SMALLEST preorder where sax gains anything.
- **Shifts:** ↓A made first-class as SNAX's pointer type (MFPS 2022
  introduces ↓A "from the downshift of adjoint logic"; THY_0037 showed
  calc's destination terms are the legal SNAX address algebra — the
  instance would give the `!cell` indirection a TYPE).
- **Exercises:** wrapper-routed shift membership (exists), promotion
  at ↑R with context restriction (G3's minimal appearance),
  write-once cells as the U-mode storables (the P2/P4 machinery
  unchanged).
- **Deliberately excluded:** G2 (no second cartesian mode), grading on
  shifts (defer to the graded-adjoint literature line, per THY_0032's
  orthogonality note, which stands).

## 5. Verdict

**Upgrade: negative → staged-positive.**

- **Stage A (G1 + the affine token mode):** cheap now — the prover
  already performs affine discharge for drawn tokens; generalizing it
  to a declared zone policy is consolidation with a deletion payoff.
  Trigger: the next time will's token machinery grows, do Stage A
  instead.
- **Stage B (G3 + the adjoint-sax instance of §4):** the real surgery
  rump — succedent modes and shift promotion. Positive ROI CONDITIONAL
  on a driving calculus (the instance itself, or the message-passing
  line); with TODO_0012's display-calculus metatheory as companion,
  Stage B is what turns per-calculus cut-elimination hand-proofs into
  Belnap instances. Not now; specified so it starts from a design.
- **G2:** stays refused until a calculus needs two cartesian modes;
  no candidate exists.

THY_0032's orthogonality claims survive intact: stamps/grades annotate
content, not zones, and would not be absorbed. What changed is only
the cost column — and it changed because the sax program spent a year
of its budget making the interface honest first.
