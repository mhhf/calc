---
title: "Proper Multi-Type Display Calculus for ILL"
created: 2026-02-18
modified: 2026-03-04
summary: "Implement Greco & Palmigiano's proper MTDC with type-uniform sequents and generic cut-elim"
tags: [MTDC, display-calculus, ILL, cut-elimination]
type: research
cluster: MTDC
status: planning
priority: 8
depends_on: []
required_by: [TODO_0013]
starred: false
---

# Proper Multi-Type Display Calculus for ILL

Current `lnl.family` implements Benton's LNL — valid for ILL but NOT a proper MTDC (Greco & Palmigiano). Key issues: sequents not type-uniform, no residuation, cut-elim not via Belnap metatheorem.

- [ ] Study Greco & Palmigiano "Linear Logic Properly Displayed"
- [ ] Design type-uniform sequent structure
- [ ] Verify generic cut-elim applies
- [ ] Implement as `lnl-proper.family` (new file, not rewrite)

## Multi-Calculus Engineering Notes (from TODO_0066 §4.16)

When a second calculus is added, these ILL-hardcoded paths need parameterization:

- `lib/engine/show.js` — 5 hardcoded ILL connective names in debug formatting (use calculus renderer)
- `lib/engine/convert.js` — `extractAntecedent`/`extractConsequent` hardcode loli/tensor/bang (each logic provides its own loader)
- `lib/engine/convert.js` — hardcodes `ILL_ENGINE_TABLES` parser tables (per-logic loader)
- `out/ill.json` — ILL-specific precomputation (each calculus gets its own bundle)
- Cross-logic programs mixing connectives from two logics — research question, adjoint logic territory

See: `doc/research/multi-type-display-calculus.md`
