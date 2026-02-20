---
title: "Proper Multi-Type Display Calculus for ILL"
created: 2026-02-18
modified: 2026-02-18
summary: "Implement Greco & Palmigiano's proper MTDC with type-uniform sequents and generic cut-elim"
tags: [MTDC, display-calculus, ILL, cut-elimination]
type: research
cluster: MTDC
status: planning
priority: 8
depends_on: []
required_by: [TODO_0013]
---

# Proper Multi-Type Display Calculus for ILL

Current `lnl.family` implements Benton's LNL — valid for ILL but NOT a proper MTDC (Greco & Palmigiano). Key issues: sequents not type-uniform, no residuation, cut-elim not via Belnap metatheorem.

- [ ] Study Greco & Palmigiano "Linear Logic Properly Displayed"
- [ ] Design type-uniform sequent structure
- [ ] Verify generic cut-elim applies
- [ ] Implement as `lnl-proper.family` (new file, not rewrite)

See: `doc/research/multi-type-display-calculus.md`
