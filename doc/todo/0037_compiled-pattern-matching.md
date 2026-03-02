---
title: "Compiled Pattern Matching"
created: 2026-02-18
modified: 2026-03-02
summary: "Per-rule compiled matchers attempted in TODO_0058 Opt_G — hit V8 megamorphic IC limit (>4 closures at one call site → ~25% regression). Persistent step fast path shipped instead (≤4 FFI closure types). WAM/Maranget-style multi-rule dispatch remains viable for future 1000+ rule scenarios."
tags: [performance, research, compilation, WAM, Maranget]
type: research
cluster: Performance
status: backlogged
priority: 3
depends_on: []
required_by: []
---

# Compiled Pattern Matching

Extracted from TODO_0022.Topic_3. Compile patterns into executable code for 1000+ rules.

## Partial Results from TODO_0058 Opt_G (2026-03-02)

Per-rule compiled matchers were implemented and tested. **59/73 EVM rules** got specialized closure matchers. Result: **~25% regression** due to V8 megamorphic dispatch — V8's IC degrades after 4+ distinct closures at a single call site (`--max-polymorphic-map-count=4`). See [RES_0069](../research/0069_v8-megamorphic-dispatch.md) for analysis.

**What shipped instead**: `persistentSteps` — pre-compiled FFI closures (≤4 types: inc, plus, neq, mul) that bypass `subApplyIdx + tryFFIDirect` for ground FFI goals. Stays within V8's polymorphic IC threshold. Result: -32% matchIdx calls, -61% substitute calls, ~6-12% wall-clock.

**Key constraint**: any optimization creating >4 distinct closure types at a single call site will regress in V8. This blocks the naive "compile each rule to a closure" approach. Viable paths must either stay monomorphic (defunctionalized) or use switch dispatch.

## Remaining (future, for 1000+ rules)

- [ ] First-occurrence vs subsequent-occurrence distinction (WAM get_variable/get_value)
- [ ] Maranget-style decision trees for multi-rule dispatch (avoids megamorphic — single switch)
- [ ] Interaction between deferral order and first/subsequent classification

See: `doc/research/compiled-pattern-matching.md`, `doc/research/de-bruijn-indexed-matching.md`
