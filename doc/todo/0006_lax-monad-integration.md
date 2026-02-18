---
title: "Lax Monad {A} — Backward/Forward Integration"
created: 2026-02-18
modified: 2026-02-18
summary: "Integrate forward and backward chaining via CLF lax monad"
tags: [architecture, CLF, lax-monad, forward-backward]
type: research
status: planning
priority: 8
depends_on: [TODO_0041]
required_by: [TODO_0010, TODO_0011]
---

# Lax Monad {A}

CLF/Celf/LolliMon integrate forward and backward chaining via the lax monad `{A}`: entering the monad switches from backward (L2/L3) to forward (L4c), exiting at quiescence.

- [ ] Study CLF, Celf, LolliMon lax monad semantics in depth
- [ ] Design how `{A}` integrates with the prover lasagne layers
- [ ] Prototype forward<->backward mode switch
- [ ] Understand relationship to Ceptre stages

See: `doc/research/clf-celf-ceptre.md`
