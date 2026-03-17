---
title: "Modality Parser Extensions"
created: 2026-02-18
modified: 2026-02-18
summary: "Extend tree-sitter grammar and parser for ownership/authorization/graded modalities"
tags: [parser, modalities, tree-sitter, implementation]
type: implementation
cluster: Multimodal
status: planning
priority: 7
depends_on: []
required_by: [TODO_0014]
---

# Modality Parser Extensions

Extracted from TODO_0014. Extend the parser to support modality syntax.

- [ ] Tree-sitter grammar rules for `[P] A` (ownership), `<P> A` (authorization), `[]_r A` (graded)
- [ ] `cst-to-ast.js` — modality AST nodes
- [ ] `convert.js` — content-addressed hashes for modality terms
- [ ] Constructor annotations in `ill.calc` for pretty-printing

See: `doc/research/multimodal-linear-logic.md`
