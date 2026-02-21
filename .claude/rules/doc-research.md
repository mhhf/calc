---
paths:
  - "doc/research/**"
---

# Research File Management

## Purpose

`doc/research/` holds **external knowledge** -- literature surveys, paper summaries, technique catalogs, design-space explorations sourced from existing work. "Did someone else write about it?" → research/.

## Format

Each research document is a file `doc/research/NNNN_kebab-title.md` where `NNNN` is a zero-padded 4-digit ID.

### Creating a Research Document

1. Read `doc/research/meta.yaml` → `current_number`
2. Create file `doc/research/<padded_number>_<kebab-title>.md`
3. Increment `current_number` in `meta.yaml`
4. Fill required frontmatter:

```yaml
---
title: "Document title"
created: YYYY-MM-DD
modified: YYYY-MM-DD
summary: "One-sentence summary"
tags: []
category: "Category name"
---
```

## Categories

Assign one of these categories (or create a new one if none fits):

- **Motivation** -- vision, accounting, financial primitives
- **Ownership** -- authorization, consensus, session types
- **Proof Theory** -- sequent calculi, display, residuation
- **Multi-Type Framework** -- adjunctions, multimodal, graded
- **Related Paradigms** -- session types, ludics, CLF/Ceptre, BDI
- **Implementation** -- DSL, FFI, prover architecture
- **Performance** -- optimization, indexing, benchmarking, data structures
- **Semantic Foundations** -- fibrations, proof terms
- **Reference** -- Q&A, bibliography, logic engineering
- **Symbolic Execution** -- equational completion, simplification
- **Forward Chaining** -- forward chaining theory

## Rules

- **`category` is required.** Every research document must have a category for UI grouping.
- **Numbered filenames.** All files must follow the `NNNN_kebab-title.md` convention.
- Keep documents focused on surveying external work. Novel contributions belong in `doc/theory/`.
- CALC-specific implementation documentation belongs in `doc/documentation/`.
- Design deliberations, open questions, and planned work belong in `doc/todo/`.
- If a file contains both external research and CALC-specific content, split it: external parts stay in research/, CALC parts go to theory/documentation/todo/ as appropriate.
- When referencing other documents, use the numbered prefix (e.g., RES_0001, THY_0001, TODO_0001, DEF_0001).
