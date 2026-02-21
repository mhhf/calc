---
paths:
  - "doc/theory/**"
---

# Theory File Management

## Purpose

`doc/theory/` holds CALC's **original theoretical contributions** -- novel results, proof sketches, formal judgments, design frameworks, and analyses that don't exist in the literature. "Did we invent it?" → theory/.

Distinguished from `doc/research/` (surveys of others' work), `doc/def/` (concept definitions), and `doc/documentation/` (implementation details).

## Format

Each theory document is a file `doc/theory/NNNN_kebab-title.md` where `NNNN` is a zero-padded 4-digit ID.

### Creating a Theory Document

1. Read `doc/theory/meta.yaml` → `current_number`
2. Create file `doc/theory/<padded_number>_<kebab-title>.md`
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
unique_contribution: "What this document adds that is NOT in any paper, textbook, or prior system."
references: []
---
```

## Rules

- **`unique_contribution` is required.** Every theory document must articulate what is novel. If the contribution can't be stated clearly, the content likely belongs in `doc/research/` instead.
- The contribution should answer: "If this were a paper, what would the abstract's main claim be?"
- **Numbered filenames.** All files must follow the `NNNN_kebab-title.md` convention.
- **`category` is required.** Assign a category for grouping in the UI.
- Keep documents focused on the theoretical result. Implementation details belong in `doc/documentation/`.
- External research surveys belong in `doc/research/`.
