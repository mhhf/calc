---
paths:
  - "doc/def/**"
---

# Definition File Management

## Purpose

`doc/def/` is an encyclopedia of atomic concepts — each file captures exactly one term, idea, or "meme". Files are self-contained: a reader should understand the concept from the file alone.

## Format

Each definition is a file `doc/def/<number>_<title>.md` where `<number>` is a zero-padded 4-digit ID (e.g. `0001`).

## Creating a Definition

1. Read `doc/def/meta.yaml` → `current_number`
2. Create file `doc/def/<padded_number>_<kebab-title>.md`
3. Increment `current_number` in `meta.yaml`
4. Fill required frontmatter and body (see below)

## Frontmatter

```yaml
---
term: "Exact term or concept name"
summary: "One-sentence definition"
tags: []
see_also: []        # links to related DEF_NNNN entries
references: []      # papers, books, URLs
---
```

- `term`: the canonical name (capitalized, no abbreviation expansion)
- `summary`: a single sentence a newcomer can read and understand
- `tags`: lowercase, hyphenated (e.g. `linear-logic`, `chr`, `proof-theory`)
- `see_also`: list of `DEF_NNNN` cross-references (optional)
- `references`: bibliography entries — author, title, year, venue (optional)

## Body Structure

```markdown
# <Term>

<1-3 paragraph explanation. Be precise and concise.>

## Example

<Concrete example demonstrating the concept. Use formulas, code, or diagrams as appropriate.>

## In CALC

<How this concept manifests in CALC specifically. Optional — omit if the concept is purely external.>
```

## Rules

- **One concept per file.** If two ideas are distinct, they get separate files.
- **Atomic.** A definition should not grow into a survey or tutorial. If it exceeds ~40 lines of body text, split it.
- **Stable.** Definitions describe what something IS, not how it changed. No status updates.
- **Cross-reference via `see_also`**, not inline prose. Keep each file self-contained.
- **No duplication with `doc/todo/`.** Definitions describe concepts; TODOs describe work to do.
