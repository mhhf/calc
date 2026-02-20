---
paths:
  - "doc/todo/**"
---

# TODO File Management

## Format

Each TODO is a file `doc/todo/<number>_<title>.md` where `<number>` is a zero-padded 4-digit ID (e.g. `0001`).

## Creating a TODO

1. Read `doc/todo/meta.yaml` → `current_number`
2. Create file `doc/todo/<padded_number>_<kebab-title>.md`
3. Increment `current_number` in `meta.yaml`
4. Fill required frontmatter:

```yaml
---
title:
created: YYYY-MM-DD
modified: YYYY-MM-DD
summary:
tags: []
type: research | design | implementation | bug | tooling
status: planning | researching | ready for implementation | in progress | done
priority: 1-10
cluster: Theory | Symexec | CLF | MTDC | Verification | Multimodal | Financial | Performance | Tooling
depends_on: []
required_by: []
---
```

## Labeling subtasks

All subtasks, stages, options use full enumeration prefix:

- `TODO_0001.Stage_1 — Title`
- `TODO_0001.Option_2.Stage_3 — Title`

## Exporting subtasks

When a subtask grows large enough to stand alone:
1. Create a new TODO file (take next number from meta.yaml)
2. In the parent, replace the subtask body with a link: `TODO_0001.Stage_2 — see [TODO_0005](0005_title.md)`
3. Set `depends_on` / `required_by` in both files

## Closing / Subsuming

When marking a TODO as `done` or `subsumed`:

1. Set `status: done` (or `status: subsumed`) and update `modified`. Do not delete the file.
2. **Update all dependents:** Search all TODOs for references to the closed item in `depends_on`, `required_by`, or `subsumed_by` fields.
   - `depends_on: [TODO_XXXX]` → replace with the subsuming TODO (if subsumed) or remove (if done with no successor)
   - `required_by: [TODO_XXXX]` → remove the closed item (the dependency is satisfied)
   - If a subsuming TODO exists, ensure the subsuming TODO inherits the closed item's `required_by` entries (i.e. things that were blocked by the closed item should now depend on the subsuming item instead)
