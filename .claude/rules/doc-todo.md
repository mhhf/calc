# TODO File Management

TODOs are managed in `~/src/os_data/todo/`, NOT in this repo.

When referencing TODOs from calc docs (research, theory, documentation), use the identifier only: `TODO_0068`. Do not create links to local files.

## Creating a TODO

1. Read `~/src/os_data/todo/meta.yaml` → `current_number`
2. Create file `~/src/os_data/todo/<padded_number>_<kebab-title>.md`
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

## Closing / Subsuming

When marking a TODO as `done` or `subsumed`:

1. Set `status: done` (or `status: subsumed`) and update `modified`. Do not delete the file.
2. **Update all dependents:** Search all TODOs for references to the closed item in `depends_on`, `required_by`, or `subsumed_by` fields.
