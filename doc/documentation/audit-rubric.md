# Audit rubric: a reusable pattern for refactor verification

A *rubric* is a flat, mechanical, idempotent checklist that grades a
refactor against its stated invariants. Unlike a TODO's prose, the
rubric is a matrix: each cell is a single assertion with a binary
pass/fail answer. When all cells pass, the refactor is done.

This file documents the pattern so future audits can reuse it rather
than reinventing grading from scratch every time.

## Why a rubric

A typical refactor-TODO succeeds at the *stated* work (rename, extract,
freeze), but drifts on adjacent invariants: dead code accumulates, one
test file escapes the migration, a performance contract isn't
re-checked, documentation falls out of date. The rubric forces each
adjacent invariant to be named and pinned before the refactor closes.

Three properties make a rubric useful:

1. **Mechanical.** Every cell must be decidable without judgment —
   ideally by a test or a grep. No "looks good to me" cells.
2. **Idempotent.** Running the rubric twice yields the same answer.
   Cells reference code properties, not events.
3. **Binary.** Each cell passes or fails. A partial pass is a fail.
   This is the opposite of a status update; it's a contract.

## Canonical cell categories

The categories below were extracted from TODO_0209 (matchOpts typed
layer interfaces) and generalize to most engine refactors. Not every
category applies to every refactor — drop the ones that don't fit and
add domain-specific cells.

### S — Shape (structural invariants)

Each S-cell asserts a property of the code's *shape* independent of
behavior. Shape violations cause V8 deopts, API drift, or hidden-class
churn even when tests pass.

| Cell | Example |
|---|---|
| S1 | Factory returns same key set regardless of input |
| S2 | Factory output has documented defaults (null, false, baseline) |
| S3 | Assembled record is frozen |
| S4 | Empty record has same shape as populated record |
| S5 | No ad-hoc construction outside the composition root (production) |
| S6 | No ad-hoc construction outside the helper (tests) |
| S7 | Canonical iteration order (V8 hidden-class stability) |
| S8 | FIELD constants are disjoint (no field owned by two factories) |

S5 and S6 are typically static code-scan tests that walk the filesystem
and assert a pattern is absent outside an allowlist. See
`tests/engine/no-ad-hoc-matchopts.test.js` for a reference scanner with
balanced-paren handling.

### C — Contract (interface invariants across implementations)

Each C-cell asserts that two or more implementations of the same
interface agree on the interface *as written*, not just the happy path.

| Cell | Example |
|---|---|
| C1 | All implementations have the same signature (arity + parameter order) |
| C2 | All implementations report post-unification (not pre-unification) data |
| C3 | All implementations emit the documented hook payload shape |
| C4 | All implementations use the canonical enum for method strings |
| C5 | All implementations return the documented type (number, boolean) |

C-cells are the highest-ROI category. They catch drift between sibling
implementations that diverge over years of local edits. See
`tests/engine/prover-contract.test.js` for the pattern: one scenario
function + one loop over implementations + one assertion per cell.

### Sem — Semantic (behavior invariants)

Each Sem-cell asserts a semantic property the refactor must preserve.
Unlike shape/contract, these often require full integration tests
because the assertion spans multiple modules.

| Cell | Example |
|---|---|
| Sem1 | End-to-end behavior unchanged (full test suite passes) |
| Sem2 | Adversarial invariants still hold (e.g., FFI-off soundness) |

### P — Performance (contract-grade invariants)

Each P-cell asserts a performance budget. A regression beyond the
stated threshold is a fail. Cells reference specific benchmarks, not
vague "feels fast" judgments.

| Cell | Example |
|---|---|
| P1 | No regression > N% on bench:diff explore suite |
| P2 | No regression > N% on bench:diff engine suite |

Threshold N should be the benchmark's observed stddev (12% is typical
for the explore suite). Smaller thresholds demand more runs.

### D — Documentation (reference invariants)

Each D-cell asserts a documentation alignment.

| Cell | Example |
|---|---|
| D1 | Reference doc reflects the final layer names |
| D2 | CLAUDE.md directory structure section reflects moves/renames |
| D3 | Rubric itself is externalized into the TODO body |

## Structure

Write the rubric as a markdown table with three columns:

```markdown
| Cell | Invariant | Status |
|---|---|---|
| S1 | factory shape stable | ✓ tests/engine/match-factories.test.js |
| S5 | no ad-hoc matchOpts in lib/engine/ | ✓ tests/engine/no-ad-hoc-matchopts.test.js |
| C1 | prover signature consistency | ✓ tests/engine/prover-contract.test.js |
| P1 | bench:explore regression < 12% | ✓ +0.85% observed |
```

Status is either ✓ (pass, with pointer to the proof) or ✗ (fail, with
specific remediation required). There is no ⚠ — if you're unsure, the
cell fails.

## Workflow

1. **Draft.** Before starting the refactor, write the rubric as a set
   of uncommitted cells. This is the contract the refactor must meet.
2. **Walk.** After implementation, walk each cell. Either a test
   exists that asserts it, or you write one. Don't mark a cell ✓
   without a mechanical proof.
3. **Externalize.** Paste the final rubric into the TODO body. Future
   readers reviewing the commit history can see what was guaranteed.
4. **Close.** Only close the TODO when every cell is ✓ with a specific
   proof pointer. Cells without pointers mean the TODO isn't done.

## Anti-patterns

- **Narrative cells.** "Makes the code cleaner" is not a cell. Rephrase
  as a mechanical assertion or drop it.
- **Prose instead of matrix.** A paragraph hiding five invariants is
  harder to walk than five one-line cells. Split.
- **Skipped categories.** If a refactor has no P-cells, the reviewer
  can't tell if performance was forgotten or genuinely irrelevant.
  State "P — N/A (no hot path touched)" explicitly.
- **"Will add tests later".** Dead cell. Either the test exists now or
  the cell fails now.

## Reference implementations

| Refactor | Rubric | Test files |
|---|---|---|
| TODO_0209 matchOpts | S1-S8, C1-C5, Sem1-2, P1, D1-3 | `match-factories`, `prover-contract`, `no-ad-hoc-matchopts` |
