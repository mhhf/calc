# TODO.md

Current tasks and priorities for the CALC revival project.

See also: [[RESEARCH]] | [[REFACTOR]] | [[README]]

---

## Current Status (2026-01-21)

**System is fully operational!**
- ✅ `npm install` works
- ✅ `npm test` passes (7/7 tests)
- ✅ Parsing works: `./libexec/calc-parse "-- : A -o B |- -- : C"`
- ✅ Proof search works for identity, modus ponens, distribution, etc.

**Quick commands:**
```bash
npm test                                    # Run tests
./libexec/calc-parse "-- : A -o B"         # Parse a formula
./libexec/calc-proof "-- : A |- -- : A"    # Try proof search
./libexec/calc-debug-proof "..."           # Debug proof search
```

**Example proofs that work:**
```bash
./libexec/calc-proof "-- : Q |- -- : Q"                              # identity
./libexec/calc-proof "-- : P, -- : P -o Q |- -- : Q"                 # modus ponens
./libexec/calc-proof "-- : P * Q |- -- : Q * P"                      # tensor commutativity
./libexec/calc-proof "-- : A & B |- -- : A"                          # with elimination
./libexec/calc-proof "-- : P -o (R & Q) |- -- : (P -o Q) & (P -o R)" # distribution
```

---

## Active Tasks

### Task 1: Get the System Running ✓ COMPLETE
**Status:** Complete
**Goal:** Verify the codebase works, trace through a proof end-to-end

**Completed (2026-01-21):**
- [x] Run `npm install` - fixed by removing native `sha3`/`keccakjs` deps, using Node crypto
- [x] Run `make test` - all 7 tests pass (1 skipped)
- [x] Run `calc parse "-- : A -o B |- -- : C"` - parsing works!
- [x] Run `calc proof` - proof search works!
- [x] Fixed proof search focusing/polarity issues

**Changes made:**
- Replaced `keccakjs` with Node's built-in `crypto.createHash('sha3-256')`
- Added `jison` and `jison-lex` to package.json (were missing)
- Fixed `parser.js` to call `Calc.init()` before generating grammar
- Fixed test syntax (`*` → `--` for any-term, `xx` → `*` for tensor)
- Fixed various null checks in `node.js` and `sequent.js`
- Updated CLI scripts for current API
- Fixed `proofstate.js` to:
  - Enable right-focusing for positive atoms (needed for identity proofs)
  - Skip atomic formulas in `getInvertableRule` (atoms use Id rule, not inversion)
  - Added `mode: 'proof'` to CLI scripts for forward chaining

**Notes:**
- See [[REFACTOR#Current State Analysis]] for architecture overview
- Key files: `lib/proofstate.js`, `lib/sequent.js`, `lib/parser.js`

---

### Task 2: Revive the UI
**Status:** Active (HIGH PRIORITY)
**Goal:** Get the interactive UI working for rendering and manual proof construction

**Subtasks:**
- [ ] Investigate current frontend code (what framework? Cycle.js?)
- [ ] Get basic rendering working (display sequents, proof trees)
- [ ] Add interactive rule application (click to apply inference rules)
- [ ] Display proofs as PDF/HTML for completeness

**Why prioritized:**
- Visual feedback helps build intuition
- Manual proof construction before automated search
- Needed for exploring the system interactively

---

### Task 3: Study Proof Nets
**Status:** Active (HIGH PRIORITY)
**Goal:** Deep understanding of proof nets and their applicability to our goals

**Subtasks:**
- [ ] Understand what proof nets are and how they relate to proof trees
- [ ] Study the "bureaucracy" problem they solve
- [ ] Understand correctness criteria
- [ ] Research HCP connection (relevant to blockchain goals)
- [ ] Evaluate: can proof nets work for multimodal quantitative linear types?
- [ ] Write findings in `dev/research/proof-nets.md`

**Key papers:**
- Girard's original (1987)
- Laurent's introduction to proof nets
- Moot & Puite: Proof Nets for the Multimodal Lambek Calculus

---

## Backlog Tasks

### [BACKLOG] Write Significance Hypothesis Document
**Status:** Deferred - need more intuition first
**Goal:** Articulate clearly what we think is significant about LL + extensions

**Subtasks:**
- [ ] Write 1-2 page document answering:
  - What specifically does LL capture that other formalisms miss?
  - What would convince me I'm right? (concrete example)
  - What would convince me I'm wrong? (falsification criteria)
  - Why do few people see this?
- [ ] Save as `dev/HYPOTHESIS.md`
- [ ] Link to [[RESEARCH#Meta-Goal: Validating the Intuition]]

---

### [BACKLOG] Design Minimal Litmus Test Example
**Status:** Deferred - need more intuition first
**Goal:** Design (on paper first) a concrete encoding that tests the hypothesis

**The example:**
```
Initial state:
  [Alice] 100 USD
  [Bob] 50 EUR

Transaction: Alice sends 50 USD to Bob

Final state:
  [Alice] 50 USD
  [Bob] 50 EUR ⊗ 50 USD
```

---

### [BACKLOG] Understand Why Display Calculus Handles Modalities Well
**Status:** Deferred
**Goal:** Deep understanding of display calculus advantages for modal extensions

---

## Completed Tasks

*(Move tasks here when done)*

---

## Backlog

### Architecture (Core/Calculus Separation)
- [ ] Identify code that is "Gentzen machinery" vs "Linear Logic specific"
- [ ] Design clean interface between core engine and calculus plugins
- [ ] Extract core into `lib/core/` directory
- [ ] Move LL-specific code to `lib/calculi/linear-logic/`
- [ ] Support compile-time and runtime calculus loading
- [ ] See [[REFACTOR#Architectural Vision]] for details

### Code Quality
- [x] Fix `npm test` script in package.json
- [ ] Add ESLint configuration
- [ ] Add TypeScript (gradual)
- [ ] Set up CI with GitHub Actions

### Parser
- [ ] Document current Jison grammar
- [ ] Evaluate Chevrotain migration
- [ ] Benchmark parser performance

### Research
- [ ] Read Pfenning's 15-836 notes (first 50 pages)
- [ ] Study Granule ICFP 2019 paper
- [ ] Research Nomos language (blockchain + linear types)

### Extensions
- [ ] Design semiring-parameterized quantities
- [ ] Design ownership modalities
- [ ] Prototype real-number arithmetic

---

## Weekly Review

**Week of 2026-01-21:**
- Created project documentation ([[README]], [[RESEARCH]], [[REFACTOR]])
- Identified three priority tasks
- Starting on Task 1: system verification

---

## Notes

- Cross-reference format: `[[DOCUMENT]]` or `[[DOCUMENT#Section]]`
- Keep this file updated as single source of truth for "what's next"
- Move completed tasks to Completed section with date
