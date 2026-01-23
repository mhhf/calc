# TODO

Outstanding tasks for the CALC project.

---

## Active Tasks

### Revive the UI
**Priority:** HIGH

- [ ] Investigate current frontend code (Cycle.js)
- [ ] Get basic rendering working (display sequents, proof trees)
- [ ] Add interactive rule application (click to apply inference rules)
- [ ] Display proofs as PDF/HTML

### Study Proof Nets
**Priority:** HIGH

- [ ] Understand proof nets vs proof trees
- [ ] Study the "bureaucracy" problem they solve
- [ ] Understand correctness criteria
- [ ] Research HCP connection (relevant to blockchain goals)
- [ ] Evaluate: can proof nets work for multimodal quantitative linear types?

---

## Backlog

### Interactive Proof UI Enhancements
- [ ] Show rule premises when hovering/selecting a rule
- [ ] Display abstract rule pattern (not just name)
- [ ] Show sigma (substitution) applied by rule

### Context Split Dialog
- [ ] For rules like `Tensor_R` that split context (?X, ?Y)
- [ ] Let user choose how to distribute resources
- [ ] Alternative: enumerate all valid splits

### Architecture (Core/Calculus Separation)
- [ ] Identify code that is "Gentzen machinery" vs "Linear Logic specific"
- [ ] Design clean interface between core engine and calculus plugins
- [ ] Extract core into `lib/core/` directory
- [ ] Support compile-time and runtime calculus loading

### Code Quality
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
- [ ] Research FFI for logics (fixed point arithmetic, etc.)

### Extensions
- [ ] Design semiring-parameterized quantities
- [ ] Design ownership modalities
- [ ] Prototype real-number arithmetic

### Documentation
- [ ] Write significance hypothesis document (dev/HYPOTHESIS.md)
- [ ] Design minimal litmus test example (token transfer encoding)
- [ ] Understand why display calculus handles modalities well
