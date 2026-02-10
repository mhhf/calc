# Development Overview

This document provides a concise overview of the CALC revival project - goals, research directions, code status, and next steps.

---

## Quick Links

- **[RESEARCH.md](./RESEARCH.md)** - Research goals, knowledge base, reading list, open questions
- **[REFACTOR.md](./REFACTOR.md)** - Code analysis, technical debt, modernization plan, Rust strategy

---

## Project Vision

**CALC** is a proof calculus sandbox for linear logic, originally written ~9 years ago. The revival aims to:

1. **Learn** - Deeply understand Gentzen-style calculi, cut elimination, and proof search
2. **Extend** - Add quantitative types (real-number multiplicities) and multimodalities
3. **Optimize** - Modernize JavaScript code, eventually rewrite core in Rust/Zig
4. **Apply** - Build a resource-aware accounting system for multi-currency tracking

---

## Key Insight: The Three-Level Structure

**CALC's modalities operate at THREE ORTHOGONAL LEVELS:**

1. **Structural** (adjoint modes): Linear vs Cartesian — can you copy/discard?
2. **Epistemic** (principal index): `[Alice]`, `[Bob]` — WHO controls?
3. **Quantitative** (grades): How much? T-account structure?

These COMBINE MULTIPLICATIVELY:

```
□_{[x//y]}^{L} [Alice] coin(BTC)
   │           │       └── base type
   │           └── principal index (epistemic)
   └── structural mode + grade (Pacioli T-account)
```

**This three-level structure may be CALC's distinctive contribution** — no existing system combines all three with this specific interpretation. See `research/insights.md` for details.

---

## Research Directions

### Core Topics

| Topic | Description | Priority |
|-------|-------------|----------|
| **Linear Logic** | Foundation - resources as propositions | Essential |
| **QTT** | Quantitative types with semiring multiplicities | High |
| **Graded Types** | Granule-style coeffect polymorphism | High |
| **Multimodalities** | Multiple indexed modal operators | Medium |
| **Focusing** | Andreoli's proof search discipline | Essential |
| **Cut Elimination** | Proof normalization / computation | Medium |
| **SSOS** | Substructural operational semantics | Long-term |

### Application Goals

1. **Accounting System**
   - Real-number quantities: `100.50 USD ⊗ 0.85 EUR/USD ⊢ 85.425 EUR`
   - Multi-account tracking via multimodalities

2. **Blockchain Modeling**
   - Ownership modalities: `[Alice] 0.5 BTC`
   - Atomic swaps as linear rules
   - Smart contract interactions

### Key Resources

- **Frank Pfenning's 15-836** - https://www.cs.cmu.edu/~fp/courses/15836-f23/ (combined notes, 248 pages)
- **Granule** - https://granule-project.github.io/ (quantitative types)
- **Idris 2 QTT Paper** - https://arxiv.org/abs/2104.00480 (practical QTT)
- **Celf** - https://clf.github.io/celf/ (reference linear logic implementation)

---

## Code Status

### Current State (2026-01-21)

| Aspect | Status | Notes |
|--------|--------|-------|
| **Builds** | Needs testing | Dependencies may be broken |
| **Tests** | Broken | `npm test` fails |
| **Parser** | Works | Jison-based, outdated |
| **Proof Search** | Works | Focusing-based, needs cleanup |
| **Frontend** | Cycle.js | Likely broken, needs rewrite |

### Architecture

```
ll.json (calculus spec) → Parser → AST → Sequent → ProofState → Proof Tree
```

**Core modules:** `proofstate.js`, `sequent.js`, `node.js`, `parser.js`

### Technical Debt

- No TypeScript / type annotations
- Global mutable state
- Outdated dependencies (Jison, Mocha, Cycle.js)
- Minimal tests
- No CI/CD

---

## Modernization Plan

### Phase 1: Make It Work (Weeks 1-2)
- [ ] Fix npm test
- [ ] Update critical dependencies
- [ ] Add TypeScript (gradual)
- [ ] Basic CI with GitHub Actions

### Phase 2: Improve Code Quality (Weeks 3-6)
- [ ] Migrate tests to Vitest
- [ ] Remove global state
- [ ] Add comprehensive tests
- [ ] Document ll.json schema

### Phase 3: Parser Migration (Weeks 7-8)
- [ ] Replace Jison with Chevrotain
- [ ] Benchmark and optimize

### Phase 4: Performance & Extensions (Weeks 9+)
- [ ] Prototype Rust core
- [ ] Implement quantitative extension
- [ ] Build accounting example

---

## Dependency Modernization

| Current | Replacement | Reason |
|---------|-------------|--------|
| Jison | Chevrotain | Performance, maintenance |
| Mocha/Chai | Vitest | Modern, fast, ESM |
| Cycle.js | HTMX / SolidJS | Simpler or faster |
| keccakjs | crypto built-in | Reduce deps |

---

## Research TODOs

### Immediate
- [ ] Re-read Pfenning's lecture notes (at least first 50 pages)
- [ ] Run existing codebase, trace through a simple proof
- [ ] Document what ll.json actually encodes

### Short-term
- [ ] Study Idris 2's QTT implementation
- [ ] Read Granule ICFP 2019 paper
- [ ] Design semiring extension for sequents

### Long-term
- [ ] Formalize blockchain modeling approach
- [ ] Implement real-number quantities
- [ ] Build accounting prototype

---

## Getting Started

```bash
# Install dependencies
npm install

# Run tests (currently broken)
make test

# Try parsing
calc parse "A -o B"

# Try proof search
calc proof
```

---

## File Structure

```
calc/
├── lib/                 # Core library
│   ├── proofstate.js    # Proof search engine
│   ├── sequent.js       # Sequent data structure
│   ├── node.js          # AST nodes
│   ├── parser.js        # Dynamic parser generation
│   └── ...              # Other utilities
├── libexec/             # CLI commands
├── src/                 # Frontend & grammars
├── tests/               # Test files
├── dev/                 # Development docs (you are here)
│   ├── README.md        # This file
│   ├── RESEARCH.md      # Research documentation
│   └── REFACTOR.md      # Code refactoring docs
├── ll.json              # Calculus definition
└── Makefile             # Build commands
```

---

## Contributing Notes

1. **Before coding:** Read RESEARCH.md for theoretical context
2. **Before refactoring:** Check REFACTOR.md for planned changes
3. **Testing:** Any new code should have tests
4. **Types:** Add TypeScript types for new code

---

## Questions to Resolve

1. What semiring structure supports real-number accounting?
2. How to represent ownership modalities for blockchain?
3. What's the minimal Rust core for WASM integration?
4. Can we reuse Granule's approach for our quantitative extension?
