# Architecture: Pipelines and ll.json Migration

## Current Data Flow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        NEW DSL PIPELINE (incomplete)                     │
│                                                                         │
│  lnl.family ─┐                                                          │
│              │   ┌─────────────┐   ┌───────────────┐                    │
│  ill.calc ───┼──►│  ts-parser  │──►│   generator   │──► calc_db        │
│              │   │ (tree-sit.) │   │ (lib/celf/)   │   (in memory)     │
│  ill.rules ──┘   └─────────────┘   └───────────────┘       │           │
│                                                             ▼           │
│                                              ┌─────────────────────────┐│
│                                              │ tests/ll-generation.js  ││
│                                              │ tests/family-generation ││
│                                              └─────────────────────────┘│
└─────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────┐
│                      CURRENT ll.json PIPELINE (live)                    │
│                                                                         │
│                ┌─────────────┐   ┌─────────────┐   ┌───────────────┐   │
│   ll.json ────►│  Calc.init  │──►│  Calc.db    │──►│  everything   │   │
│                └─────────────┘   └─────────────┘   └───────────────┘   │
│                                        │                                │
│                    ┌───────────────────┼───────────────────┐            │
│                    ▼                   ▼                   ▼            │
│             ┌──────────┐        ┌──────────┐        ┌──────────┐       │
│             │ parser.js│        │ prover   │        │ renderer │       │
│             │ (Jison)  │        │proofstate│        │ node.js  │       │
│             └──────────┘        └──────────┘        └──────────┘       │
└─────────────────────────────────────────────────────────────────────────┘
```

## File Dependencies on ll.json

### Core Library (lib/)
| File | Uses | What For |
|------|------|----------|
| `sequent.js:31` | `require('../ll.json')` | Sequent parsing/construction |
| `calc.js` | `Calc.init(calc)` | Initializes Calc.db from ll.json-format object |
| `parser.js` | `Calc.calc.calc_structure` | Generates Jison grammar |
| `node.js` | `Calc.db.rules[id]` | Node rendering (ascii/latex/isabelle) |
| `proofstate.js` | `Calc.db.rules[id]` | Rule lookup, polarity checking |
| `prover.js` | `calculus.rules` | Rule patterns for proof search |
| `substitute.js` | `Calc.db.rules[node.id]` | Formula_Forall check |
| `mgu.js` | `Calc.db.rules` | Unification |
| `llt_compiler.js` | `Calc.calc.calc_structure["Formula"]` | LLT compilation |

### CLI Tools (libexec/)
All CLI tools directly `require('../ll.json')`:
- calc-parse, calc-proof, calc-genparser, calc-export, calc-gendoc
- calc-debug-*, calc-saturate, calc-tmp, calc-compare

### Tests
Most tests directly `require('../ll.json')`:
- parser-baseline, calc-db-baseline, proofstate, node, test, intern, rendering-baseline
- polarity-inference, sequent-lnl

### Benchmarks
- `benchmarks/proof/proofs.bench.js`, `benchmarks/micro/mgu.bench.js`

## New DSL Pipeline (lib/celf/)

### Files
```
lib/celf/
├── ts-parser.js    # Tree-sitter parser for .family/.calc/.rules
├── generator.js    # Converts parsed AST to ll.json format
└── loader.js       # Runtime loader (async/sync APIs)
```

### What it does
1. `ts-parser.js` parses Extended Celf syntax using tree-sitter
2. `generator.js` extracts declarations, rules, and generates ll.json-compatible structure
3. `loader.js` provides `loadILL()` / `loadILLSync()` for runtime loading

### Current limitation
The generated `calc_structure` has **different shape** than ll.json:
- **ll.json**: 2-arg sequent `X |- Y`, uses `Formula_Bin_Op` factoring
- **DSL output**: 3-arg sequent `G ; D |- C`, direct constructors like `Formula_Tensor`

This means the **Jison parser expects different structure** than what DSL generates.

## Key Structural Differences

### ll.json structure (current)
```json
{
  "calc_structure": {
    "Formula": {
      "Formula_Freevar": { "type": "string", "ascii": "F? _" },
      "Formula_Atprop": { "type": "Atprop" }
    },
    "Formula_Bin_Op": {
      "Formula_Tensor": { "ascii": "_ * _", "type": ["Formula", "Formula"] },
      "Formula_Loli": { "ascii": "_ -o _", "type": ["Formula", "Formula"] }
    },
    "Sequent": {
      "Sequent": { "type": ["Structure", "Structure"], "ascii": "_ |- _" }
    }
  }
}
```

### DSL-generated structure (new)
```json
{
  "calc_structure": {
    "Formula": {
      "Formula_Freevar": { "type": "string", "ascii": "F? _" },
      "Formula_Tensor": { "ascii": "_ * _", "type": ["Formula", "Formula"] },
      "Formula_Loli": { "ascii": "_ -o _", "type": ["Formula", "Formula"] }
    },
    "Sequent": {
      "Sequent_Seq": { "type": ["Structure", "Structure", "Structure"], "ascii": "_ ; _ |- _" }
    }
  }
}
```

Key differences:
1. **No `Formula_Bin_Op` factoring** - connectives directly in `Formula`
2. **3-arg sequent** vs 2-arg sequent
3. **Different constructor names** (`Formula_Tensor` vs `Sequent_Seq`)

## Migration Plan

### Phase 1: Parallel Structures (CURRENT)
**Status**: Complete ✓

- [x] Create new DSL files (lnl.family, ill.calc, ill.rules)
- [x] Implement tree-sitter parser
- [x] Implement generator producing ll.json format
- [x] Tests verify generation works

**Blocking issue**: Generated format differs from ll.json, parser incompatible.

### Phase 2: Parser Abstraction Layer
**Goal**: Make parser work with both structures.

**Option A: Generate ll.json-compatible output**
- Modify generator to produce Formula_Bin_Op factoring
- Modify generator to produce 2-arg sequents
- Pros: No changes to parser/prover
- Cons: Loses the cleaner 3-arg design

**Option B: Abstract parser over structure shape**
- Create parser configuration layer
- Parser reads config to determine sequent arity, factoring
- Pros: Supports both old and new designs
- Cons: More complex

**Option C: Rewrite parser for new structure**
- Update Jison grammar generation for 3-arg sequents
- Remove Formula_Bin_Op dependency
- Pros: Clean slate, matches DSL design
- Cons: Breaking change, needs full migration

**Recommended: Option A first, then C**
- First make generator produce ll.json-compatible output
- This lets us remove ll.json immediately
- Then later refactor to cleaner structure

### Phase 3: Generator produces ll.json-compatible format
**Tasks**:
- [ ] Add Formula_Bin_Op grouping logic to generator
- [ ] Convert 3-arg seq() to 2-arg Sequent
- [ ] Match freevar naming conventions
- [ ] Update rule pattern generation

### Phase 4: Replace ll.json with generated output
**Tasks**:
- [ ] Update sequent.js to use loader instead of require
- [ ] Update all CLI tools to use loader
- [ ] Update all tests to use loader
- [ ] Delete ll.json file
- [ ] Make generation part of build step (or lazy load)

### Phase 5: (Optional) Migrate to new structure
**Tasks**:
- [ ] Update parser.js for 3-arg sequents
- [ ] Update prover for direct Formula constructors
- [ ] Simplify generator to output clean structure
- [ ] Update all tests

## Immediate Next Steps

1. **Understand ll.json structure deeply** - compare exact shape expected by parser.js
2. **Modify generator.js** to produce ll.json-compatible output
3. **Test**: `Calc.init(generatedOutput)` should work with existing parser
4. **Create loader facade** that generators and returns calc_db
5. **Replace require('../ll.json')** with loader call
6. **Delete ll.json**
