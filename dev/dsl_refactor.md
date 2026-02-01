# DSL Refactor: Extended Celf Implementation Plan

This document outlines the implementation plan for replacing ll.json with an Extended Celf DSL.

## Current State

### Architecture
```
ll.json                    # Monolithic: types + rules + metadata + rendering
    │
    ├── lib/parser.js      # Generates Jison grammar from ll.json
    ├── lib/calc.js        # Processes ll.json, builds rule DB with integer IDs
    ├── lib/node.js        # AST with (id, vals[]) structure
    ├── lib/polarity.js    # Infers polarity from rule structure
    └── lib/proofstate.js  # Focused proof search
```

### Pain Points
1. **ll.json is verbose** - 600+ lines mixing grammar, rules, rendering, metadata
2. **No type safety** - Rules are strings, typos silently fail
3. **Jison is unmaintained** - Poor error messages, no TypeScript
4. **Hard to extend** - Adding connectives requires JSON surgery
5. **No reuse** - Can't import stdlib or share definitions

---

## Target State

### Three-File Architecture
```
linear-logic.calc          # Types, connectives with @annotations
linear-logic.rules         # Inference rules (Celf + @pretty)
lib/*.mde                  # Pure Celf stdlib (optimism-mde compatible)
```

### Syntax Summary

**.calc files** (Extended Celf):
```celf
formula : type.

tensor : formula -> formula -> formula
  @ascii "_ * _"
  @latex "#1 \\otimes #2"
  @prec 60 left
  @polarity positive.
```

**.rules files** (Celf + annotations):
```celf
deriv : sequent -> type.

tensor_l : deriv (seq (comma G (struct (tensor A B))) C)
        <- deriv (seq (comma (comma G (struct A)) (struct B)) C)
  @pretty "*L"
  @invertible true.
```

**.mde files** (Pure Celf - optimism-mde compatible):
```celf
bin : type.
e : bin.
i : bin -> bin.

plus : bin -> bin -> bin -> type.
plus/z1 : plus e e e.
plus/s1 : plus (o M) (o N) (o R) <- plus M N R.
```

---

## Design Questions to Resolve

### 1. First-Order vs Higher-Order Abstract Syntax
**Question:** Support HOAS like `forall : (formula -> formula) -> formula`?

**Options:**
- **A) First-order only** - Explicit variable names, simpler to implement
- **B) Full HOAS** - True to LF, requires scope/binding machinery

**Recommendation:** Start with first-order. The current ll.json uses explicit `Atterm` for bound variables. HOAS can be added later.

### 2. Annotation Syntax
**Question:** Exact syntax for `@annotations`?

**Decided:**
- `@key value` - Simple value (identifier, string, number)
- `@key "string"` - String literal
- `@key n assoc` - Precedence with associativity

### 3. ll.json Generation vs Direct Use
**Question:** Generate ll.json for backwards compatibility or refactor consumers?

**Recommendation:**
- Phase 1: Generate ll.json from .calc/.rules
- Phase 2: Refactor consumers to use new AST directly
- This allows incremental migration without breaking the UI

### 4. FFI Hook Point
**Question:** Where does FFI dispatch integrate with proof search?

**Answer:** In `lib/prover.js` during rule application. When a rule is marked `@ffi`, check if arguments are ground, dispatch to JS function, unify result.

---

## Implementation Phases

### Phase 0: Baseline Tests (Before Refactoring)
**Goal:** Capture current behavior to verify refactor doesn't break anything.

**Tasks:**
- [ ] Test current parser output for all ll.json constructs
- [ ] Test proof search for known theorems (from tests/proofstate.js)
- [ ] Test rendering (ASCII, LaTeX) for all connectives
- [ ] Test polarity inference
- [ ] Snapshot ll.json-derived Calc.db for comparison

**Files:**
```
tests/parser-snapshot.js    # Parser output tests
tests/calc-db-snapshot.js   # Calc.db structure tests
tests/rendering-snapshot.js # toString() output tests
```

### Phase 1: Ohm Parser for Pure Celf
**Goal:** Parse optimism-mde style .mde files.

**Grammar Elements:**
```ohm
Celf {
  Program = Declaration*

  Declaration = TypeDecl | ConstDecl | ClauseDecl

  TypeDecl = ident ":" "type" "."

  ConstDecl = ident ":" Type "."

  ClauseDecl = clauseName ":" Term ("." | BackChain)

  BackChain = "<-" Term BackChain
            | "."

  Type = Type "->" Type      -- arrow
       | Type "-o" Type      -- loli
       | ident               -- atom
       | "(" Type ")"        -- paren

  Term = Term "*" Term       -- tensor
       | Term "-o" "{" Term "}" -- forward
       | "!" Term            -- bang
       | Application

  Application = Application Atom
              | Atom

  Atom = ident
       | "(" Term ")"
       | var

  ident = lower (alnum | "_")*
  var = upper (alnum | "_")*
  clauseName = ident ("/" ident)?

  comment = "%" (~"\n" any)*
}
```

**Tests:**
- [ ] Parse optimism-mde/lib/bin.mde successfully
- [ ] Parse optimism-mde/main.mde successfully
- [ ] AST structure matches expected form
- [ ] Variables correctly identified (uppercase)

**Files:**
```
lib/celf/grammar.ohm        # Ohm grammar
lib/celf/parser.js          # Ohm semantics → AST
tests/celf-parser.js        # Parser tests
```

### Phase 2: Extended Celf (@annotations)
**Goal:** Parse .calc files with annotations.

**Grammar Extension:**
```ohm
CelfExtended <: Celf {
  ConstDecl := ident ":" Type AnnotationBlock? "."
  ClauseDecl := clauseName ":" Term BackChain AnnotationBlock?

  AnnotationBlock = Annotation+

  Annotation = "@" annotKey annotValue?

  annotKey = ident
  annotValue = string
             | number assoc?
             | ident

  assoc = "left" | "right" | "none"
  string = "\"" (~"\"" any)* "\""
}
```

**Annotation Schema:**
| Key | Values | Used In |
|-----|--------|---------|
| `@ascii` | string | .calc |
| `@latex` | string | .calc |
| `@isabelle` | string | .calc |
| `@prec` | number [assoc] | .calc |
| `@polarity` | positive/negative | .calc |
| `@category` | multiplicative/additive/exponential | .calc |
| `@dual` | ident | .calc |
| `@shallow` | true/false | .calc |
| `@pretty` | string | .rules |
| `@invertible` | true/false | .rules |
| `@direction` | forward/backward | .rules |
| `@ffi` | ident | .calc |
| `@mode` | mode-spec | .calc |

**Tests:**
- [ ] Parse annotation blocks
- [ ] Extract annotations into structured metadata
- [ ] Handle missing annotations gracefully

### Phase 3: ll.json Generation
**Goal:** Generate ll.json from .calc + .rules for backwards compatibility.

**Transformation:**
```
.calc types/connectives  →  calc_structure
.calc @annotations       →  ascii/latex/precedence fields
.rules definitions       →  rules section
Inferred from structure  →  calc_structure_rules_meta
```

**Tests:**
- [ ] Generate ll.json from linear-logic.calc + linear-logic.rules
- [ ] Compare with existing ll.json (structure, not exact match)
- [ ] Verify generated ll.json works with current parser.js
- [ ] Verify Calc.init() produces equivalent Calc.db

**Files:**
```
lib/celf/generator.js       # .calc → ll.json
tests/ll-generation.js      # Generation tests
```

### Phase 4: Direct AST Consumers
**Goal:** Refactor lib/ to consume new AST directly.

**Strategy:**
1. Create abstraction layer `lib/calculus.js`
2. Support loading from ll.json OR .calc/.rules
3. Gradually migrate consumers

**Interface:**
```javascript
class Calculus {
  // Load from ll.json (legacy)
  static fromJSON(json) { ... }

  // Load from .calc + .rules
  static fromCelf(calcPath, rulesPath) { ... }

  // Unified API
  getConnectives() { ... }
  getRules() { ... }
  getRule(name) { ... }
  getPolarity(connective) { ... }
}
```

**Tests:**
- [ ] Both loading paths produce equivalent Calculus
- [ ] Proof search works with both
- [ ] Rendering works with both

### Phase 5: FFI Support
**Goal:** Support `@ffi` and `@mode` for computational predicates.

**Syntax:**
```celf
plus : bin -> bin -> bin -> type
  @ffi "arithmetic.plus"
  @mode + + -
  @verify true.
```

**Implementation:**
1. Register FFI functions at startup
2. During proof search, check if goal matches FFI predicate
3. Verify mode (inputs are ground)
4. Call JS function
5. Unify result

**Files:**
```
lib/ffi/registry.js         # FFI function registry
lib/ffi/arithmetic.js       # Built-in arithmetic
lib/celf/mode-check.js      # Mode checking
```

**Tests:**
- [ ] Parse @ffi and @mode annotations
- [ ] Mode checking rejects non-ground inputs
- [ ] FFI dispatch computes correct results
- [ ] Verify option catches errors

### Phase 6: Stdlib and Migration
**Goal:** Create reusable stdlib, migrate to new system.

**Stdlib:**
```
lib/celf/stdlib/
├── base.mde          # nat, bin, bool
├── arithmetic.mde    # plus, mul, etc.
└── linear-logic.calc # ILL connectives
```

**Migration:**
- [ ] Create linear-logic.calc from ll.json
- [ ] Create linear-logic.rules from ll.json
- [ ] Port lib/bin.mde from optimism-mde
- [ ] Verify all tests pass
- [ ] Remove ll.json (or keep as generated artifact)

---

## File Structure After Refactor

```
/home/mhhf/src/calc/
├── calc/                      # NEW: Calculus definitions
│   ├── linear-logic.calc      # Connectives with annotations
│   ├── linear-logic.rules     # Inference rules
│   └── stdlib/
│       ├── base.mde           # nat, bin, bool
│       └── arithmetic.mde     # plus, mul, etc.
│
├── lib/
│   ├── celf/                  # NEW: Celf parser
│   │   ├── grammar.ohm
│   │   ├── parser.js
│   │   ├── generator.js       # → ll.json
│   │   └── mode-check.js
│   │
│   ├── ffi/                   # NEW: FFI support
│   │   ├── registry.js
│   │   └── arithmetic.js
│   │
│   ├── calculus.js            # NEW: Unified calculus API
│   │
│   ├── calc.js                # MODIFIED: use calculus.js
│   ├── parser.js              # DEPRECATED: Jison generation
│   ├── node.js                # UNCHANGED
│   ├── prover.js              # MODIFIED: FFI support
│   └── ...
│
├── ll.json                    # GENERATED from .calc/.rules
│
└── tests/
    ├── celf-parser.js         # NEW
    ├── ll-generation.js       # NEW
    └── ffi.js                 # NEW
```

---

## Risks and Mitigations

### Risk 1: Parser complexity
**Mitigation:** Start with pure Celf subset. Ohm handles left-recursion and precedence well.

### Risk 2: Breaking proof search
**Mitigation:** Extensive baseline tests before refactoring. Dual loading path during migration.

### Risk 3: Scope creep
**Mitigation:** Each phase is independently valuable. Can stop after any phase.

---

## Dependencies

**Required:**
- [ ] Install Ohm: `npm install ohm-js`

**Optional:**
- [ ] tree-sitter (future, for editor support)

---

## Success Criteria

1. **Phase 1 Complete:** Can parse optimism-mde files
2. **Phase 3 Complete:** Can generate ll.json from .calc/.rules
3. **Phase 4 Complete:** Proof search works without ll.json
4. **Phase 5 Complete:** `plus(2,3,X)` computes X=5 via FFI

---

## Open Questions for User

1. **HOAS Priority:** Is higher-order abstract syntax (for quantifier binding) needed soon, or can we defer?

2. **Backwards Compatibility:** Keep ll.json as generated artifact indefinitely, or remove after migration?

3. **Stdlib Location:** Should stdlib live in this repo or separate (optimism-mde style)?

4. **Parser Target:** Stick with Ohm, or evaluate tree-sitter for editor integration?
