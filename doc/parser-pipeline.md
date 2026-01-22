# Parser Pipeline

How sequent strings in ll.json become AST nodes.

## Overview

```
ll.json              lib/parser.js           Jison              out/parser.js
─────────────────────────────────────────────────────────────────────────────
calc_structure   →   generates grammar   →   compiles   →   parses strings
(types, syntax)      object dynamically      to parser       into Node AST
```

## Step by Step

### 1. ll.json defines the calculus

Types and their syntax:
```json
"Formula_Bin_Op": {
  "Formula_Tensor": {
    "ascii": "*",
    "latex": "\\otimes"
  },
  "Formula_Loli": {
    "ascii": "-o",
    "latex": "\\multimap"
  }
}
```

Rules reference these via strings:
```json
"Tensor_R": [
  "?X, ?Y |- -- : [ F?A * F?B ]",
  "?X |- -- : [ F?A ]",
  "?Y |- -- : [ F?B ]"
]
```

### 2. lib/parser.js generates Jison grammar

- Iterates over `calc_structure`
- Extracts symbols from `ascii` fields (`*`, `-o`, `|-`, etc.)
- Builds BNF rules mapping syntax to Node constructors
- Each rule becomes: `[syntax_pattern, "$$ = new yy.Node(id, [children]);"]`

### 3. Jison compiles to parser

```bash
./libexec/calc-genparser
```

Outputs `out/parser.js` - a standalone parser module.

### 4. Parser converts strings to AST

```javascript
const parser = require("./out/parser.js");
parser.parse("?X |- -- : F?A * F?B")
// → Node { id: ..., vals: [...] }
```

## Key Files

 | File                     | Role                                       |
 | ------                   | ------                                     |
 | `ll.json`                | Calculus definition (types, syntax, rules) |
 | `lib/parser.js`          | Grammar generator                          |
 | `libexec/calc-genparser` | Build script                               |
 | `out/parser.js`          | Generated parser                           |
 | `lib/node.js`            | AST node class                             |

## Adding New Syntax

1. Add type/connective to `calc_structure` in ll.json with `ascii` field
2. Run `npm run build:parser`
3. Parser now recognizes the new syntax

No manual grammar editing needed.
