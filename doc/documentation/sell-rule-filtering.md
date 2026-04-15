# SELL Rule Filtering

Subexponential-scoped rule sets for forward execution directives.

## Overview

SELL (Subexponential Linear Logic) rule filtering restricts which forward rules participate in `exec()` and `explore()` calls. It implements the first non-trivial SELL generalization: moving from `|I|=1` (standard ILL, one subexponential) to `|I|>1` with a label preorder derived from the import tree.

See THY_0013 for the theoretical foundation (indexed lax monad `{A}_a`).

## Surface Syntax

```ill
#import(evm.ill)
#import(gas_model.ill)

% Tier 1: label list — evm + transitive deps only
#symex (rules: [evm]) [S] pc 0 * gas 0xffff * storage S.

% Tier 1: multiple labels
#symex (rules: [evm, gas_model]) [S] pc 0 * gas 0xffff * storage S.

% Tier 2: named module
@module evm_full = evm + gas_model.
@module evm_light = evm_full - {gas_charge, gas_refund}.
#symex (rules: evm_light) [S] pc 0 * gas 0xffff * storage S.

% Default: all rules (backward-compatible)
#symex [S] pc 0 * gas 0xffff * storage S.
```

## Architecture

```
declarations.js          index.js                 forward.js / explore.js
┌─────────────┐         ┌──────────────────┐      ┌──────────────────┐
│ (rules: ..) │ ──AST──▸│ filterRules()    │──▸   │ run(state, rules)│
│ @module ..  │         │ labelIndex       │      │ (generic, no     │
│             │         │ modules          │      │  label awareness) │
└─────────────┘         │ resolveLabels()  │      └──────────────────┘
                        └──────────────────┘
```

The filtering boundary sits in `index.js` between the user-facing `calc.exec()`/`calc.explore()` wrappers and the generic engine. The generic engine (`forward.js`, `explore.js`) accepts a pre-filtered rules array and knows nothing about labels.

## Design Decisions

| ID | Decision | Rationale |
|----|----------|-----------|
| D1 | Transitive deps included | Forward rules depend on backward clauses from imports |
| D2 | Only forward rules filtered | Backward clauses provide persistent goal resolution |
| D3 | Root file always participates | The root file defines the program under analysis |
| D4 | Label = filename stem | `evm.ill` → `evm`; collision → load-time error |
| D5 | Default = all rules | No existing code breaks |
| D6 | `querySettings` separate from `queries` | Doesn't change `queries: Map<string, number>` shape |
| D7 | Modules shadow labels | `(rules: 'x')` checks modules first, falls back to label |

## API

```javascript
const calc = mde.load('main.ill');

// Tier 1: label list
calc.exec(state, { rules: ['evm'] });
calc.exec(state, { rules: ['evm', 'gas_model'] });

// Tier 2: named module
calc.exec(state, { rules: 'evm_full' });

// Default: all rules
calc.exec(state, {});

// Same for explore
calc.explore(state, { rules: ['evm'], maxDepth: 5 });

// Introspection
calc.labelIndex;    // Map<label, ruleName[]>
calc.modules;       // Map<moduleName, Set<ruleName>>
calc.querySettings; // Map<kind, settings>
```

## Dispatch

- `Array.isArray(rules)` → Tier 1: resolve labels + transitive deps, filter by `sourceLabel`
- `typeof rules === 'string'` → check `modules` Map first (D7), fall back to single label
- `rules` absent → return all compiled rules

## Module Algebra

Operators (precedence: `&` > `+`/`-`, left-associative):

| Op | Meaning | Example |
|----|---------|---------|
| `+` | union | `evm + gas` |
| `-` | subtraction | `full - {gas_charge}` |
| `&` | intersection | `evm & gas` |
| `{..}` | rule name set | `{gas_charge, gas_refund}` |

Grammar:
```
module_expr := module_term (( '+' | '-' ) module_term)*
module_term := module_atom ('&' module_atom)*
module_atom := IDENT | '{' IDENT (',' IDENT)* '}' | '(' module_expr ')'
```

Modules resolve sequentially — each definition can reference previously-defined modules or import labels.

## Soundness

Restricting the rule set is a **sound operational refinement**: any derivation found under restricted rules is valid in the full logic. Restriction can only miss derivations, never produce invalid ones. See THY_0013 §6.

## Files

| File | Role |
|------|------|
| `lib/parser/declarations.js` | `parseQuerySettings()`, `parseModuleDefinition()` |
| `lib/engine/convert.js` | `_scanDeclNames()`, threading querySettings/moduleDecls |
| `lib/engine/compile.js` | `sourceLabel` field on compiled rules |
| `lib/engine/index.js` | `labelDeps()`, `filterRules()`, `_resolveModuleExpr()`, exec/explore wrappers |
