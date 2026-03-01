---
title: "V8 Megamorphic Dispatch: Inline Cache States, Costs, and Workarounds"
created: 2026-03-02
modified: 2026-03-02
summary: "How V8 inline caches degrade from monomorphic to megamorphic with >4 shapes/closures, the 3.5-60x performance penalty, and practical workarounds (switch dispatch, defunctionalization, code generation)"
tags: [performance, optimization, JavaScript, benchmarking, implementation, data-structures]
category: "Performance"
---

# V8 Megamorphic Dispatch

## What Is Megamorphic Dispatch?

V8 uses **inline caches (ICs)** at every operation site (property access, function call) to speculate on types. Each IC records the "shapes" (hidden classes / maps) it has seen and caches the fast path for that shape.

**IC state machine:**

```
uninitialized → monomorphic → polymorphic → megamorphic
                  (1 shape)    (2-4 shapes)   (5+ shapes)
```

- **Monomorphic**: single shape seen. V8 emits a direct guard + fast path. TurboFan can inline the callee.
- **Polymorphic**: 2-4 shapes seen. Linear search over cached entries. Still optimizable but slower.
- **Megamorphic**: >4 shapes. V8 gives up on per-site caching and falls back to a global megamorphic stub that does a generic hash-table lookup.

The threshold is controlled by the V8 flag `--max-polymorphic-map-count` (default: **4**).

### Property Access ICs vs Call ICs

For **property access**, the IC tracks the object's Map (hidden class). For **function calls**, the IC tracks the **closure identity** (the specific JSFunction object), not the SharedFunctionInfo. This means:

- Two closures from the same function literal are **different targets** to the call IC
- Creating N closure instances from a factory and calling them at one site -> megamorphic after the 5th distinct closure

This was flagged as V8 Issue #2206 by Vyacheslav Egorov: V8 should use SharedFunctionInfo identity instead of closure identity for call target feedback. As of current V8 (2025), this remains the behavior -- closure identity determines monomorphism for calls.

## Performance Cost

### Relative Slowdowns (property access)

| IC State | Relative Cost | Source |
|---|---|---|
| Monomorphic (1 shape) | 1.0x (baseline) | mrale.ph |
| Polymorphic (4 shapes) | ~1.4x | mrale.ph |
| Megamorphic (cache hit) | ~3.5x | builder.io |
| Megamorphic (cache overflow, ~1000+ shapes) | ~60x | builder.io |

### Chrome-specific benchmarks (Misko Hevery's DOM test)

- OBJ megamorphic vs OBJ monomorphic: **181.7x slower** (Chrome 72)
- DOM megamorphic vs DOM monomorphic: **2.9x slower** (Chrome 72)

### TypeScript compiler (real-world)

Microsoft's TypeScript team measured fixing megamorphic ICs:
- **16% faster** total compilation (range 10.5-23.7%)
- **20.8% faster** type checking (range 16.6-26.8%)
- Memory cost: only ~2.7% increase

### Absolute numbers (estimated from JVM analog)

JVM megamorphic virtual calls measure ~3ns monomorphic vs ~5ns megamorphic per call (Aleksey Shipilev's JVM Anatomy Quarks #16). V8's overhead is likely similar or slightly higher due to JavaScript's dynamic nature. Rough estimate for V8:

- Monomorphic call: ~2-5ns
- Megamorphic call (cache hit): ~10-20ns
- Megamorphic call (cache miss / overflow): ~50-200ns

### Impact on optimization

When a call site is megamorphic, TurboFan:
1. Cannot inline the callee
2. Cannot propagate types through the call
3. Cannot eliminate redundancies downstream
4. May decline to optimize the containing function entirely

The downstream effects are often worse than the raw IC miss cost.

## The Specific Problem: Many Closures at One Call Site

In an interpreter/engine pattern:

```javascript
// 44 different rule functions, called from one site
for (const rule of applicableRules) {
  rule.apply(state)  // megamorphic after 5th distinct closure
}
```

Each `rule.apply` is a different closure -> call IC sees >4 targets -> megamorphic.

## Workarounds

### 1. Switch/if-else dispatch table

Replace closure calls with a numeric opcode + switch:

```javascript
// Instead of: rule.apply(state)
switch (rule.opcode) {
  case 0: applyTensorL(state, rule.data); break;
  case 1: applyLoliR(state, rule.data); break;
  case 2: applyBangL(state, rule.data); break;
  // ...
}
```

**Pros**: Each case body is monomorphic. CPU branch predictor handles switch well for predictable patterns.
**Cons**: All cases in one function -- V8 may still struggle if the function is too large. Cannot easily inline individual cases.

**Variant -- split the switch into groups:**

```javascript
// Outer dispatch by category (small switch, predictable)
switch (rule.category) {
  case MULT: return dispatchMult(rule.opcode, state, rule.data);
  case ADD:  return dispatchAdd(rule.opcode, state, rule.data);
  case EXP:  return dispatchExp(rule.opcode, state, rule.data);
}

// Each sub-dispatcher is a small monomorphic-friendly function
function dispatchMult(opcode, state, data) {
  switch (opcode) {
    case OP_TENSOR_L: return applyTensorL(state, data);
    case OP_TENSOR_R: return applyTensorR(state, data);
    // ...
  }
}
```

### 2. Single function with data parameter (defunctionalization)

Replace N closures with one function + N data descriptors:

```javascript
// Instead of N closures:
function applyRule(state, descriptor) {
  // descriptor is a plain object with { opcode, slots, ... }
  // all descriptors share the same shape -> monomorphic property access
  const lhs = state.get(descriptor.lhsSlot);
  const rhs = state.get(descriptor.rhsSlot);
  // ...
}

// Call site is now monomorphic (always calls applyRule)
for (const rule of applicableRules) {
  applyRule(state, rule.descriptor)
}
```

**Pros**: Call site is trivially monomorphic. Property access on descriptor is monomorphic if all descriptors share the same shape.
**Cons**: Loses ability to specialize per-rule. The single function may be large and hard for TurboFan to optimize.

**Critical requirement**: all descriptor objects must have the **same hidden class**. Initialize all properties in the same order, always include all fields (use `null`/`0` for absent ones).

### 3. TypeScript-style: monomorphic wrapper + data indirection

The pattern Microsoft used for TypeScript AST nodes:

```javascript
// All nodes share identical top-level shape
class Node {
  constructor(kind, pos, end, data) {
    this.kind = kind;   // always present
    this.pos = pos;     // always present
    this.end = end;     // always present
    this.data = data;   // variant-specific payload
  }
}

// Access variant fields through getters
Object.defineProperty(Node.prototype, 'name', {
  get() { return this.data.name; }
});
```

All Node instances share one Map -> property access is monomorphic everywhere.
**Result**: 16% faster TypeScript compilation, 20.8% faster type checking.

### 4. Indirect call through a single wrapper

```javascript
// One stable call target
function callRule(fn, state, data) {
  return fn(state, data);
}

// The call to callRule is monomorphic (always same function)
// But fn(state, data) inside is still megamorphic
for (const rule of applicableRules) {
  callRule(rule.fn, state, rule.data);
}
```

**Does NOT help** for the inner `fn(state, data)` call -- that site still sees multiple closures. The wrapper only helps if you can use it to do additional work (like dispatching via opcode).

### 5. Map-based lookup

```javascript
const handlers = new Map();
handlers.set('tensor_l', applyTensorL);
handlers.set('loli_r', applyLoliR);

// Dispatch:
const handler = handlers.get(rule.name);
handler(state, rule.data);
```

**Does NOT help** -- the `handler(...)` call site still sees different closures. Map lookup adds its own overhead (~50-100ns for string-keyed Map.get).

### 6. Array-indexed dispatch

```javascript
const handlers = [
  applyTensorL,   // 0
  applyTensorR,   // 1
  applyLoliL,     // 2
  // ...44 handlers
];

// Dispatch:
handlers[rule.opcode](state, rule.data);
```

**Does NOT help** for the call IC -- the call site `handlers[i](...)` still sees different function objects. Array lookup is O(1) and fast, but the megamorphic call remains.

**However**, if you combine this with defunctionalization (workaround #2), the array stores data descriptors instead of functions, and a single `applyRule` function processes them.

## Creative Approaches

### 7. eval/new Function code generation

Generate specialized monomorphic code at startup:

```javascript
function compileDispatcher(rules) {
  const cases = rules.map((r, i) =>
    `case ${i}: return apply_${r.name}(state, data);`
  ).join('\n');

  return new Function('opcode', 'state', 'data', `
    switch (opcode) {
      ${cases}
    }
  `);
}

const dispatch = compileDispatcher(rules);
// dispatch is a single function, switch is monomorphic per case
```

**Pros**: Each branch is monomorphic. V8 can optimize the generated function. You can specialize the generated code further (inline constants, eliminate dead branches).
**Cons**: CSP restrictions may block `new Function`. Startup cost. Debugging is harder.

### 8. Separate hot path per rule category

If most calls go to a few rules, split the hot path:

```javascript
// Profile shows 80% of calls are tensor_l or loli_match
if (rule.opcode === OP_TENSOR_L) {
  applyTensorL(state, rule.data);       // monomorphic
} else if (rule.opcode === OP_LOLI_MATCH) {
  applyLoliMatch(state, rule.data);     // monomorphic
} else {
  genericApply(rule, state);            // megamorphic but cold
}
```

**Pros**: Hot path stays monomorphic. CPU branch predictor handles the if-chain well for skewed distributions.
**Cons**: Only works when the distribution is skewed.

### 9. WebAssembly function table

WASM has native indirect call dispatch through typed function tables (`call_indirect`). The WASM engine handles dispatch without JS IC overhead.

```javascript
// In WASM: funcref table + call_indirect
// Each function has a known signature
// Dispatch is: table lookup + type check + direct call
// No IC state machine, no megamorphic degradation
```

**Pros**: No megamorphic problem. Fixed overhead per indirect call (~3-5ns in WASM).
**Cons**: Requires porting hot path to WASM. JS<->WASM boundary crossing has overhead (~50-100ns per call). Only worth it if the hot loop lives entirely in WASM.

### 10. Unrolled interpreter with goto-like pattern

Simulate computed goto using a while-switch pattern that V8 can optimize:

```javascript
function interpret(rules, state) {
  let pc = 0;
  while (pc < rules.length) {
    const r = rules[pc];
    switch (r.opcode) {
      case 0: /* inline tensor_l logic */ pc++; continue;
      case 1: /* inline loli_r logic */  pc++; continue;
      // ...
    }
    pc++;
  }
}
```

V8's Ignition interpreter itself uses this pattern internally. The switch becomes a single indirect branch that the CPU branch predictor can learn.

## Summary: What Actually Works

| Approach | Eliminates megamorphic call? | Practical? | Speedup |
|---|---|---|---|
| Switch dispatch | Yes (per-case monomorphic) | High | 2-4x |
| Defunctionalization (single fn + data) | Yes (one call target) | High | 2-4x |
| Monomorphic wrapper (TS pattern) | Yes (for property access) | Medium | 10-20% |
| Hot-path split (if-else top rules) | Partially (hot path only) | High | 1.5-3x |
| eval/new Function codegen | Yes | Medium | 2-5x |
| Array/Map dispatch | No | - | None |
| Indirect wrapper | No | - | None |
| WASM function table | Yes | Low | Variable |

**Best bet for an interpreter engine**: **switch dispatch** or **defunctionalization**. These are the two patterns that directly eliminate the megamorphic call site while remaining practical and debuggable.

## Diagnostic Tools

- `--trace-ic` flag: shows IC state transitions (1=mono, P=poly, N=mega)
- [Deopt Explorer](https://github.com/microsoft/deoptexplorer-vscode): VS Code extension for analyzing V8 deoptimizations
- `--trace-deopt`: shows when TurboFan deoptimizes
- `--print-opt-code --code-comments`: shows generated optimized code
- `%GetOptimizationStatus(fn)` (with `--allow-natives-syntax`): check if function is optimized

## References

- Egorov, V. "What's up with monomorphism?" (2015) -- mrale.ph
- Egorov, V. "Grokking V8 closures for fun" (2012) -- mrale.ph
- Buckton, R. "Deopt Explorer" / TypeScript PR #51380, #51682, Issue #59198
- Hevery, M. DOM megamorphic access perf tests
- romgrk "Optimizing JavaScript for fun and profit"
- V8 Blog: "Fast properties in V8", "Super fast super property access"
- builder.io "Understanding Monomorphism to Improve Your JS Performance up to 60x"
