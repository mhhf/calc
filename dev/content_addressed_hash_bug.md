# Content-Addressed Architecture Bug

## Summary

The v2 codebase claims to use content-addressed ASTs but actually passes around embedded object trees, recomputing hashes on every operation. This causes **5,876x redundant hashing** (82,269 hash computations for just 14 unique ASTs in a simple proof).

## The Correct Architecture

```
AST_STORE[hash] = { tag, children: [child_hash_1, child_hash_2] }
```

- Hash IS the pointer/identifier (CID)
- Children are stored as hashes (references), not embedded objects
- Equality: `hash1 === hash2` (O(1) integer comparison)
- Lookup: `AST_STORE[hash]` to dereference

## What We Have (Broken)

```javascript
// Embedded tree - NO content addressing
{ tag: 'tensor', children: [
    { tag: 'freevar', children: ['A'] },  // Full object
    { tag: 'freevar', children: ['B'] }   // Full object
]}
```

- ASTs are plain JS objects with no identity
- Hash computed from scratch on every comparison/lookup
- No store, no interning, no memoization

---

## Files Requiring Changes

### 1. AST Creation (Critical)

**`lib/v2/calculus/index.js:184-212`** - `buildAST()`
```javascript
// CURRENT (broken):
AST[name] = (a, b) => ({ tag: name, children: [a, b] });

// SHOULD BE:
AST[name] = (a, b) => intern(name, [a, b]);
// Where intern() stores in AST_STORE and returns hash
```

**`lib/v2/calculus/index.js:284,299,309,329,331`** - Parser creates objects
```javascript
// CURRENT: left = { tag: op.name, children: [left, right] };
// SHOULD: left = intern(op.name, [left, right]);
```

**`lib/v2/browser.js:82-98,165,179,188,205,207`** - Duplicate AST factory
Same problem - creates plain objects, needs interning.

### 2. AST Hashing (Critical)

**`lib/v2/kernel/ast-hash.js`** - No memoization, no store
```javascript
// CURRENT (recomputes every time):
const hashAST = ast => {
  let h = hashString(ast.tag);
  for (const c of ast.children) h = hashCombine(h, hashAST(c));
  return h;
};

// WITH CORRECT ARCHITECTURE:
// hashAST not needed - hash IS the identifier
// Children already stored as hashes
const getHash = nodeOrHash => typeof nodeOrHash === 'number' ? nodeOrHash : nodeOrHash._hash;
```

### 3. Equality Check (Critical)

**`lib/v2/kernel/substitute.js:8`**
```javascript
// CURRENT (recomputes 2 hashes per call!):
const eq = (a, b) => a === b || (a?.tag && b?.tag && hashAST(a) === hashAST(b));

// SHOULD BE:
const eq = (a_hash, b_hash) => a_hash === b_hash;
```

### 4. Sequent Storage (Major)

**`lib/v2/kernel/sequent.js:19,32-35`**
```javascript
// CURRENT: stores formula objects
const seq = (contexts, succedent) => ({ contexts, succedent, _hash: null });
// contexts = { linear: [formula_obj, ...], cartesian: [formula_obj, ...] }

// SHOULD BE: stores formula hashes
// contexts = { linear: [formula_hash, ...], cartesian: [formula_hash, ...] }
```

**`lib/v2/kernel/sequent.js:44-54,60-70`** - copy/substitute
Currently deep-copies AST objects. Should create new hashes via interning.

**`lib/v2/kernel/sequent.js:109-117`** - hash()
Currently iterates and calls `hashAST()` on each formula. Should just combine stored hashes.

**`lib/v2/kernel/sequent.js:131-156`** - Context operations
All work with formula objects, should work with hashes.

### 5. Context Multiset (Major)

**`lib/v2/prover/focused/context.js`** - Entire file

The Context module has the right IDEA (keyed by hash) but wrong implementation:
```javascript
// CURRENT: stores formula objects, recomputes hash on every operation
ms[h] = { formula, count, hash: h };
const h = String(hashAST(formula));  // Called on every add/remove/lookup!

// SHOULD BE: stores only hashes and counts
ms[hash] = count;
// Formula retrieval: AST_STORE[hash] when needed
```

Specific locations:
- Line 25: `hashAST(formula)` in `fromArray()`
- Line 66: `hashAST(formula)` in `add()`
- Line 102: `hashAST(formula)` in `removeFormula()`
- Line 109: `hashAST(formula)` in `has()`
- Line 195: `hashAST(newFormula)` in `substitute()`

### 6. Prover (Major)

**`lib/v2/prover/focused/prover.js`**

All these locations pass formula objects and recompute hashes:
- Line 130: `String(Seq.hashAST(f))` - hash for focus tracking
- Line 155: `Seq.hashAST(linear[i])` - hash in tryIdentity
- Line 166: `Seq.hashAST(focused)` - hash in tryIdentity
- Line 197: `Seq.hashAST(formula)` - hash in applyRule
- Line 341: `String(Seq.hashAST(f))` - findIndex by hash (!)

Focus state stores hash as string, then searches by recomputing:
```javascript
// CURRENT (insane):
focusIdx = linear.findIndex(f => String(Seq.hashAST(f)) === state.focusHash);

// SHOULD BE: linear is [hash1, hash2, ...], focusHash is a hash
focusIdx = linear.indexOf(state.focusHash);
```

Rule specs access `formula.children`:
- Lines 487, 502, 504, 514, 516, 527, 529, 543, 557, 559, 569, 571, 601, 612, 614, 626

These need AST_STORE dereference: `AST_STORE[formula_hash].children`

### 7. Unification (Major)

**`lib/v2/kernel/unify.js`**

Currently operates on AST objects:
```javascript
// CURRENT:
if (t0.tag === t1.tag && t0.children.length === t1.children.length) {
  t0.children.forEach((c, i) => G.push([c, t1.children[i]]));
}

// SHOULD BE (with hash pointers):
const n0 = AST_STORE[t0], n1 = AST_STORE[t1];
if (n0.tag === n1.tag && n0.children.length === n1.children.length) {
  n0.children.forEach((c, i) => G.push([c, n1.children[i]]));  // c, n1.children[i] are hashes
}
```

- Line 9: `ast.children[0]` needs dereference
- Line 11: `ast.children[0]` needs dereference
- Line 21: `eq(t0, t1)` - should be `t0 === t1` (hash comparison)
- Line 32: `t0.children[0] !== t1.children[0]` - should compare hashes
- Lines 35-36: `t0.children` needs dereference

### 8. Substitution (Major)

**`lib/v2/kernel/substitute.js`**

```javascript
// CURRENT: Creates new objects, doesn't intern
const sub = (ast, v, val) => {
  if (eq(ast, v)) return copy(val);
  const cs = ast.children.map(c => c?.tag ? sub(c, v, val) : c);
  return { tag: ast.tag, children: cs };  // New object, not interned!
};

// SHOULD BE: Works with hashes, interns results
const sub = (ast_hash, v_hash, val_hash) => {
  if (ast_hash === v_hash) return val_hash;
  const node = AST_STORE[ast_hash];
  const new_children = node.children.map(c => sub(c, v_hash, val_hash));
  return intern(node.tag, new_children);  // Returns hash
};
```

- Line 8: `eq()` should be hash comparison
- Line 10: `copy()` creates objects, should just return hash (immutable)
- Line 14: `eq(ast, v)` should be hash comparison
- Line 16: Creates new object, should intern

### 9. Proof Tree (Minor)

**`lib/v2/prover/pt.js`**

- Lines 24-25, 31-32: `conclusion`, `delta_in`, `delta_out` store objects
- Line 43-50: `copy()` deep-copies everything
- Line 134: `copy(entry.formula)` - should just be hash

### 10. Parser Integration (Major)

**`lib/v2/parser/sequent-parser.js:73,77`**
```javascript
// CURRENT: returns AST object
return calculus.parse(formulaStr);

// SHOULD BE: parse returns hash (after interning)
```

---

## New Components Needed

### AST Store Module (`lib/v2/kernel/ast-store.js`)

```javascript
const AST_STORE = new Map();  // hash -> { tag, children: [hash, ...] }
let nextId = 0;

function intern(tag, children) {
  // children are already hashes
  const h = computeHash(tag, children);
  if (AST_STORE.has(h)) return h;
  AST_STORE.set(h, { tag, children, _id: nextId++ });
  return h;
}

function get(hash) {
  return AST_STORE.get(hash);
}

function getTag(hash) {
  return AST_STORE.get(hash)?.tag;
}

function getChildren(hash) {
  return AST_STORE.get(hash)?.children || [];
}

// For leaf nodes (atoms, freevars with string children)
function internLeaf(tag, value) {
  const h = computeHash(tag, [hashString(value)]);
  if (AST_STORE.has(h)) return h;
  AST_STORE.set(h, { tag, children: [value], _id: nextId++ });
  return h;
}
```

---

## Migration Strategy

### Phase 1: Add Store + Intern (non-breaking)
1. Create `ast-store.js` with `intern()` and `get()`
2. Modify `buildAST()` to intern and return hash
3. Add `_hash` field to objects for gradual migration

### Phase 2: Convert Core Modules
1. `substitute.js` - work with hashes
2. `unify.js` - work with hashes
3. `ast-hash.js` - just return stored hash

### Phase 3: Convert Data Structures
1. `sequent.js` - store hashes in contexts
2. `context.js` - simplify to hash->count map

### Phase 4: Convert Prover
1. `prover.js` - pass hashes, dereference when needed
2. Remove all `hashAST()` calls

### Phase 5: Cleanup
1. Remove `hashAST()` (hash is the pointer)
2. Remove `eq()` for ASTs (just compare hashes)
3. Remove `copy()` for ASTs (immutable, just return hash)

---

## Expected Performance Improvement

Current (broken): 82,269 hash operations for simple proof
Target: ~14 hash operations (one per unique AST, computed at creation)

**Speedup: ~5,876x for hashing operations**

Since hashing was 76% of proof time, overall speedup: **~4x minimum**

With proper interning, many operations become O(1):
- Equality: hash comparison vs tree traversal
- Context membership: hash lookup vs tree hash + lookup
- Substitution: share structure vs deep copy

Expected overall: **10-50x faster proofs**
