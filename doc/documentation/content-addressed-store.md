---
title: "Content-Addressed Store & Term Architecture"
created: 2026-02-13
modified: 2026-02-13
summary: How the content-addressed Store works — node model, hashing, substitution, unification, complexity analysis
tags: [architecture, store, hash-consing, content-addressing, kernel]
---

# Content-Addressed Store & Term Architecture

All formulas, terms, and logical objects in CALC are **content-addressed hashes** — plain JavaScript numbers. The Store is a global hash-consing table that maps hashes to `{ tag, children }` nodes. Structural equality is O(1) hash comparison.

> **Research background:** [[../research/content-addressed-formulas]] — design rationale, hash function selection, migration from AST objects
> **Prover architecture:** [[architecture]] — how the Store is used across prover layers L1-L5
> **Optimization research:** [[../research/backward-prover-optimization]] — substitution/unification benchmarks

---

## 1. Node Model

Every term is a node in a Merkle DAG:

```
STORE[hash] = { tag: string, children: (hash | string | bigint)[] }
```

**Tags** are the outermost constructor: `atom`, `freevar`, `tensor`, `loli`, `with`, `bang`, `app`, `one`, `binlit`, `strlit`, `charlit`, `type`, `monad`, `arrow`.

**Children** have three types:

| Type | Meaning | Example |
|------|---------|---------|
| `number` | Hash reference to another term | `tensor(h1, h2)` → children: `[h1, h2]` |
| `string` | Primitive leaf value | `atom('plus')` → children: `['plus']` |
| `bigint` | Compact numeric literal | `binlit(42n)` → children: `[42n]` |

**Leaf nodes** (no term children): `atom`, `freevar`, `binlit`, `strlit`, `charlit`, `one`, `type`
**Branch nodes** (term children): `tensor`, `loli`, `with`, `bang`, `app`, `monad`, `arrow`

### Example

The formula `A ⊗ (B ⊸ C)` produces four Store entries:

```
h1 = put('atom', ['A'])     → { tag: 'atom', children: ['A'] }
h2 = put('atom', ['B'])     → { tag: 'atom', children: ['B'] }
h3 = put('atom', ['C'])     → { tag: 'atom', children: ['C'] }
h4 = put('loli', [h2, h3])  → { tag: 'loli', children: [h2, h3] }
h5 = put('tensor', [h1, h4]) → { tag: 'tensor', children: [h1, h4] }
```

If `A` appears elsewhere, `put('atom', ['A'])` returns the same `h1` — no new entry.

---

## 2. Hashing

**Algorithm:** FNV-1a (32-bit). Fast, no crypto overhead, consistent across runs.

```
computeHash(tag, children):
  h = FNV_OFFSET (0x811c9dc5)
  h = hashCombine(h, hashString(tag))
  h = hashCombine(h, children.length)    // arity discrimination
  for each child c:
    number  → hashCombine(h, c)          // hash reference
    string  → hashCombine(h, hashString(c))
    bigint  → hashCombine(h, hashBigInt(c))
  return h
```

**Collision risk:** 32-bit birthday paradox threshold is ~77k entries. Acceptable for proof search (typically <10k terms). No collision detection — a collision would silently corrupt terms.

**File:** `lib/hash.js`

### Upgrade Path

For persistence or large-scale use, switch to 64-bit or 128-bit hash (e.g., xxHash128). The Store API doesn't change — only `computeHash` internals. See `lib/hash-alternatives.js` for xxHash128 prototype.

---

## 3. Store API

**File:** `lib/kernel/store.js`

| Operation | Signature | Complexity | Notes |
|-----------|-----------|------------|-------|
| `put(tag, children)` | → hash | O(k) | k = children count. Deduplicates: returns existing hash if node exists |
| `get(hash)` | → node \| undefined | O(1) | Map lookup |
| `tag(hash)` | → string \| undefined | O(1) | `get(hash)?.tag` |
| `children(hash)` | → array | O(1) | `get(hash)?.children` |
| `child(hash, i)` | → child \| undefined | O(1) | Index into children |
| `eq(a, b)` | → boolean | O(1) | `a === b` — the core insight |
| `isTerm(v)` | → boolean | O(1) | Is this hash in the Store? |
| `isTermChild(c)` | → boolean | O(1) | Is this child a hash reference (number)? |
| `clear()` | — | O(n) | Testing only |
| `size()` | → number | O(1) | Map.size |

### Key Invariant

**Content-addressing guarantee:** If `put(tag1, c1) === put(tag2, c2)`, then `tag1 === tag2` and `c1` deeply equals `c2` (modulo hash collisions).

**Consequence:** Equality of arbitrarily deep terms is always O(1).

---

## 4. Substitution

**File:** `lib/kernel/substitute.js`

### Core Operations

| Operation | Signature | Complexity | Notes |
|-----------|-----------|------------|-------|
| `eq(a, b)` | → boolean | O(1) | `a === b` |
| `copy(h)` | → h | O(1) | Identity — terms are immutable |
| `sub(h, v, val)` | → hash | O(m) | Single variable substitution, m = term size |
| `apply(h, theta)` | → hash | O(n + m) | Simultaneous substitution (default) |
| `applySimultaneous(h, theta, memo?)` | → hash | O(n + m) | n = \|theta\|, m = term size. Single traversal |
| `applySequential(h, theta)` | → hash | O(n × m) | Legacy. Applies bindings one-by-one |
| `occurs(v, h)` | → boolean | O(m) | Occurs check for unification |

### Simultaneous Substitution (the key optimization)

The default `apply` uses `applySimultaneous`:

1. Build a `Map` from theta: O(n)
2. Single depth-first traversal of term: O(m)
3. At each node, check Map for variable match: O(1)
4. If children change, `put` new node: O(k)

**Requires:** theta is idempotent (no variable references other bound variables). This is guaranteed by the unifier producing MGU.

**vs Sequential:** Sequential applies each binding one at a time, traversing the entire term for each binding → O(n × m). With 12 bindings: 251 Store.get calls vs 4 (63x fewer).

### Structural Sharing

Substitution preserves sharing. If a subtree has no substitution targets, its hash is returned unchanged — no new nodes allocated. Only the path from root to the substituted variable creates new nodes.

---

## 5. Unification

**File:** `lib/kernel/unify.js`

### Variable Convention

| Kind | Tag | Name convention | Role |
|------|-----|-----------------|------|
| Metavar | `freevar` | starts with `_` (e.g., `_X`, `_V42`) | Unification variable — can be bound |
| Freevar | `freevar` | no `_` prefix (e.g., `A`, `x`) | Object-level variable — must match exactly |

### Algorithms

**Union-Find Unification** (default, `unify`):

| Step | Complexity |
|------|------------|
| Build goal list | O(1) |
| Process each goal | O(α(n)) per find |
| Decompose nodes | O(k) per node |
| Occurs check | O(m) per binding |
| Convert to theta | O(|bindings|) |
| **Total** | O(K × m) where K = bindings, m = max term size |

The `UnionFind` class provides:
- `find(v)` — path-compressed root lookup: O(α(n)) amortized
- `union(v, term)` — bind variable to term: O(α(n))
- `toTheta()` — convert to substitution list: O(K)

**Idempotent MGU** (legacy, `unifyIdempotent`):
- Maintains idempotent substitution eagerly: O(K² × m)
- Still available for testing/comparison

**One-way Matching** (`match`):
- Pattern variables bind, term is ground
- No occurs check needed
- O(m) where m = pattern size

### Ephemeral Expansion

Compact primitives (`binlit`, `strlit`) can be pattern-matched against their structural equivalents without materializing the full tree:

```
binlit(10n)  vs  (o X)    → X = binlit(5n)     // even: divide by 2
binlit(7n)   vs  (i X)    → X = binlit(3n)     // odd: (n-1)/2
binlit(0n)   vs  e        → success             // zero
strlit("hi") vs  cons(H,T) → H = charlit('h'), T = strlit("i")
strlit("")   vs  nil       → success
```

This avoids expanding a 256-bit binary number into ~256 cons cells. The expanded terms are created lazily during unification and interned in the Store.

---

## 6. AST Utilities

**File:** `lib/kernel/ast.js`

| Operation | Complexity | Notes |
|-----------|------------|-------|
| `freeVars(h)` | O(m) | Collect all freevar names (Set-deduplicated) |
| `isAtomic(h)` | O(1) | tag is `atom` or `freevar` |
| `connective(h)` | O(1) | Outermost tag |
| `hash(h)` | O(1) | Identity — term IS its hash |
| `mapChildren(h, fn)` | O(k) | Apply fn to term children, put if changed |
| `fold(h, fn, init)` | O(m) | Depth-first fold over entire term |
| `tag(h)` | O(1) | Delegates to Store.tag |
| `children(h)` | O(1) | Delegates to Store.children |

---

## 7. Sequents

**File:** `lib/kernel/sequent.js`

Structure: `{ contexts: { [name]: hash[] }, succedent: hash, _hash: number | null }`

For ILL: `contexts = { linear: [...], cartesian: [...] }`.

| Operation | Complexity | Notes |
|-----------|------------|-------|
| `seq(contexts, succedent)` | O(1) | Constructor |
| `fromArrays(linear, cart, succ)` | O(1) | ILL convenience |
| `copy(s)` | O(c) | c = total context formulas. Shallow — copies arrays, not terms |
| `substitute(s, theta)` | O(c × (n+m)) | Apply theta to every formula |
| `hash(s)` | O(c log c) | Sort + combine. Cached in `_hash` |
| `eq(a, b)` | O(c log c) | First call; O(1) if cached |
| `freeVars(s)` | O(c × m) | Walk all formulas |
| `renameVars(s)` | O(c × m) | Fresh variable names via global counter |
| `addToContext(s, name, h)` | O(c) | Returns new sequent |
| `removeAtIndex(s, name, i)` | O(c) | Returns new sequent |

### Note: Dual Representation

The focused prover (L3) maintains contexts BOTH as `seq.contexts.linear` (array) AND as `delta` (multiset `{ hash: count }`). This is redundant — profiling shows ~25% overhead in conversion. See [[../research/prover-optimization]] §1.

---

## 8. Multiset Contexts

**File:** `lib/prover/context.js`

Used by the focused prover (L3) as the working representation for linear resources.

Structure: `{ [hash: number]: count: number }`

| Operation | Complexity | Notes |
|-----------|------------|-------|
| `empty()` | O(1) | `{}` |
| `fromArray(arr)` | O(n) | Count occurrences |
| `toArray(ms)` | O(n) | Expand counts |
| `add(ms, h)` | O(d) | d = distinct formulas (object spread) |
| `remove(ms, h)` | O(d) | Returns null if insufficient |
| `has(ms, h)` | O(1) | Check existence |
| `getCount(ms, h)` | O(1) | How many copies |
| `copy(ms)` | O(d) | Object spread |
| `merge(ms1, ms2)` | O(d₂) | Add counts |
| `subtract(ms1, ms2)` | O(d₂) | Remove counts, null if insufficient |
| `contains(ms1, ms2)` | O(d₂) | ms2 ⊆ ms1 |
| `eq(ms1, ms2)` | O(d) | Compare all counts |
| `substitute(ms, theta)` | O(d × (n+m)) | Apply theta, rebuild (hashes may merge) |
| `find(ms, pred)` | O(d) | First match |
| `filter(ms, pred)` | O(d) | All matches |

**Key property:** Because formulas are content-addressed, identical formulas automatically collapse to the same hash key. No deep comparison needed for multiset operations.

---

## 9. Properties & Invariants

### What Content-Addressing Gives Us

1. **O(1) equality** — `a === b` for arbitrarily deep terms
2. **O(1) copy** — `copy = h => h`, terms are immutable
3. **Automatic structural sharing** — identical subtrees are stored once
4. **Natural memoization keys** — hashes ARE cache keys
5. **O(1) multiset membership** — `hash in context`

### What It Costs

1. **Global mutable state** — the Store is a singleton `Map`, not garbage collected
2. **Hash computation on creation** — O(k) per put, amortized by deduplication
3. **Indirection** — every structural inspection requires a `Store.get` lookup
4. **No GC** — terms live forever once interned (acceptable for proof search lifetimes)
5. **32-bit collision risk** — no detection, silent corruption at ~77k entries

### Critical Assumptions

- **Idempotent MGU:** `applySimultaneous` assumes theta has no variable-to-variable chains. The union-find unifier guarantees this via `toTheta()`.
- **Immutability:** Nothing in the Store is ever modified after creation. Breaking this would invalidate all cached hashes.
- **Singleton Store:** There is one global Store. All terms across all proof searches share it. This enables cross-proof sharing but prevents independent garbage collection.

---

## 10. File Summary

```
lib/kernel/
  store.js        — Store: put, get, tag, children, eq
  substitute.js   — sub, apply (simultaneous), occurs
  unify.js        — unify (union-find), match, ephemeral expansion
  ast.js          — freeVars, mapChildren, fold, isAtomic
  ast-hash.js     — hashAST (identity function, backwards compat)
  sequent.js      — sequent construction, hashing, operations

lib/hash.js       — FNV-1a: hashString, hashCombine, hashBigInt

lib/prover/
  context.js      — multiset operations on { hash: count }
```

---

## 11. Improvements & Research Topics

### Collision Mitigation (MEDIUM priority)
32-bit FNV-1a has birthday-paradox collisions at ~77k entries. Two options:
- **Detection:** On `put`, if hash exists, verify `tag === existing.tag && children deepEquals existing.children`. Cost: O(k) per put.
- **Wider hash:** 64-bit or 128-bit hash (xxHash, rapidhash). Cost: needs BigInt or two-number representation for hash values. See `lib/hash-alternatives.js`.

### Scoped Store / Arena Allocation (LOW priority, MEDIUM for Zig port)
Each proof branch gets its own scope. On backtrack, discard entire scope in O(1). Currently, failed branches leave garbage in the global Store. Would require `ScopedStore` with parent chain for lookups. See [[../research/prover-optimization]] §4.

### Eliminate Dual Representation (MEDIUM priority)
The focused prover (L3) converts between `seq.contexts.linear` (array) and `delta` (multiset) constantly. Use multiset as single source of truth. ~25% runtime reduction expected. See [[../research/prover-optimization]] §1.

### Constructor Indexing for Identity (HIGH priority)
`tryIdentity` in `lib/prover/generic.js` does a linear scan over context formulas. Index by `Store.tag(h)` for O(1) ground identity and filtered unification. See [[../dev/constructor-indexing]].

### Substitution Memoization in Substitution
`applySimultaneous` with `memoize=true` caches intermediate results during a single traversal. Currently disabled by default (`apply` passes `false`). For terms with heavy sharing (e.g., deeply nested tensors with repeated subformulas), memoization avoids redundant traversals. Cost: Map allocation per `apply` call.

### Weak References for GC
Replace `STORE = new Map()` with a `WeakRef`-based structure to allow garbage collection of unreachable terms. Challenges: hashes are numbers (can't be WeakRef keys), would need `FinalizationRegistry` with indirection.

### Persistent Store for Incremental Proofs
Serialize Store to disk (hash → node mapping is naturally serializable). On reload, resume proof search without re-parsing. The content-addressed nature means serialization is trivial — just dump the Map.

---

## References

- Goto, S. (1974). "Monocopy and Associative Algorithms in Extended Lisp." — Original hash consing
- Filliâtre, J-C. & Conchon, S. (2006). "Type-Safe Modular Hash-Consing." — Modern hash consing in ML
- Fowler, Noll, Vo. "FNV Hash." — The hash algorithm used
- [[../research/content-addressed-formulas]] — Design rationale and migration from AST objects
- [[../research/backward-prover-optimization]] — Substitution/unification benchmarks
- [[../research/prover-optimization]] — Full optimization catalog
