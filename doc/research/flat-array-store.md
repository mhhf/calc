# Flat-Array Term Store in JavaScript

Research into replacing `Map<hash, {tag, children}>` with flat-array storage for O(1) indexed access.

## Benchmark Results (measured on this machine)

```
Store access micro-benchmark (2000 terms, 1M lookups)

Map.get + .tag                     25-44 ns/op    1.0x  (baseline)
Map→index + TypedArray[i]          22-24 ns/op    1.1x  (Map still dominates)
Map→index + packed arena           22-25 ns/op    1.0x  (same — Map is bottleneck)
Open-addr hash + packed arena       8-10 ns/op    3-5x
TypedArray[i] direct                3-5  ns/op    7-12x
Sequential index + packed arena     3-5  ns/op    7-12x
```

**Key finding**: `Map.get()` costs ~25ns. TypedArray indexed access costs ~4ns. The Map lookup is the bottleneck, not the object/array storage format. Replacing `{tag, children}` with TypedArrays while keeping `Map.get()` gains nothing.

---

## Option 1: Sequential Index Arena (best fit, 7-12x faster reads)

Replace hash-as-identity with sequential-index-as-identity. `put()` returns a monotonic integer instead of a content-hash.

### Layout

```javascript
// Tag enum
const TAG = { atom: 0, freevar: 1, tensor: 2, loli: 3, with: 4, bang: 5,
              one: 6, type: 7, arrow: 8, monad: 9, app: 10, binlit: 11,
              strlit: 12, charlit: 13, var: 14, any: 15, hyp: 16,
              comma: 17, empty: 18, seq: 19, deriv: 20 };
const TAG_NAMES = Object.keys(TAG); // reverse lookup

// Struct-of-Arrays layout (SoA)
const MAX_TERMS = 8192;
const tags   = new Uint8Array(MAX_TERMS);       // tag enum
const arity  = new Uint8Array(MAX_TERMS);        // 0-4
const child0 = new Uint32Array(MAX_TERMS);       // first child (term index or string table index)
const child1 = new Uint32Array(MAX_TERMS);       // second child
const child2 = new Uint32Array(MAX_TERMS);       // third child (rare)
const child3 = new Uint32Array(MAX_TERMS);       // fourth child (very rare)
// For mixed-type children: 1 bit per child indicating "is string ref"
const childTypes = new Uint8Array(MAX_TERMS);    // bitmask: bit i = child[i] is string ref

let nextId = 0;

// String interning table
const STRING_TO_ID = new Map();  // string → index
const ID_TO_STRING = [];         // index → string
let nextStringId = 0;

function internString(s) {
  let id = STRING_TO_ID.get(s);
  if (id === undefined) {
    id = nextStringId++;
    STRING_TO_ID.set(s, id);
    ID_TO_STRING.push(s);
  }
  return id;
}

// Content-address dedup: hash → index (only used during put)
const DEDUP = new Map();

function put(tagName, children) {
  // Compute content hash for dedup (same FNV-1a as current)
  const h = computeHash(tagName, children);
  const existing = DEDUP.get(h);
  if (existing !== undefined) return existing;

  const id = nextId++;
  DEDUP.set(h, id);
  tags[id] = TAG[tagName];
  arity[id] = children.length;

  let typeBits = 0;
  for (let i = 0; i < children.length; i++) {
    const c = children[i];
    let val;
    if (typeof c === 'string') {
      val = internString(c);
      typeBits |= (1 << i);
    } else if (typeof c === 'bigint') {
      // BigInts go to a side table (rare, only binlit)
      val = storeBigInt(c);  // returns index into bigint table
      typeBits |= (2 << (i * 2)); // could use separate bitmask
    } else {
      val = c; // term index
    }
    if (i === 0) child0[id] = val;
    else if (i === 1) child1[id] = val;
    else if (i === 2) child2[id] = val;
    else child3[id] = val;
  }
  childTypes[id] = typeBits;
  return id;
}

function getTag(id) { return tags[id]; }
function getTagName(id) { return TAG_NAMES[tags[id]]; }
function getChild(id, i) {
  if (i === 0) return child0[id];
  if (i === 1) return child1[id];
  if (i === 2) return child2[id];
  return child3[id];
}
function getArity(id) { return arity[id]; }

// Tag comparison: integer === instead of string ===
// Before: if (Store.tag(h) === 'tensor') ...
// After:  if (tags[id] === TAG.tensor) ...
```

### Tradeoffs

- **Reads**: 3-5 ns (pure array index) vs 25-44 ns (Map.get). 7-12x faster.
- **Writes**: slightly slower on `put()` because we still need `Map.get()` for dedup. But `put()` is rare (build phase only).
- **Tag comparison**: integer `===` is faster than string `===` (no length check, no character comparison). With 79 tag comparisons across the codebase, this adds up.
- **Memory**: SoA with Uint32Array uses 4 bytes per child slot vs ~40 bytes per JS object property. For 2000 terms: ~48KB flat vs ~160KB objects+Map overhead.
- **Breaking change**: Term identities change from hashes to sequential indices. Every `Store.get(hash)` becomes `tags[id]`, `child0[id]`, etc.

### Complication: BigInts

`binlit` children are BigInts. Cannot store in Uint32Array. Options:
1. **Side table**: `BIGINT_TABLE = []`, store index in child0. Cost: one extra array lookup for binlit terms only.
2. **DataView with Float64**: fits 53-bit integers. EVM values exceed this (256-bit), so side table is necessary.
3. **BigUint64Array**: exists in modern JS, but still limited to 64 bits.

Side table is the pragmatic choice. BigInts are only used in `binlit` nodes (one child), and the count is small.

### Complication: Equality

Current system: `a === b` compares hashes (O(1)). With sequential indices, identity is the index itself: `a === b` still works, because content-addressing ensures the same content gets the same index (via the DEDUP map).

---

## Option 2: Open-Addressing Hash Table (3-5x faster, keeps hash identity)

Keep hash-as-identity but replace `Map` with a custom open-addressing hash table in TypedArrays.

```javascript
// Open-addressing table: hash → arena index
const TABLE_SIZE = 4096; // power of 2, load factor < 0.5
const MASK = TABLE_SIZE - 1;
const htKeys = new Uint32Array(TABLE_SIZE).fill(0xFFFFFFFF); // sentinel = empty
const htVals = new Uint32Array(TABLE_SIZE); // arena index

function htInsert(hash, arenaIdx) {
  let slot = hash & MASK;
  while (htKeys[slot] !== 0xFFFFFFFF) {
    if (htKeys[slot] === hash) return; // already exists
    slot = (slot + 1) & MASK;
  }
  htKeys[slot] = hash;
  htVals[slot] = arenaIdx;
}

function htLookup(hash) {
  let slot = hash & MASK;
  while (htKeys[slot] !== hash) {
    if (htKeys[slot] === 0xFFFFFFFF) return -1; // not found
    slot = (slot + 1) & MASK;
  }
  return htVals[slot];
}

// Arena (same SoA as Option 1)
const tags   = new Uint8Array(MAX_TERMS);
const child0 = new Uint32Array(MAX_TERMS);
// ...

function put(tagName, children) {
  const h = computeHash(tagName, children);
  const existing = htLookup(h);
  if (existing !== -1) return h; // return hash as before

  const id = nextId++;
  htInsert(h, id);
  tags[id] = TAG[tagName];
  // ... store children
  return h;
}

function get(h) {
  const idx = htLookup(h);  // ~8-10 ns vs Map's ~25 ns
  return idx === -1 ? undefined : { tag: TAG_NAMES[tags[idx]], children: ... };
}
```

### Tradeoffs

- **Reads**: 8-10 ns. 3-5x faster than Map.get.
- **API compatible**: returns same hashes, same interface.
- **Risk**: linear probing degrades with high load factor. At 2000/4096 = 49% load, average probes ~1.5. At 75% load, ~4 probes. Need resize logic.
- **Sentinel collision**: hash value 0xFFFFFFFF cannot be stored. Use 0 as sentinel and reserve it, or use a separate "occupied" bitmap.
- **Less benefit than Option 1**: still doing a hash lookup on every read.

---

## Option 3: Packed Arena (AoS in single Uint32Array)

Single contiguous buffer, fixed stride per node.

```javascript
// [tag, arity, child0, child1, child2, child3] = 6 uint32 per term
const STRIDE = 6;
const arena = new Uint32Array(MAX_TERMS * STRIDE);

function putAt(id, tagEnum, children) {
  const base = id * STRIDE;
  arena[base]     = tagEnum;
  arena[base + 1] = children.length;
  for (let i = 0; i < children.length; i++) {
    arena[base + 2 + i] = children[i]; // must be uint32
  }
}

function getTag(id)     { return arena[id * STRIDE]; }
function getArity(id)   { return arena[id * STRIDE + 1]; }
function getChild(id,i) { return arena[id * STRIDE + 2 + i]; }
```

### AoS vs SoA in JS

**SoA (separate TypedArrays per field)** is generally better in JS because:
1. V8 optimizes TypedArray access to near-native speed when the array type is monomorphic.
2. Reading only `tags[id]` touches only the tags array, not the children data (better cache utilization when doing tag-only scans).
3. Each array can have the right element size (Uint8 for tags, Uint32 for children).

**AoS (interleaved in one buffer)** is better when you always access all fields of a node together (tag + all children). In practice, many hot paths do `tag check → bail` without touching children, so SoA wins.

The benchmark showed identical performance for AoS and SoA when accessed through Map (both ~24ns), because Map lookup dominates. With direct index access, SoA's cache advantage would emerge in tag-scan patterns.

---

## Tag Encoding

21 tags in `NON_PRED_TAGS` plus dynamically created predicate tags. Encode as Uint8 enum:

```javascript
const TAG = Object.create(null);
const TAG_NAMES = [];
let nextTag = 0;

function registerTag(name) {
  if (TAG[name] !== undefined) return TAG[name];
  const id = nextTag++;
  TAG[name] = id;
  TAG_NAMES[id] = name;
  return id;
}

// Pre-register known tags
['atom','freevar','tensor','loli','with','bang','one','type',
 'arrow','monad','app','binlit','strlit','charlit',
 'var','any','hyp','comma','empty','seq','deriv'].forEach(registerTag);
```

Benefits:
- `tags[id] === TAG.tensor` is integer comparison (~1 ns) vs `node.tag === 'tensor'` is string comparison (~3-5 ns for short strings, but V8 interns short strings so it's often pointer comparison already).
- Tag fits in Uint8 (256 possible tags, currently ~25 used).
- Switch statements on integer tags compile to jump tables in V8.

Honest assessment: V8 already interns short strings, so the speedup from tag encoding alone is modest (~2x on the comparison itself). The real win is avoiding the Map.get + object dereference to reach the tag in the first place.

---

## String Interning

For atom names, variable names. Store string once, reference by uint32 index.

```javascript
const strings = [];       // id → string
const stringMap = new Map(); // string → id

function intern(s) {
  let id = stringMap.get(s);
  if (id === undefined) {
    id = strings.length;
    strings.push(s);
    stringMap.set(s, id);
  }
  return id;
}

function getString(id) { return strings[id]; }
```

This lets all children in TypedArrays be uint32 (either term index or string table index). A bitmask per node indicates which children are string refs vs term refs.

---

## Existing JS Libraries

| Library | Approach | Notes |
|---------|----------|-------|
| [BitECS](https://github.com/NateTheGreatt/bitECS) | SoA TypedArrays per component | Game ECS. Adopted by Phaser 4. Pure SoA, no objects. |
| [generational-arena](https://github.com/richardanaya/generational-arena) | Generational indices, JS arrays | Prevents use-after-free. 64-bit indices for WASM interop. |
| [Javelin ECS](https://javelin.hashnode.dev/ecs-in-js-storage-mechanisms) | Mixed SoA + object columns | Archetype storage with TypedArray columns. |

BitECS is the closest precedent: pure TypedArray SoA for hot data, zero object allocation in the hot path.

---

## Recommendation

**Option 1 (Sequential Index Arena)** with SoA layout is the strongest choice:

1. **7-12x faster reads** on the get path (the hot path). Every `Store.tag()`, `Store.child()`, `Store.children()` call goes from ~30ns to ~4ns.
2. **Content-addressing preserved** via the DEDUP map, which is only consulted during `put()` (cold path).
3. **Tag enum** eliminates 79 string comparisons across the codebase.
4. **String interning** makes all children homogeneous uint32, enabling pure TypedArray storage.
5. **SoA layout** lets tag-only scans (the most common pattern: check tag, bail if wrong) touch only the `tags` array.

The migration path:
- `Store.get(h).tag` becomes `TAG_NAMES[tags[id]]` (or better: `tags[id] === TAG.tensor`)
- `Store.get(h).children[i]` becomes `getChild(id, i)`
- `Store.put('tensor', [a, b])` returns `id` (uint32 index) instead of `hash`
- `a === b` equality still works (same content → same id via dedup)
- BigInts stored in side table, transparent to callers

The main cost is the migration: every call site touching `Store.get()` needs updating. The 82 call sites across 14 files are manageable. The API surface is small (`get`, `tag`, `children`, `child`, `put`).

---

## Sources

- [Flattening ASTs (Adrian Sampson, Cornell)](https://www.cs.cornell.edu/~asampson/blog/flattening.html) — 2.4x speedup from arena-allocated flat AST
- [BitECS](https://github.com/NateTheGreatt/bitECS) — SoA TypedArray ECS for JS
- [generational-arena](https://github.com/richardanaya/generational-arena) — Arena allocator for JS
- [ECS in JS: Storage Mechanisms (Javelin)](https://javelin.hashnode.dev/ecs-in-js-storage-mechanisms) — comparison of storage strategies
- [Fast properties in V8](https://v8.dev/blog/fast-properties) — V8 object representation
- [Object vs Map performance](https://www.zhenghao.io/posts/object-vs-map) — benchmark with integer keys
- [Arena allocators: 50-100x secret](https://medium.com/@ramogh2404/arena-and-memory-pool-allocators-the-50-100x-performance-secret-behind-game-engines-and-browsers-1e491cb40b49) — motivation and patterns
