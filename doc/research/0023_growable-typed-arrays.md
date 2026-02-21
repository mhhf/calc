---
title: "Growable TypedArrays in JavaScript"
created: 2026-02-21
modified: 2026-02-21
summary: "Techniques for dynamically growable TypedArrays in JavaScript: ArrayBuffer.resize(), transfer(), demand paging, ECS patterns, and memory analysis."
tags: [TypedArrays, JavaScript, memory-management, buffers, performance]
category: "Performance"
---

# Growable TypedArrays in JavaScript

## 1. `ArrayBuffer.prototype.resize()`

**Spec:** ECMAScript 2024 (TC39 proposal-resizablearraybuffer)

```js
const buf = new ArrayBuffer(8, { maxByteLength: 1024 });
buf.resizable;     // true
buf.maxByteLength; // 1024
buf.resize(64);    // in-place, zero-filled, no copy
```

TypedArray views on resizable buffers auto-track length:
```js
const view = new Uint32Array(buf); // length-tracking
buf.resize(128);
view.length; // 32 (128/4)
```

**Browser support (Baseline July 2024):**
| Engine | Version | Date |
|--------|---------|------|
| Chrome | 111 | 2023-03-07 |
| Edge | 111 | 2023-03-13 |
| Safari | 16.4 | 2023-03-27 |
| Firefox | 128 | 2024-07-09 |
| Node.js | 20 (V8 11.3) | 2023-04-18 |
| Deno | 1.33 | ~2023-05 |

Constraint: must declare `maxByteLength` upfront. The resize cannot exceed it.

## 2. `ArrayBuffer.prototype.transfer()`

**Spec:** ECMAScript 2024 (TC39 proposal-arraybuffer-transfer)

```js
const buf = new ArrayBuffer(8);
const buf2 = buf.transfer(16); // zero-copy when possible (realloc)
buf.detached; // true
buf2.byteLength; // 16
```

**Browser support (Baseline March 2024):**
| Engine | Version | Date |
|--------|---------|------|
| Chrome | 114 | 2023-05-30 |
| Firefox | 122 | 2024-01-23 |
| Safari | 17.4 | 2024-03-05 |
| Node.js | 21 (V8 11.8) | 2023-10-17 |

Preserves resizability. Implementations may use zero-copy move or `realloc`.

## 3. ECS Library Strategies

**BitECS:** Fixed preallocation. Default 100K entities, configurable via `setDefaultSize()`. Each component is a SoA of TypedArrays sized to max entities. Never grows. Relies on OS demand paging to avoid physical memory cost. Simple, no resize logic, but wastes virtual address space.

**Javelin ECS:** SoA TypedArrays with doubling reallocation. When capacity exceeded, allocates 2x TypedArray and copies via `.set()`. More memory-efficient but has copy pauses.

**General pattern:** High-performance JS ECS libraries prefer fixed preallocation over dynamic growth, because resize introduces branch overhead on every write and potential GC pauses from copy-based growth.

## 4. OS Demand Paging (Linux)

**Yes, the OS lazily allocates.** Measured on Linux 6.17.9, Node.js v22.22.0:

```
new Uint32Array(16_000_000) — 64MB allocation:
  RSS delta (no touch):  0.13 MB   ← almost nothing
  RSS delta (all pages): 63.25 MB  ← full cost on touch

new Uint32Array(64_000_000) — 256MB allocation:
  RSS delta (no touch):  0.40 MB
  RSS delta (first 1MB): 9.25 MB
  RSS delta (all pages): 252.75 MB
```

V8 allocates ArrayBuffer backing stores via `mmap(MAP_ANONYMOUS)`. Linux uses:
- **Demand paging:** virtual pages map to the shared zero page until first write
- **Copy-on-write:** first write triggers page fault, kernel allocates physical 4KB page
- **Overcommit:** virtual memory far exceeds physical; OOM killer intervenes if truly exhausted

Resizable ArrayBuffer with large `maxByteLength` also lazy:
```
new ArrayBuffer(4, { maxByteLength: 256MB }):
  RSS delta: 0.13 MB   ← reserves virtual address space only
  After resize(1MB): +2.13 MB RSS
  After writing 1MB: +7.63 MB RSS
```

**Conclusion:** `new Uint32Array(16_000_000)` does NOT consume 64MB of RAM. It consumes ~0.1MB until touched. Safe to over-allocate on Linux.

## 5. TypedArray `.set()` Copy Performance

Measured on this machine (Node.js v22.22.0):

| Elements | Time/copy | Throughput | ns/elem |
|----------|-----------|------------|---------|
| 1K | <1us | 37 GB/s | 0.10 |
| 10K | 1us | 28 GB/s | 0.14 |
| 100K | 10us | 40 GB/s | 0.10 |
| 1M | 323us | 12 GB/s | 0.32 |
| 10M | 3.8ms | 10 GB/s | 0.38 |

V8 compiles `.set()` to `memcpy`. For doubling strategy, total copy cost across all doublings is O(n) — each element copied ~2x on average. A 1M-element grow-from-1 benchmark:

| Strategy | Median |
|----------|--------|
| Preallocated | 2.14ms |
| Resizable | 3.48ms |
| Transfer | 4.55ms |
| DoublingCopy | 4.51ms |

Resizable is ~1.6x slower than preallocated (branch + potential TLB overhead), but ~1.3x faster than doubling copy.

## 6. Concrete Growable Uint32Array

```js
class GrowableUint32Array {
  constructor(initialCapacity = 64) {
    this._arr = new Uint32Array(initialCapacity);
    this._len = 0;
  }

  get length() { return this._len; }
  get capacity() { return this._arr.length; }

  push(value) {
    if (this._len >= this._arr.length) this._grow();
    this._arr[this._len++] = value;
  }

  get(i) { return this._arr[i]; }
  set(i, v) { this._arr[i] = v; }

  _grow() {
    const newArr = new Uint32Array(this._arr.length * 2);
    newArr.set(this._arr);
    this._arr = newArr;
  }

  // Return a trimmed view (no copy, shares buffer)
  view() {
    return this._arr.subarray(0, this._len);
  }

  // Return a trimmed copy
  toArray() {
    return this._arr.slice(0, this._len);
  }
}
```

### Resizable-buffer variant (Node 20+, all modern browsers):

```js
class GrowableUint32Array {
  constructor(initialCapacity = 64, maxCapacity = 1 << 24) {
    this._buf = new ArrayBuffer(
      initialCapacity * 4,
      { maxByteLength: maxCapacity * 4 }
    );
    this._arr = new Uint32Array(this._buf); // length-tracking
    this._len = 0;
  }

  get length() { return this._len; }
  get capacity() { return this._arr.length; }

  push(value) {
    if (this._len >= this._arr.length) this._grow();
    this._arr[this._len++] = value;
  }

  get(i) { return this._arr[i]; }
  set(i, v) { this._arr[i] = v; }

  _grow() {
    const newSize = Math.min(
      this._buf.byteLength * 2,
      this._buf.maxByteLength
    );
    if (newSize <= this._buf.byteLength) {
      throw new RangeError('GrowableUint32Array exceeded maxCapacity');
    }
    this._buf.resize(newSize);
    // this._arr.length auto-updates (length-tracking view)
  }

  view() {
    return this._arr.subarray(0, this._len);
  }
}
```

### Overallocation variant (BitECS style, simplest):

```js
// Relies on OS demand paging — no physical RAM until touched
const MAX = 1 << 20; // 1M entities
const store = {
  x: new Float32Array(MAX),
  y: new Float32Array(MAX),
  health: new Uint16Array(MAX),
};
let count = 0;

function addEntity(x, y, hp) {
  const eid = count++;
  store.x[eid] = x;
  store.y[eid] = y;
  store.health[eid] = hp;
  return eid;
}
// Virtual: 10MB. Physical (RSS) with 1K entities: ~12KB
```

## Summary

| Approach | Pros | Cons |
|----------|------|------|
| **Preallocate max** | Fastest iteration, no resize logic, OS demand pages | Must know max, wastes virtual address space |
| **Resizable ArrayBuffer** | No copies, in-place growth, auto-tracking views | Must declare maxByteLength upfront, ~12% slower iteration vs fixed |
| **transfer()** | No max needed, zero-copy possible | Invalidates old views, must reassign all references |
| **Doubling + .set()** | Works everywhere, no max needed | GC pressure from old arrays, copy pauses at large sizes |

For CALC's content-addressed store: preallocate-max is likely best. Typical formula counts are bounded, and OS demand paging means the cost is near-zero until used.
