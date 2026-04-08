/**
 * Store Binary Serialization/Deserialization
 *
 * Binary format for fast Store snapshot restore.
 * Layout (little-endian):
 *
 *   Header (20 bytes):
 *     magic      u32   0x43414C43 ("CALC")
 *     version    u16   1
 *     endian     u8    1 = LE
 *     reserved   u8    0
 *     nodeCount  u32   number of Store entries (excluding sentinel)
 *     strCount   u32   number of interned strings
 *     bigCount   u32   number of bigints
 *
 *   SoA arrays (nodeCount entries each, offset starts at sentinel+1):
 *     tags       u8[]
 *     arities    u8[]
 *     <pad to 4-byte alignment>
 *     child0     u32[]
 *     child1     u32[]
 *     child2     u32[]
 *     child3     u32[]
 *     child4     u32[]
 *
 *   DEDUP table (nodeCount entries):
 *     hashes     u32[]   content hash for each node (index 1..nodeCount)
 *
 *   String table:
 *     for each string: u16 length + utf8 bytes
 *
 *   BigInt table:
 *     for each bigint: u8 sign + u16 byteLen + bytes (little-endian)
 *
 *   Tag registry:
 *     tagCount   u16
 *     for each tag: u16 nameLen + utf8 name
 *
 *   SDK metadata (JSON):
 *     metaLen    u32
 *     utf8 JSON bytes
 *
 *   Footer:
 *     checksum   u32   CRC32 of everything before footer
 */

const { hashString, hashCombine2, hashBigInt } = require('../hash');

const MAGIC = 0x43414C43; // "CALC"
const VERSION = 4; // v4: named_arg pre-registered (PRED_BOUNDARY shift)

// CRC32 (IEEE 802.3)
const crcTable = new Uint32Array(256);
for (let i = 0; i < 256; i++) {
  let c = i;
  for (let j = 0; j < 8; j++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1;
  crcTable[i] = c;
}

function crc32(buf) {
  let crc = 0xFFFFFFFF;
  for (let i = 0; i < buf.length; i++) {
    crc = crcTable[(crc ^ buf[i]) & 0xFF] ^ (crc >>> 8);
  }
  return (crc ^ 0xFFFFFFFF) >>> 0;
}

/**
 * Serialize a Store snapshot to binary Buffer.
 * @param {Object} snapshot - from Store.snapshot()
 * @returns {Buffer}
 */
function serialize(snapshot) {
  const { nodeCount, tags, arities, child0, child1, child2, child3, child4,
          dedupHashes, strings, bigints, arrays, tagNames, metadata } = snapshot;

  // Pre-encode variable-length sections
  const stringBuffers = strings.map(s => Buffer.from(s, 'utf8'));
  const bigintBuffers = bigints.map(n => {
    const abs = n < 0n ? -n : n;
    const hex = abs.toString(16);
    const byteLen = Math.ceil(hex.length / 2);
    const buf = Buffer.alloc(byteLen);
    for (let i = 0; i < byteLen; i++) {
      const off = hex.length - 2 * (i + 1);
      buf[i] = parseInt(off < 0 ? hex.slice(0, off + 2) : hex.slice(off, off + 2), 16);
    }
    return { sign: n < 0n ? 1 : 0, buf };
  });
  const tagNameBuffers = tagNames.map(n => Buffer.from(n, 'utf8'));
  const metaJson = Buffer.from(JSON.stringify(metadata || {}), 'utf8');

  // Calculate total size
  const soaPad = (2 * nodeCount) % 4 === 0 ? 0 : 4 - (2 * nodeCount) % 4;
  let totalSize = 20; // header
  totalSize += nodeCount; // tags
  totalSize += nodeCount; // arities
  totalSize += soaPad;    // alignment
  totalSize += 4 * nodeCount * 5; // child0-4
  totalSize += 4 * nodeCount; // dedup hashes

  // String table
  for (const sb of stringBuffers) totalSize += 2 + sb.length;
  // BigInt table
  for (const { buf } of bigintBuffers) totalSize += 1 + 2 + buf.length;
  // Array table: arrayCount:u32, for each: length:u32 + data:u32[length]
  const snapArrays = arrays || [];
  totalSize += 4; // arrayCount
  for (const entry of snapArrays) totalSize += 4 + 4 * entry.data.length;
  // Tag registry
  totalSize += 2; // tagCount
  for (const tb of tagNameBuffers) totalSize += 2 + tb.length;
  // Metadata
  totalSize += 4 + metaJson.length;
  // Footer
  totalSize += 4; // CRC32

  const buffer = Buffer.alloc(totalSize);
  let pos = 0;

  // Header
  buffer.writeUInt32LE(MAGIC, pos); pos += 4;
  buffer.writeUInt16LE(VERSION, pos); pos += 2;
  buffer[pos++] = 1; // LE
  buffer[pos++] = 0; // reserved
  buffer.writeUInt32LE(nodeCount, pos); pos += 4;
  buffer.writeUInt32LE(strings.length, pos); pos += 4;
  buffer.writeUInt32LE(bigints.length, pos); pos += 4;

  // SoA arrays (slices from index 0..nodeCount, representing Store IDs 1..nodeCount)
  buffer.set(tags, pos); pos += nodeCount;
  buffer.set(arities, pos); pos += nodeCount;
  pos += soaPad; // alignment padding

  const c0view = new Uint8Array(child0.buffer, child0.byteOffset, child0.byteLength);
  const c1view = new Uint8Array(child1.buffer, child1.byteOffset, child1.byteLength);
  const c2view = new Uint8Array(child2.buffer, child2.byteOffset, child2.byteLength);
  const c3view = new Uint8Array(child3.buffer, child3.byteOffset, child3.byteLength);
  const c4view = child4 ? new Uint8Array(child4.buffer, child4.byteOffset, child4.byteLength) : new Uint8Array(4 * nodeCount);
  buffer.set(c0view, pos); pos += c0view.length;
  buffer.set(c1view, pos); pos += c1view.length;
  buffer.set(c2view, pos); pos += c2view.length;
  buffer.set(c3view, pos); pos += c3view.length;
  buffer.set(c4view, pos); pos += c4view.length;

  // DEDUP hashes
  const dedupView = new Uint8Array(dedupHashes.buffer, dedupHashes.byteOffset, dedupHashes.byteLength);
  buffer.set(dedupView, pos); pos += dedupView.length;

  // String table
  for (const sb of stringBuffers) {
    buffer.writeUInt16LE(sb.length, pos); pos += 2;
    sb.copy(buffer, pos); pos += sb.length;
  }

  // BigInt table
  for (const { sign, buf } of bigintBuffers) {
    buffer[pos++] = sign;
    buffer.writeUInt16LE(buf.length, pos); pos += 2;
    buf.copy(buffer, pos); pos += buf.length;
  }

  // Array table
  buffer.writeUInt32LE(snapArrays.length, pos); pos += 4;
  for (const entry of snapArrays) {
    const data = entry.data instanceof Uint32Array ? entry.data : new Uint32Array(entry.data);
    buffer.writeUInt32LE(data.length, pos); pos += 4;
    const view = new Uint8Array(data.buffer, data.byteOffset, data.byteLength);
    buffer.set(view, pos); pos += view.length;
  }

  // Tag registry
  buffer.writeUInt16LE(tagNames.length, pos); pos += 2;
  for (const tb of tagNameBuffers) {
    buffer.writeUInt16LE(tb.length, pos); pos += 2;
    tb.copy(buffer, pos); pos += tb.length;
  }

  // Metadata
  buffer.writeUInt32LE(metaJson.length, pos); pos += 4;
  metaJson.copy(buffer, pos); pos += metaJson.length;

  // CRC32 footer
  const checksum = crc32(buffer.subarray(0, pos));
  buffer.writeUInt32LE(checksum, pos); pos += 4;

  return buffer;
}

/**
 * Deserialize binary buffer back to snapshot data.
 * @param {Buffer} buffer
 * @returns {Object} snapshot-compatible object
 */
function deserialize(buffer) {
  let pos = 0;

  // Header
  const magic = buffer.readUInt32LE(pos); pos += 4;
  if (magic !== MAGIC) throw new Error(`Invalid magic: 0x${magic.toString(16)} (expected 0x${MAGIC.toString(16)})`);
  const version = buffer.readUInt16LE(pos); pos += 2;
  if (version !== VERSION) throw new Error(`Unsupported version: ${version} (expected ${VERSION})`);
  const endian = buffer[pos++];
  if (endian !== 1) throw new Error('Only little-endian supported');
  pos++; // reserved
  const nodeCount = buffer.readUInt32LE(pos); pos += 4;
  const strCount = buffer.readUInt32LE(pos); pos += 4;
  const bigCount = buffer.readUInt32LE(pos); pos += 4;

  // Verify CRC32
  const storedCrc = buffer.readUInt32LE(buffer.length - 4);
  const computedCrc = crc32(buffer.subarray(0, buffer.length - 4));
  if (storedCrc !== computedCrc) {
    throw new Error(`CRC32 mismatch: stored=0x${storedCrc.toString(16)} computed=0x${computedCrc.toString(16)}`);
  }

  // SoA arrays (all independent copies — buffer can be GC'd)
  const soaPad = (2 * nodeCount) % 4 === 0 ? 0 : 4 - (2 * nodeCount) % 4;
  const tags = new Uint8Array(buffer.subarray(pos, pos + nodeCount)); pos += nodeCount;
  const arities = new Uint8Array(buffer.subarray(pos, pos + nodeCount)); pos += nodeCount;
  pos += soaPad;

  const child0 = new Uint32Array(buffer.buffer.slice(buffer.byteOffset + pos, buffer.byteOffset + pos + 4 * nodeCount)); pos += 4 * nodeCount;
  const child1 = new Uint32Array(buffer.buffer.slice(buffer.byteOffset + pos, buffer.byteOffset + pos + 4 * nodeCount)); pos += 4 * nodeCount;
  const child2 = new Uint32Array(buffer.buffer.slice(buffer.byteOffset + pos, buffer.byteOffset + pos + 4 * nodeCount)); pos += 4 * nodeCount;
  const child3 = new Uint32Array(buffer.buffer.slice(buffer.byteOffset + pos, buffer.byteOffset + pos + 4 * nodeCount)); pos += 4 * nodeCount;
  const child4 = new Uint32Array(buffer.buffer.slice(buffer.byteOffset + pos, buffer.byteOffset + pos + 4 * nodeCount)); pos += 4 * nodeCount;

  // DEDUP hashes
  const dedupHashes = new Uint32Array(buffer.buffer.slice(buffer.byteOffset + pos, buffer.byteOffset + pos + 4 * nodeCount)); pos += 4 * nodeCount;

  // String table
  const strings = [];
  for (let i = 0; i < strCount; i++) {
    const len = buffer.readUInt16LE(pos); pos += 2;
    strings.push(buffer.toString('utf8', pos, pos + len));
    pos += len;
  }

  // BigInt table
  const bigints = [];
  for (let i = 0; i < bigCount; i++) {
    const sign = buffer[pos++];
    const byteLen = buffer.readUInt16LE(pos); pos += 2;
    let val = 0n;
    for (let j = byteLen - 1; j >= 0; j--) {
      val = (val << 8n) | BigInt(buffer[pos + j]);
    }
    pos += byteLen;
    bigints.push(sign ? -val : val);
  }

  // Array table
  const arrayCount = buffer.readUInt32LE(pos); pos += 4;
  const arrays = [];
  for (let i = 0; i < arrayCount; i++) {
    const len = buffer.readUInt32LE(pos); pos += 4;
    const data = new Uint32Array(buffer.buffer.slice(buffer.byteOffset + pos, buffer.byteOffset + pos + 4 * len));
    pos += 4 * len;
    arrays.push({ data });
  }

  // Tag registry
  const tagCount = buffer.readUInt16LE(pos); pos += 2;
  const tagNames = [];
  for (let i = 0; i < tagCount; i++) {
    const len = buffer.readUInt16LE(pos); pos += 2;
    tagNames.push(buffer.toString('utf8', pos, pos + len));
    pos += len;
  }

  // Metadata
  const metaLen = buffer.readUInt32LE(pos); pos += 4;
  const metadata = JSON.parse(buffer.toString('utf8', pos, pos + metaLen));
  pos += metaLen;

  return {
    nodeCount,
    tags, arities,
    child0, child1, child2, child3, child4,
    dedupHashes,
    strings,
    bigints,
    arrays,
    tagNames,
    metadata
  };
}

/**
 * Compact a snapshot by removing unreachable nodes (Store GC).
 * Renumbers all Store IDs contiguously and recomputes dedup hashes.
 * @param {Object} snap - snapshot from Store.snapshot()
 * @returns {Object} compacted snapshot (same format, fewer nodes)
 */
function compactSnapshot(snap) {
  const { nodeCount, tags, arities, child0, child1, child2, child3, child4,
          strings, bigints, arrays, tagNames, metadata } = snap;

  if (nodeCount === 0) return snap;

  // ── Tag classification (which tags have non-ID child0) ──
  const STRING_CHILD = new Set(['atom', 'freevar', 'metavar', 'strlit']);
  const BIGINT_CHILD = new Set(['binlit', 'bound', 'evar']);
  const ARRAY_CHILD = new Set(['arrlit']);

  const nonIdChild0 = new Uint8Array(256); // indexed by tagId
  const strChild0 = new Uint8Array(256);
  const bigChild0 = new Uint8Array(256);
  const arrChild0 = new Uint8Array(256);
  const charlitTag = tagNames.indexOf('charlit');
  for (let i = 0; i < tagNames.length; i++) {
    if (STRING_CHILD.has(tagNames[i])) { nonIdChild0[i] = 1; strChild0[i] = 1; }
    if (BIGINT_CHILD.has(tagNames[i])) { nonIdChild0[i] = 1; bigChild0[i] = 1; }
    if (ARRAY_CHILD.has(tagNames[i])) { nonIdChild0[i] = 1; arrChild0[i] = 1; }
    if (i === charlitTag) nonIdChild0[i] = 1;
  }

  // ── 1. Find reachable nodes via DFS from metadata roots ──
  // Snapshot uses 0-based indexing; Store IDs are 1-based (id = index + 1).
  const reachable = new Uint8Array(nodeCount + 1); // 1-based
  const stack = [];

  function mark(id) {
    if (id >= 1 && id <= nodeCount && !reachable[id]) {
      reachable[id] = 1;
      stack.push(id);
    }
  }

  // Walk metadata JSON to find root hashes
  function walkRoots(obj) {
    if (obj == null) return;
    if (typeof obj === 'number') { mark(obj); return; }
    if (Array.isArray(obj)) { for (let i = 0; i < obj.length; i++) walkRoots(obj[i]); return; }
    if (typeof obj === 'object') { for (const v of Object.values(obj)) walkRoots(v); }
  }
  walkRoots(metadata);

  // DFS: expand children of reachable nodes
  while (stack.length > 0) {
    const id = stack.pop();
    const idx = id - 1;
    const tag = tags[idx];
    const ar = arities[idx];
    if (ar >= 1 && !nonIdChild0[tag]) mark(child0[idx]);
    if (ar >= 2) mark(child1[idx]);
    if (ar >= 3) mark(child2[idx]);
    if (ar >= 4) mark(child3[idx]);
    if (ar >= 5) mark(child4[idx]);
    // Walk array elements (arrlit child0 is array table index)
    if (arrChild0[tag] && ar >= 1) {
      const arrIdx = child0[idx];
      if (arrIdx < arrays.length) {
        const arr = arrays[arrIdx];
        if (arr && arr.data) for (let i = 0; i < arr.data.length; i++) mark(arr.data[i]);
      }
    }
  }

  // ── 2. Build renumbering map ──
  const remap = new Uint32Array(nodeCount + 1); // old ID → new ID
  let newCount = 0;
  for (let id = 1; id <= nodeCount; id++) {
    if (reachable[id]) remap[id] = ++newCount;
  }

  if (newCount === nodeCount) return snap; // nothing to compact

  // ── 3. Create compacted SoA arrays ──
  const nTags = new Uint8Array(newCount);
  const nAr = new Uint8Array(newCount);
  const nC0 = new Uint32Array(newCount);
  const nC1 = new Uint32Array(newCount);
  const nC2 = new Uint32Array(newCount);
  const nC3 = new Uint32Array(newCount);
  const nC4 = new Uint32Array(newCount);

  for (let id = 1; id <= nodeCount; id++) {
    if (!reachable[id]) continue;
    const oi = id - 1, ni = remap[id] - 1;
    const tag = tags[oi], ar = arities[oi];
    nTags[ni] = tag;
    nAr[ni] = ar;
    if (ar >= 1) nC0[ni] = nonIdChild0[tag] ? child0[oi] : (remap[child0[oi]] || 0);
    if (ar >= 2) nC1[ni] = remap[child1[oi]] || 0;
    if (ar >= 3) nC2[ni] = remap[child2[oi]] || 0;
    if (ar >= 4) nC3[ni] = remap[child3[oi]] || 0;
    if (ar >= 5) nC4[ni] = remap[child4[oi]] || 0;
  }

  // ── 4. Remap array elements ──
  const newArrays = arrays.map(entry => {
    const d = entry.data;
    const nd = new Uint32Array(d.length);
    for (let i = 0; i < d.length; i++) nd[i] = remap[d[i]] || 0;
    return { data: nd };
  });

  // ── 5. Recompute dedup hashes (content hashes change because child IDs changed) ──
  const nDedup = new Uint32Array(newCount);
  for (let ni = 0; ni < newCount; ni++) {
    const tag = nTags[ni], ar = nAr[ni];
    const tagName = tagNames[tag];
    let h = hashString(tagName);

    if (arrChild0[tag] && ar >= 1) {
      // arrlit: special hash = tag + length + elements
      const arrIdx = nC0[ni];
      const arr = newArrays[arrIdx];
      h = hashCombine2(h, arr.data.length);
      for (let i = 0; i < arr.data.length; i++) h = hashCombine2(h, arr.data[i]);
    } else {
      h = hashCombine2(h, ar);
      for (let ci = 0; ci < ar && ci < 5; ci++) {
        const cv = [nC0, nC1, nC2, nC3, nC4][ci][ni];
        if (ci === 0 && strChild0[tag]) {
          h = hashCombine2(h, hashString(strings[cv]));
        } else if (ci === 0 && bigChild0[tag]) {
          h = hashCombine2(h, hashBigInt(bigints[cv]));
        } else {
          h = hashCombine2(h, cv);
        }
      }
    }
    nDedup[ni] = h;
  }

  // ── 6. Remap all Store hashes in metadata ──
  function remapMeta(obj) {
    if (obj == null) return obj;
    if (typeof obj === 'number') return remap[obj] || obj;
    if (typeof obj === 'string' || typeof obj === 'boolean') return obj;
    if (Array.isArray(obj)) return obj.map(remapMeta);
    const out = {};
    for (const [k, v] of Object.entries(obj)) out[k] = remapMeta(v);
    return out;
  }

  return {
    nodeCount: newCount,
    tags: nTags, arities: nAr,
    child0: nC0, child1: nC1, child2: nC2, child3: nC3, child4: nC4,
    dedupHashes: nDedup,
    strings,   // keep as-is (referenced by table index, unchanged)
    bigints,   // keep as-is
    arrays: newArrays,
    tagNames,
    metadata: remapMeta(metadata),
  };
}

module.exports = { serialize, deserialize, compactSnapshot, crc32 };
