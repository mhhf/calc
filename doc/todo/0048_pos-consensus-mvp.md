---
title: "Simplified Consensus MVP (PoA / PoS)"
created: 2026-02-24
modified: 2026-03-01
summary: "In-memory consensus MVP for CALC — PoA (~100 LOC) as starting point, PoS (~300 LOC) as stretch goal"
tags: [consensus, pos, poa, learning, prototype]
type: implementation
status: planning
priority: 5
cluster: Verification
depends_on: [THY_0011]
required_by: []
---

# TODO_0048 — Simplified PoS Consensus MVP

## Motivation

THY_0011 maps Ethereum PoS onto CALC's linear-logic primitives. Before building a real consensus layer, we need a minimal in-memory implementation (~300 LOC) that captures the essential PoS lifecycle. This is a **teaching tool** — not production consensus — designed to:

1. Validate the THY_0011 mapping concretely (proofs as transactions, linear resources as state)
2. Provide a runnable playground for experimenting with validator behavior
3. Serve as a test harness for future consensus work

## The Simplified PoS Algorithm

Strip Ethereum PoS to five core mechanisms:

| Mechanism | Ethereum | Simplified version |
|---|---|---|
| **Validator registry** | 32 ETH deposit, activation queue | Fixed stake, immediate activation |
| **Block production** | RANDAO proposer selection | Round-robin by slot |
| **Attestations** | LMD-GHOST head + FFG source/target | Single vote: block hash + `proof_valid` flag |
| **Finality** | Casper FFG justify → finalize | 2/3 supermajority on consecutive checkpoints |
| **Slashing** | Double vote / surround vote detection | Double vote detection only |

## TODO_0048.Component_1 — Validator Registry

```js
// Validator lifecycle: deposit → active → exited/slashed
function createValidator(id, stake) {
  return { id, stake, active: true, slashed: false }
}

function createRegistry(validatorConfigs) {
  const validators = new Map()
  for (const { id, stake } of validatorConfigs) {
    validators.set(id, createValidator(id, stake))
  }
  return {
    validators,
    totalStake() {
      let sum = 0
      for (const v of this.validators.values()) {
        if (v.active && !v.slashed) sum += v.stake
      }
      return sum
    },
    activeSet() {
      return [...this.validators.values()].filter(v => v.active && !v.slashed)
    }
  }
}
```

## TODO_0048.Component_2 — Block Production

```js
// Round-robin proposer selection (replaces RANDAO)
function selectProposer(registry, slot) {
  const active = registry.activeSet()
  return active[slot % active.length]
}

// Block structure (simplified from THY_0011)
function createBlock({ slot, parentHash, proposerId, proofSubmissions }) {
  return {
    slot,
    parentHash,
    proposerId,
    proofSubmissions,   // List<{ proof, consumed, produced }>
    hash: null          // set after creation
  }
}
```

**CALC mapping**: `proofSubmissions` are the transaction type from THY_0011. Each submission contains a proof tree verified by L1 kernel, plus the linear resources it consumes and produces.

## TODO_0048.Component_3 — Attestations

```js
// Attestation: validator's vote on a block
function createAttestation(validatorId, slot, blockHash, proofValid) {
  return { validatorId, slot, blockHash, proofValid }
}

// Collect attestations and check supermajority
function hasSupermajority(attestations, registry) {
  const validVotes = attestations.filter(a => {
    const v = registry.validators.get(a.validatorId)
    return v && v.active && !v.slashed && a.proofValid
  })
  const votedStake = validVotes.reduce((sum, a) => {
    return sum + registry.validators.get(a.validatorId).stake
  }, 0)
  return votedStake * 3 >= registry.totalStake() * 2
}
```

**CALC-specific**: The `proofValid` flag is deterministic — honest validators always agree because L1 kernel verification is pure. A validator attesting `proofValid=true` for a block with invalid proofs is slashable.

## TODO_0048.Component_4 — Finality (Simplified Casper FFG)

```js
// Checkpoint: first slot of each epoch
function checkpointSlot(epoch, slotsPerEpoch) {
  return epoch * slotsPerEpoch
}

// Finality state machine
function createFinalityTracker(slotsPerEpoch = 4) {
  return {
    slotsPerEpoch,
    justified: null,   // { epoch, blockHash }
    finalized: null,   // { epoch, blockHash }
    votes: new Map(),  // epoch → Set<validatorId>

    // Record a checkpoint vote
    addVote(epoch, validatorId) {
      if (!this.votes.has(epoch)) this.votes.set(epoch, new Set())
      this.votes.get(epoch).add(validatorId)
    },

    // Try to advance justification/finalization
    tryAdvance(currentEpoch, registry) {
      const prevEpoch = currentEpoch - 1
      const voters = this.votes.get(prevEpoch)
      if (!voters) return

      const votedStake = [...voters].reduce((sum, id) => {
        const v = registry.validators.get(id)
        return sum + (v && v.active ? v.stake : 0)
      }, 0)

      // Justify if 2/3+ voted
      if (votedStake * 3 >= registry.totalStake() * 2) {
        const wasJustified = this.justified
        this.justified = { epoch: prevEpoch }

        // Finalize if previous epoch was also justified (consecutive)
        if (wasJustified && wasJustified.epoch === prevEpoch - 1) {
          this.finalized = wasJustified
        }
      }
    }
  }
}
```

## TODO_0048.Component_5 — Slashing (Double Vote Detection)

```js
// Track votes per validator per slot to detect doubles
function createSlashingDetector() {
  // validatorId → slot → blockHash
  const voteHistory = new Map()

  return {
    // Returns slashing evidence if double vote, null otherwise
    recordVote(validatorId, slot, blockHash) {
      if (!voteHistory.has(validatorId)) {
        voteHistory.set(validatorId, new Map())
      }
      const history = voteHistory.get(validatorId)

      if (history.has(slot)) {
        const prev = history.get(slot)
        if (prev !== blockHash) {
          return { type: 'double_vote', validatorId, slot,
                   vote1: prev, vote2: blockHash }
        }
      }
      history.set(slot, blockHash)
      return null
    },

    // Apply slashing to registry
    slash(evidence, registry) {
      const v = registry.validators.get(evidence.validatorId)
      if (v) {
        v.slashed = true
        v.active = false
      }
    }
  }
}
```

## TODO_0048.Component_6 — CALC Integration Points

Where CALC APIs plug into the consensus layer:

```
┌──────────────────────────────────────────────────┐
│  Consensus Layer (this TODO)                     │
│                                                  │
│  createBlock()                                   │
│       │                                          │
│       ▼                                          │
│  proofSubmissions ──► verifyTree(proof)    [L1]   │
│       │                  kernel.js                │
│       ▼                                          │
│  state.linear ────► consume/produce hashes       │
│       │                  Store.get/put            │
│       ▼                                          │
│  attestations ────► proofValid = all verified?   │
│       │                                          │
│       ▼                                          │
│  finality ────────► checkpoint + justify/finalize│
└──────────────────────────────────────────────────┘
```

| CALC API | Consensus role |
|---|---|
| `kernel.verifyTree(proof)` | Validate proof submissions in blocks |
| `Store.get(hash)` / `Store.put(term)` | Read/write content-addressed state |
| `state.linear` (Set of hashes) | UTXO-like resource pool — consumed/produced atomically |
| `state.persistent` (Set of hashes) | Reusable knowledge (rules under `!`) |
| `forward.run(state, rules)` | Off-chain: provers search for proofs to submit |

## TODO_0048.Scenario_1 — Full Lifecycle Walkthrough

**Setup**: 3 validators (Alice, Bob, Carol), each staking 100. Epoch = 4 slots.

```
Slot 0 (proposer: Alice)
  - Alice creates block B0 with proof P1: consumes resource R1, produces R2
  - All 3 validators verify P1 via kernel.verifyTree → valid
  - All 3 attest (blockHash=B0, proofValid=true)
  - 300/300 stake attested → supermajority ✓

Slot 1 (proposer: Bob)
  - Bob creates block B1 with proof P2: consumes R2, produces R3
  - All 3 verify and attest → supermajority ✓

Slot 2 (proposer: Carol)
  - Carol creates block B2 (empty — no pending proofs)
  - All 3 attest → supermajority ✓

Slot 3 (proposer: Alice)
  - Alice creates block B3
  - All 3 attest → supermajority ✓
  - End of epoch 0 → checkpoint at slot 0
  - 3/3 voted for epoch 0 → justified ✓

Slot 4 (proposer: Bob — epoch 1 begins)
  - Bob creates B4
  - Meanwhile: Eve (if she existed) tries to double-vote on slot 1
    → slashingDetector.recordVote returns evidence
    → Eve slashed, removed from active set

Slot 7 (end of epoch 1)
  - Epoch 1 checkpoint also justified
  - Epoch 0 was justified at (epoch-1) → finalized ✓
  - Blocks B0–B3 are now irreversible
```

## Implementation Notes

- Single file: `lib/consensus/pos-mvp.js` (~300 LOC)
- Pure in-memory, no networking, no persistence
- Test file: `tests/consensus/pos-mvp.test.js`
- No RANDAO — round-robin is sufficient for learning
- No inactivity leak — out of scope for MVP
- No surround vote detection — only double votes

---

## TODO_0048.Option_B — Proof of Authority (PoA) Alternative

### Motivation

The PoS design above (Option A) has 5 interacting components (~300 LOC). For a first consensus implementation, PoA is dramatically simpler: it replaces all cryptoeconomic machinery with a trust assumption on a known validator set. This is the approach used by Gnosis Chain (AuRa), Ethereum testnets (Clique/EIP-225), and private chains.

**Key insight**: PoA replaces cryptoeconomic game theory with a trust assumption. By assuming validators are known and accountable off-chain, the entire economic layer disappears.

### Why PoA First

| | PoS (Option A) | PoA (Option B) |
|---|---|---|
| **Components** | 5 (registry, blocks, attestations, finality, slashing) | 2 (blocks, validation) |
| **LOC estimate** | ~300 | ~100 |
| **State** | Validator balances, stake, slashing records, finality tracker, vote history | Validator list (fixed) |
| **Concepts to implement** | Supermajority, Casper FFG, double-vote detection | Round-robin, signature check |
| **CALC mapping complexity** | Same (proofs = transactions) | Same (proofs = transactions) |
| **What we learn** | Consensus + economics | Consensus only |

The CALC integration points (Component_6 above) are **identical** for both — the consensus layer only decides block ordering, not proof semantics. Starting with PoA lets us validate the THY_0011 mapping without getting bogged down in economics.

### TODO_0048.Option_B.Design — PoA for CALC (Clique-inspired)

Three phases of increasing complexity. Each phase is self-contained — implement Phase 1 first, extend later.

---

### Phase 1: Strict Round-Robin (~80 LOC)

The simplest possible PoA. One designated proposer per block, no forks, no missed-block recovery. Useful for validating the CALC integration without any consensus complexity.

#### TODO_0048.Option_B.P1.Component_1 — Block Structure & Hashing

```js
const crypto = require('crypto')

// Compute a short deterministic hash from block contents
function hashBlock(block) {
  const data = JSON.stringify({
    number: block.number,
    parentHash: block.parentHash,
    proposerId: block.proposerId,
    proofSubmissions: block.proofSubmissions,
    timestamp: block.timestamp
  })
  return crypto.createHash('sha256').update(data).digest('hex').slice(0, 16)
}

// Create a block with auto-computed hash
function createBlock({ number, parentHash, proposerId, proofSubmissions, timestamp }) {
  const block = {
    number,
    parentHash,
    proposerId,
    proofSubmissions,    // List<{ proof, consumed: hash[], produced: hash[] }>
    timestamp: timestamp || Date.now(),
    hash: null
  }
  block.hash = hashBlock(block)
  return block
}

// Genesis block — the root of every chain
function createGenesis() {
  const g = {
    number: 0,
    parentHash: '0'.repeat(16),
    proposerId: null,
    proofSubmissions: [],
    timestamp: 0,
    hash: null
  }
  g.hash = hashBlock(g)
  return g
}
```

#### TODO_0048.Option_B.P1.Component_2 — Proposer Selection

```js
// Deterministic round-robin. Zero state needed.
function expectedProposer(validators, blockNumber) {
  return validators[blockNumber % validators.length]
}
```

With 3 validators `['alice', 'bob', 'carol']`:
```
Block 0 (genesis): no proposer
Block 1: validators[1 % 3] = 'bob'
Block 2: validators[2 % 3] = 'carol'
Block 3: validators[0 % 3] = 'alice'
Block 4: validators[1 % 3] = 'bob'    ← cycle repeats
```

#### TODO_0048.Option_B.P1.Component_3 — Block Validation

```js
function validateBlock(block, parent, validators, verifyProof) {
  // 1. Parent linkage — block must build on the known parent
  if (block.parentHash !== parent.hash)
    return { valid: false, reason: 'parent hash mismatch' }

  // 2. Block number must be sequential
  if (block.number !== parent.number + 1)
    return { valid: false, reason: 'bad block number' }

  // 3. Time must advance (prevents timestamp manipulation)
  if (block.timestamp <= parent.timestamp)
    return { valid: false, reason: 'timestamp not increasing' }

  // 4. Only the designated proposer may sign this block
  if (block.proposerId !== expectedProposer(validators, block.number))
    return { valid: false, reason: 'wrong proposer' }

  // 5. Every proof submission must pass L1 kernel verification
  for (const sub of block.proofSubmissions) {
    if (!verifyProof(sub.proof))
      return { valid: false, reason: 'invalid proof' }
  }

  return { valid: true }
}
```

The entire consensus is two questions: "is it your turn?" and "are the proofs valid?"

#### TODO_0048.Option_B.P1.Component_4 — Linear Chain + Resource Tracking

```js
function createChain(validators, verifyProof) {
  const genesis = createGenesis()
  const blocks = [genesis]
  const resourcePool = new Set()  // current set of available linear resources

  return {
    validators,
    head()   { return blocks[blocks.length - 1] },
    height() { return blocks.length - 1 },

    // Validate, check resources, apply atomically
    append(block) {
      // Structural validation
      const result = validateBlock(block, this.head(), validators, verifyProof)
      if (!result.valid) return result

      // Resource availability check — consumed resources must exist
      for (const sub of block.proofSubmissions) {
        for (const c of sub.consumed) {
          if (!resourcePool.has(c))
            return { valid: false, reason: `resource ${c} not available` }
        }
      }

      // All checks passed — apply state transition atomically
      for (const sub of block.proofSubmissions) {
        for (const c of sub.consumed) resourcePool.delete(c)
        for (const p of sub.produced) resourcePool.add(p)
      }
      blocks.push(block)
      return { valid: true }
    },

    resources() { return new Set(resourcePool) },
    blockAt(n)  { return blocks[n] || null }
  }
}
```

**Resource tracking is the CALC-specific part.** Each proof submission consumes and produces content-addressed hashes (linear resources). The chain enforces that consumed resources exist and are consumed exactly once — this is the linear logic guarantee.

#### TODO_0048.Option_B.P1.Scenario_1 — Happy Path

```
Setup: validators = ['alice', 'bob', 'carol']
       verifyProof = (p) => p.valid  // simplified for example

const chain = createChain(validators, verifyProof)

Block 1 (expected proposer: bob)
  block = createBlock({
    number: 1, parentHash: genesis.hash, proposerId: 'bob',
    proofSubmissions: [{ proof: {valid:true}, consumed: [], produced: ['R1','R2'] }]
  })
  chain.append(block)
  → { valid: true }
  → Pool: {R1, R2}

Block 2 (expected proposer: carol)
  block = createBlock({
    number: 2, parentHash: block1.hash, proposerId: 'carol',
    proofSubmissions: [{ proof: {valid:true}, consumed: ['R1'], produced: ['R3'] }]
  })
  chain.append(block)
  → { valid: true }
  → Pool: {R2, R3}         ← R1 consumed, R3 produced

Block 3 (expected proposer: alice)
  Empty block (proofSubmissions: [])
  → { valid: true }
  → Pool: {R2, R3}         ← unchanged
```

#### TODO_0048.Option_B.P1.Scenario_2 — Double-Spend Prevention

```
Continuing from above. Pool: {R2, R3}

Block 4 (expected proposer: bob)
  bob tries to consume R1 again:
    proofSubmissions: [{ proof: {valid:true}, consumed: ['R1'], produced: ['R4'] }]

  chain.append(block)
  → { valid: false, reason: 'resource R1 not available' }

  R1 was consumed in block 2. Linear logic prevents double-spending.
  Bob must submit a block that consumes only available resources.
```

#### TODO_0048.Option_B.P1.Scenario_3 — Wrong Proposer

```
Block 4 (expected proposer: bob)
  alice tries to produce block 4:
    createBlock({ number: 4, ..., proposerId: 'alice' })

  chain.append(block)
  → { valid: false, reason: 'wrong proposer' }

  Only bob can produce block 4 in Phase 1 (strict round-robin).
```

#### Phase 1 Limitation

If bob is offline, the chain **stalls**. No block 4 can ever be produced because only bob is authorized. Phase 2 solves this.

---

### Phase 2: Fault-Tolerant PoA (~150 LOC)

Handle offline validators using Clique-style mechanics: any authorized signer can produce any block, but in-turn signers get priority. Introduces forks and fork choice.

#### TODO_0048.Option_B.P2.Component_1 — Difficulty (In-Turn vs Out-of-Turn)

```js
const DIFF_INTURN  = 2   // in-turn proposer: publishes immediately
const DIFF_NOTURN  = 1   // out-of-turn backup: publishes after delay
const BLOCK_PERIOD = 1000 // ms minimum between blocks

// Which signer is "in turn" for this block number?
function inTurnSigner(validators, blockNumber) {
  return validators[blockNumber % validators.length]
}

// Compute difficulty based on whether proposer is in-turn
function blockDifficulty(proposerId, blockNumber, validators) {
  return proposerId === inTurnSigner(validators, blockNumber)
    ? DIFF_INTURN
    : DIFF_NOTURN
}
```

**Why difficulty matters:** When multiple validators produce competing blocks (a fork), the chain with more in-turn blocks accumulates higher total difficulty and wins. This naturally favors the "correct" chain where everyone is online.

#### TODO_0048.Option_B.P2.Component_2 — Signing Limit

Prevents a minority of validators from monopolizing block production.

```js
// SIGNER_LIMIT: each signer can sign at most 1 of every SIGNER_LIMIT consecutive blocks
// This is Clique's anti-spam rule from EIP-225
function signerLimit(validators) {
  return Math.floor(validators.length / 2) + 1
}

// Check: has this proposer signed too recently?
// recentBlocks = the last few ancestors of the block being validated
function signerAllowed(proposerId, recentBlocks, validators) {
  const limit = signerLimit(validators)

  // Look at the last (limit - 1) blocks
  const lookback = Math.min(limit - 1, recentBlocks.length)
  for (let i = 0; i < lookback; i++) {
    if (recentBlocks[recentBlocks.length - 1 - i].proposerId === proposerId) {
      return false  // this signer signed one of the recent blocks → blocked
    }
  }
  return true
}
```

**Worked example** — 3 validators, `SIGNER_LIMIT = floor(3/2) + 1 = 2`:

Each signer can sign at most 1 of every 2 consecutive blocks. After signing block N, a validator cannot sign block N+1 (but can sign N+2).

```
Block  In-turn   Who CAN sign (signing limit check)
  1      bob      all three (genesis has no proposer to conflict)
  2      carol    carol + alice  (if bob signed block 1, he's blocked)
                  carol + bob    (if alice signed block 1, she's blocked)
  3      alice    depends on who signed block 2
```

**Worked example** — 5 validators, `SIGNER_LIMIT = 3`:

Each signer can sign at most 1 of every 3 consecutive blocks. After signing block N, blocked for N+1 and N+2.

```
Block  In-turn   Blocked (if in-turn signed each block)
  1      bob      —
  2      carol    bob (signed 1)
  3      dave     bob (signed 1), carol (signed 2)
  4      eve      carol (signed 2), dave (signed 3)
  5      alice    dave (signed 3), eve (signed 4)
```

**Why this matters:** Without the limit, 2 colluding validators (out of 5) could alternate and produce every block, censoring the other 3. With `SIGNER_LIMIT = 3`, each must wait 2 blocks, so 2 colluding validators can produce at most 2 of every 3 blocks — not enough to exclude others indefinitely.

#### TODO_0048.Option_B.P2.Component_3 — Extended Block Validation

```js
function validateBlockP2(block, parent, recentBlocks, validators, verifyProof) {
  // 1. Parent linkage
  if (block.parentHash !== parent.hash)
    return { valid: false, reason: 'parent hash mismatch' }

  // 2. Sequential numbering
  if (block.number !== parent.number + 1)
    return { valid: false, reason: 'bad block number' }

  // 3. Time must advance, with minimum gap
  if (block.timestamp < parent.timestamp + BLOCK_PERIOD)
    return { valid: false, reason: 'block too fast (< BLOCK_PERIOD)' }

  // 4. Proposer must be an authorized validator
  if (!validators.includes(block.proposerId))
    return { valid: false, reason: 'not a validator' }

  // 5. Signing limit: proposer hasn't signed too recently
  if (!signerAllowed(block.proposerId, recentBlocks, validators))
    return { valid: false, reason: 'signed too recently (signing limit)' }

  // 6. Difficulty must match in-turn/out-of-turn status
  const expectedDiff = blockDifficulty(block.proposerId, block.number, validators)
  if (block.difficulty !== expectedDiff)
    return { valid: false, reason: 'wrong difficulty' }

  // 7. All proof submissions must pass L1 kernel verification
  for (const sub of block.proofSubmissions) {
    if (!verifyProof(sub.proof))
      return { valid: false, reason: 'invalid proof' }
  }

  return { valid: true }
}
```

Note: resource availability is checked separately in the block tree (Component_4), because the available resources depend on which fork the block extends.

#### TODO_0048.Option_B.P2.Component_4 — Block Tree + Fork Choice

With multiple validators able to produce blocks, forks can occur. We need a tree, not a list.

```js
// Collect N ancestor blocks by walking parentHash links
function getAncestors(hash, blockMap, count) {
  const result = []
  let current = blockMap.get(hash)
  while (current && result.length < count) {
    result.unshift(current)
    current = blockMap.get(current.parentHash)
  }
  return result
}

// Compute resource pool by walking from genesis to a given block
function computeResources(tipHash, blockMap) {
  // Collect full ancestry chain
  const chain = []
  let current = blockMap.get(tipHash)
  while (current) {
    chain.unshift(current)
    current = blockMap.get(current.parentHash)
  }
  // Replay resource transitions
  const pool = new Set()
  for (const block of chain) {
    for (const sub of block.proofSubmissions) {
      for (const c of sub.consumed) pool.delete(c)
      for (const p of sub.produced) pool.add(p)
    }
  }
  return pool
}

function createBlockTree(validators, verifyProof) {
  const genesis = createGenesis()
  genesis.difficulty = 0
  genesis.totalDifficulty = 0

  const blocks = new Map()          // hash → Block (all known blocks)
  const childMap = new Map()        // parentHash → [childHash] (for tip detection)
  blocks.set(genesis.hash, genesis)

  return {
    validators,
    genesis,

    // Insert a block into the tree. Validates everything.
    insert(block) {
      // Already known?
      if (blocks.has(block.hash))
        return { valid: false, reason: 'duplicate block' }

      // Parent must exist in our tree
      const parent = blocks.get(block.parentHash)
      if (!parent)
        return { valid: false, reason: 'unknown parent' }

      // Collect recent ancestors for signing limit check
      const recent = getAncestors(block.parentHash, blocks, validators.length)

      // Structural + consensus validation
      const result = validateBlockP2(block, parent, recent, validators, verifyProof)
      if (!result.valid) return result

      // Resource availability (along THIS block's ancestry, not canonical)
      const pool = computeResources(block.parentHash, blocks)
      for (const sub of block.proofSubmissions) {
        for (const c of sub.consumed) {
          if (!pool.has(c))
            return { valid: false, reason: `resource ${c} not available` }
        }
        // Apply within this block's submissions (for intra-block consistency)
        for (const c of sub.consumed) pool.delete(c)
        for (const p of sub.produced) pool.add(p)
      }

      // All checks passed — add to tree
      block.totalDifficulty = parent.totalDifficulty + block.difficulty
      blocks.set(block.hash, block)
      if (!childMap.has(block.parentHash)) childMap.set(block.parentHash, [])
      childMap.get(block.parentHash).push(block.hash)

      return { valid: true }
    },

    // Fork choice: highest total difficulty, tie-break by lower hash
    bestTip() {
      let best = genesis
      for (const [hash, block] of blocks) {
        const isLeaf = !childMap.has(hash) || childMap.get(hash).length === 0
        if (!isLeaf) continue
        if (block.totalDifficulty > best.totalDifficulty ||
            (block.totalDifficulty === best.totalDifficulty && hash < best.hash)) {
          best = block
        }
      }
      return best
    },

    // The canonical chain: genesis → bestTip
    canonicalChain() {
      const chain = []
      let current = this.bestTip()
      while (current) {
        chain.unshift(current)
        current = blocks.get(current.parentHash)
      }
      return chain
    },

    // Resource pool at the current canonical tip
    resources() {
      return computeResources(this.bestTip().hash, blocks)
    },

    getBlock(hash) { return blocks.get(hash) || null }
  }
}
```

**Fork choice rule:** Sum difficulty along each chain. The chain with the highest total wins. Since in-turn blocks contribute difficulty 2 and out-of-turn contribute 1, a chain where every validator was online and produced their assigned blocks naturally outscores any alternative.

#### TODO_0048.Option_B.P2.Component_5 — Block Production (Validator Perspective)

From a single validator's point of view: "should I produce a block now?"

```js
function produceBlock(validatorId, tree, proofSubmissions, timestamp) {
  const parent = tree.bestTip()
  const blockNumber = parent.number + 1

  // Am I allowed? (signing limit)
  const recent = getAncestors(parent.hash, /* blocks */, tree.validators.length)
  if (!signerAllowed(validatorId, recent, tree.validators))
    return null  // can't sign — signed too recently

  // Am I in turn?
  const difficulty = blockDifficulty(validatorId, blockNumber, tree.validators)
  const isInTurn = difficulty === DIFF_INTURN

  // Timing: in-turn publishes immediately, out-of-turn waits
  // (In real Clique: out-of-turn delay = rand(SIGNER_COUNT * 500ms))
  const minTimestamp = parent.timestamp + BLOCK_PERIOD
  const delay = isInTurn ? 0 : Math.random() * tree.validators.length * 500
  const publishAt = minTimestamp + delay

  if (timestamp < publishAt)
    return null  // too early — wait

  const block = createBlock({
    number: blockNumber,
    parentHash: parent.hash,
    proposerId: validatorId,
    proofSubmissions,
    timestamp
  })
  block.difficulty = difficulty

  return block
}
```

**In-turn vs out-of-turn timing:**
```
Time ──────────────────────────────────────────────►

parent.timestamp + BLOCK_PERIOD
  │
  ├── In-turn signer publishes HERE (immediately)
  │
  ├── Out-of-turn signer A waits rand(n * 500ms)
  │      └── publishes here ─────┐
  │                               │
  ├── Out-of-turn signer B waits rand(n * 500ms)
  │      └── publishes here ──────────┐
  │                                    │
  ▼                                    ▼
  Whoever publishes first wins (others see it and don't bother)
```

#### TODO_0048.Option_B.P2.Scenario_1 — Missed Block + Recovery

```
Setup: validators = ['alice', 'bob', 'carol'], SIGNER_LIMIT = 2

Block 1 (in-turn: bob)
  bob is OFFLINE.

  After BLOCK_PERIOD ms, carol and alice notice no block.
  Both are authorized (signing limit: no recent blocks from either).

  carol creates block 1:
    difficulty = DIFF_NOTURN (1)   ← carol is not in-turn
    carol waits rand(3 * 500ms) = ~800ms
    publishes

  alice also creates block 1:
    difficulty = DIFF_NOTURN (1)
    alice waits rand(3 * 500ms) = ~1200ms
    publishes (but carol's already arrived)

  Two competing block 1s! This is a fork:
    genesis ─── carol's B1 (totalDiff=1)
           └── alice's B1 (totalDiff=1)

  Tie-break: lower hash wins. Say carol's hash < alice's hash.
  bestTip() → carol's B1.

Block 2 (in-turn: carol)
  carol just signed block 1 → signing limit blocks her.
    signerAllowed('carol', [carol's B1], validators)?
    lookback = 1. recentBlocks[-1].proposerId = 'carol'. BLOCKED.

  alice signs block 2:
    difficulty = DIFF_NOTURN (1)   ← alice is not in-turn for block 2
    signerAllowed? recentBlocks[-1] = carol's B1. 'alice' ≠ 'carol'. ✓

  bob comes back, signs block 2:
    difficulty = DIFF_INTURN? No — carol is in-turn for block 2 but blocked.
    Actually: inTurnSigner(validators, 2) = 'carol'. bob gets DIFF_NOTURN (1).

  Chain continues: genesis → carol's B1 → alice's B2 (totalDiff=2)
  No stall. One block missed, chain recovered automatically.
```

#### TODO_0048.Option_B.P2.Scenario_2 — Fork Resolution by Difficulty

```
Setup: validators = ['alice', 'bob', 'carol', 'dave', 'eve'], SIGNER_LIMIT = 3

Network partition: {alice, bob} see each other. {carol, dave, eve} see each other.

Block 1 (in-turn: bob)
  Partition A: bob produces B1a (diff=2, in-turn)
  Partition B: carol produces B1b (diff=1, out-of-turn)

Block 2 (in-turn: carol)
  Partition A: alice produces B2a (diff=1, out-of-turn). totalDiff=3
  Partition B: carol blocked (signed B1b). dave produces B2b (diff=1). totalDiff=2

Block 3 (in-turn: dave)
  Partition A: bob blocked (signed B1a). alice blocked (signed B2a).
               Nobody can sign! (SIGNER_LIMIT=3, both signed in last 2 blocks)
               ... wait for block 4.
  Partition B: eve produces B3b (diff=1). totalDiff=3

Partition heals at block 3. Both sides exchange blocks.

  Fork A: genesis → B1a(2) → B2a(1)              totalDiff=3, height=2
  Fork B: genesis → B1b(1) → B2b(1) → B3b(1)    totalDiff=3, height=3

  totalDiff tied! Tie-break by hash at tip. Say B3b wins.
  Fork B becomes canonical. Fork A blocks are orphaned.

  Key insight: in-turn blocks (difficulty 2) are worth double, so even a
  shorter chain with in-turn blocks can beat a longer chain without them.
  In normal operation (no partitions), the chain where everyone is online
  and in-turn always wins.
```

#### TODO_0048.Option_B.P2.Scenario_3 — Signing Limit Prevents Censorship

```
Setup: 5 validators, SIGNER_LIMIT = 3. Eve and Dave collude to censor alice/bob/carol.

WITHOUT signing limit:
  Block 1: eve
  Block 2: dave
  Block 3: eve    ← eve signs every other block
  Block 4: dave
  Block 5: eve
  ... alice, bob, carol never get to produce. Censored.

WITH signing limit (SIGNER_LIMIT = 3):
  Block 1: eve
  Block 2: dave
  Block 3: eve? NO — eve signed block 1, within lookback of 2. BLOCKED.
           dave? NO — dave signed block 2, within lookback. BLOCKED.
           → Only alice, bob, or carol can sign block 3.

  At least 1 of every 3 blocks MUST come from a non-colluding validator.
  Censorship requires controlling SIGNER_LIMIT validators (majority).
```

---

### Phase 3: Deterministic Finality (~180 LOC)

Add AuRa-style finality on top of Phase 2. Once `n/2 + 1` distinct validators have signed blocks in a suffix, everything before that suffix is irreversible.

#### TODO_0048.Option_B.P3.Component_1 — Finality Tracker

```js
function createFinalityTracker(validators) {
  const threshold = Math.floor(validators.length / 2) + 1

  return {
    threshold,
    lastFinalizedHash: null,
    lastFinalizedNumber: 0,

    // Given the canonical chain, find the latest finality point.
    //
    // Algorithm: scan backwards from tip, collecting distinct signers.
    // When we reach `threshold` distinct signers, the block where we
    // hit threshold (and all ancestors) is finalized.
    //
    // Intuition: if n/2+1 different validators built on top of block K,
    // then a majority has "seen and accepted" K. Reverting K would require
    // a majority to abandon their own blocks — contradicting honest majority.
    computeFinality(chain) {
      const seen = new Set()

      for (let i = chain.length - 1; i >= 1; i--) {
        seen.add(chain[i].proposerId)

        if (seen.size >= this.threshold) {
          // Block i is the START of a suffix with enough distinct signers.
          // Block i and all ancestors are finalized.
          this.lastFinalizedHash = chain[i].hash
          this.lastFinalizedNumber = chain[i].number
          return {
            finalizedNumber: chain[i].number,
            finalizedHash: chain[i].hash,
            window: chain.length - 1 - i,  // how many blocks in the suffix
            distinctSigners: seen.size
          }
        }
      }

      // Not enough distinct signers yet — nothing finalized
      return {
        finalizedNumber: 0,
        finalizedHash: null,
        window: chain.length - 1,
        distinctSigners: seen.size
      }
    }
  }
}
```

**What "finalized" means:** Once a block is finalized, no honest fork choice can ever remove it from the canonical chain. Even if a partition occurs, any alternative chain would need >n/2 validators to abandon blocks they already signed — which violates the honest majority assumption.

#### TODO_0048.Option_B.P3.Scenario_1 — Finality with 5 Validators

```
validators = ['alice', 'bob', 'carol', 'dave', 'eve']
threshold = floor(5/2) + 1 = 3

Chain: [genesis, B1(bob), B2(carol), B3(dave), B4(eve), B5(alice)]

After B1:
  scan back: {bob}. 1 < 3. Nothing finalized.

After B2:
  scan back: B2→{carol}, B1→{carol,bob}. 2 < 3. Nothing finalized.

After B3:
  scan back: B3→{dave}, B2→{dave,carol}, B1→{dave,carol,bob}. 3 ≥ 3!
  → B1 and genesis are finalized. (suffix B1..B3 has 3 distinct signers)
  → finalizedNumber: 1, window: 2

After B4:
  scan back: B4→{eve}, B3→{eve,dave}, B2→{eve,dave,carol}. 3 ≥ 3!
  → B2 and ancestors finalized. (suffix B2..B4)
  → finalizedNumber: 2, window: 2

After B5:
  scan back: B5→{alice}, B4→{alice,eve}, B3→{alice,eve,dave}. 3 ≥ 3!
  → B3 and ancestors finalized.
  → finalizedNumber: 3, window: 2
```

Best case: finality lags by `threshold - 1` blocks = 2 blocks behind tip.

#### TODO_0048.Option_B.P3.Scenario_2 — Finality with Repeated Signers

What if out-of-turn signers repeat? Finality slows down.

```
validators = ['alice', 'bob', 'carol', 'dave', 'eve'], threshold = 3

Chain: [genesis, B1(bob), B2(bob? NO — signing limit), ...]

Actually signing limit prevents exact repetition. But with 5 validators and
SIGNER_LIMIT = 3, a validator CAN re-sign after 2 blocks:

Chain: [genesis, B1(bob), B2(carol), B3(bob), B4(carol), B5(bob), ...]
  (dave, eve, alice all offline)

After B5:
  scan back: B5→{bob}, B4→{bob,carol}. Only 2 distinct signers.
  2 < 3. Nothing finalized.

  Even with 100 blocks from just bob and carol alternating, finality
  never advances — you need a THIRD distinct signer.

  This is correct: if only 2/5 validators are online, we DON'T have
  honest majority, so we SHOULDN'T finalize.

dave comes back and produces B6:
  scan back: B6→{dave}, B5→{dave,bob}, B4→{dave,bob,carol}. 3 ≥ 3!
  → B4 finalized. Finality resumes as soon as majority participates.
```

#### TODO_0048.Option_B.P3.Scenario_3 — Finality Prevents Reversals

```
validators = ['alice', 'bob', 'carol'], threshold = 2

Main chain: [genesis, B1(bob), B2(carol), B3(alice)]
  After B2: scan back → {carol, bob} = 2 ≥ 2. B1 finalized.
  After B3: scan back → {alice, carol} = 2 ≥ 2. B2 finalized.

Attacker tries to rewrite from genesis with a fork:
  Fork: [genesis, B1'(bob)]

  For B1 to be un-finalized, the attacker needs an alternative chain where
  B1 is NOT an ancestor AND that chain has higher totalDifficulty.

  But B1 is already finalized — honest nodes REFUSE to switch away from
  any chain that doesn't include B1. The fork is rejected regardless of
  its difficulty.

  Implementation: when selecting bestTip(), only consider tips whose
  ancestry includes lastFinalizedHash.
```

**Enforcement in fork choice:**

```js
// Modified bestTip() that respects finality
bestTip(finality) {
  let best = genesis
  for (const [hash, block] of blocks) {
    const isLeaf = !childMap.has(hash) || childMap.get(hash).length === 0
    if (!isLeaf) continue

    // Skip tips that don't descend from the finalized block
    if (finality.lastFinalizedHash) {
      const ancestry = getAncestors(hash, blocks, block.number + 1)
      const includesFinalized = ancestry.some(b => b.hash === finality.lastFinalizedHash)
      if (!includesFinalized) continue  // reject this fork
    }

    if (block.totalDifficulty > best.totalDifficulty ||
        (block.totalDifficulty === best.totalDifficulty && hash < best.hash)) {
      best = block
    }
  }
  return best
}
```

---

### ILL Encoding — PoA as Linear Logic

The PoA algorithms above can be expressed directly in ILL. The key insight: **linear logic's resource discipline IS the consensus invariant**. A `turn N` token is linear — it can only be consumed once, so exactly one block per slot is guaranteed by the type system. No runtime check needed.

#### Phase 1 in ILL — Strict Round-Robin

```ill
%% ═══════════════════════════════════════════════
%% Phase 1: Strict Round-Robin PoA
%% ═══════════════════════════════════════════════

%% --- Persistent configuration ---
%% These facts are reusable (!bang) — they define the validator set.
!validator alice.
!validator bob.
!validator carol.
!num_validators 3.

%% --- Backward clauses: expected proposer ---
%% Computed by backward chaining (like FFI-accelerated `mod`).
%% expected_proposer N V holds when V = validators[N % 3].

expected_proposer/0: expected_proposer N alice
  <- mod N 3 0.
expected_proposer/1: expected_proposer N bob
  <- mod N 3 1.
expected_proposer/2: expected_proposer N carol
  <- mod N 3 2.

%% --- Forward rule: block production ---
%% Consumes: turn N (linear — exactly one block per slot)
%%           tip ParentHash ParentN (linear — chain head moves)
%% Requires: !validator V, !expected_proposer N V (persistent — checked, not consumed)
%% Produces: block record (persistent), new tip, next turn

produce:
  turn N *
  tip ParentHash ParentN *
  !validator V *
  !expected_proposer N V *
  !inc ParentN N
  -o {
    exists Hash. (
      !block N Hash ParentHash V *
      tip Hash N *
      turn (s N))
  }.

%% --- Initial state ---
%% tip genesis_hash 0 * turn 1.
%%
%% The forward engine starts here and applies `produce` repeatedly.
```

**Why this works:** The `turn N` fact is **linear** — it exists exactly once and is consumed when a block is produced. This means:
- Exactly one block per slot (linear resource = consumed once)
- Only the expected proposer can fire the rule (`!expected_proposer N V` must be provable)
- The chain tip moves atomically (`tip` consumed and re-produced with new hash)

**Adding resource tracking** — proof submissions as linear transitions within a block:

```ill
%% A proof submission consumes and produces linear resources.
%% This is a separate rule that fires WITHIN a block's context.

%% Submit a proof: consume resource R1, produce resource R2
%% The proof must be valid (checked by L1 kernel via persistent clause).
submit:
  available R1 *
  !proof_valid P R1 R2
  -o {
    available R2
  }.

%% Double-spend is impossible:
%%   `available R1` is linear. After submit consumes it, R1 is gone.
%%   A second rule trying to consume R1 cannot fire — no matching fact.
%%   This is not a runtime check. It's a structural property of linear logic.
```

**Composing block production with resource transitions:**

```ill
%% Full block production with one proof submission:
%% Consume turn + tip + resource, produce block + new tip + new resource + next turn.

produce_with_proof:
  turn N *
  tip ParentHash ParentN *
  available R1 *
  !validator V *
  !expected_proposer N V *
  !inc ParentN N *
  !proof_valid P R1 R2
  -o {
    exists Hash. (
      !block N Hash ParentHash V *
      tip Hash N *
      available R2 *
      turn (s N))
  }.

%% Empty block (no proof submissions):
produce_empty:
  turn N *
  tip ParentHash ParentN *
  !validator V *
  !expected_proposer N V *
  !inc ParentN N
  -o {
    exists Hash. (
      !block N Hash ParentHash V *
      tip Hash N *
      turn (s N))
  }.
```

**Phase 1 execution trace** (what the forward engine would do):

```ill
%% Initial state:
%%   tip genesis_hash 0 * turn 1 * available R1 * available R2

%% Step 1: produce_with_proof fires
%%   turn 1 consumed, tip genesis_hash 0 consumed, available R1 consumed
%%   !expected_proposer 1 bob proved (1 % 3 = 1 → bob)
%%   !proof_valid P1 R1 R3 proved (L1 kernel)
%%   Produces: !block 1 H1 genesis_hash bob * tip H1 1 * available R3 * turn 2

%% Step 2: produce_with_proof fires
%%   turn 2 consumed, tip H1 1 consumed, available R2 consumed
%%   !expected_proposer 2 carol proved (2 % 3 = 2 → carol)
%%   Produces: !block 2 H2 H1 carol * tip H2 2 * available R4 * turn 3

%% Step 3: produce_empty fires (no resources to consume)
%%   turn 3 consumed, tip H2 2 consumed
%%   !expected_proposer 3 alice proved (3 % 3 = 0 → alice)
%%   Produces: !block 3 H3 H2 alice * tip H3 3 * turn 4

%% Final state:
%%   tip H3 3 * turn 4 * available R3 * available R4
%%   !block 1 H1 genesis_hash bob * !block 2 H2 H1 carol * !block 3 H3 H2 alice
```

#### Phase 2 in ILL — Fault Tolerance with Oplus

Phase 2's key addition: **any** validator can produce, with in-turn/out-of-turn distinction. This maps to **oplus (additive disjunction)** — the system chooses which validator produces.

```ill
%% ═══════════════════════════════════════════════
%% Phase 2: Fault-Tolerant PoA (Clique-style)
%% ═══════════════════════════════════════════════

%% In-turn check (backward clause)
in_turn/yes: in_turn N V
  <- expected_proposer N V.

not_in_turn/yes: not_in_turn N V
  <- expected_proposer N W
  <- neq V W.

%% Signing limit (backward clause)
%% V is allowed to sign block N if V did not sign any of the
%% last (SIGNER_LIMIT - 1) blocks.
%%
%% signed_block V M is a persistent record of who signed what.
%% signer_ok checks the lookback window.

signer_ok/base: signer_ok V N 0.    %% checked enough blocks, OK

signer_ok/step: signer_ok V N Remaining
  <- inc PrevN N                     %% PrevN = N - 1
  <- !block PrevN _ _ Signer         %% who signed block PrevN?
  <- neq V Signer                    %% V ≠ that signer
  <- inc RemPrev Remaining           %% decrement remaining
  <- signer_ok V PrevN RemPrev.      %% recurse

signer_ok/start: signer_ok_full V N
  <- signer_limit Limit
  <- inc LookbackCount Limit         %% lookback = SIGNER_LIMIT - 1
  <- signer_ok V N LookbackCount.

%% --- Forward rules: in-turn and out-of-turn production ---
%% Both consume the slot. Oplus models the nondeterministic choice
%% of which validator produces the block.

%% In-turn production (difficulty 2)
produce_inturn:
  slot N *
  tip ParentHash ParentN *
  !validator V *
  !in_turn N V *
  !signer_ok_full V N *
  !inc ParentN N
  -o {
    exists Hash. (
      !block N Hash ParentHash V *
      !difficulty N 2 *
      tip Hash N *
      slot (s N))
  }.

%% Out-of-turn production (difficulty 1)
produce_outturn:
  slot N *
  tip ParentHash ParentN *
  !validator V *
  !not_in_turn N V *
  !signer_ok_full V N *
  !inc ParentN N
  -o {
    exists Hash. (
      !block N Hash ParentHash V *
      !difficulty N 1 *
      tip Hash N *
      slot (s N))
  }.
```

**Fork choice** — in ILL, forks correspond to different branches of the symexec tree. The forward engine explores all possible orderings. The "best chain" is the path with highest cumulative difficulty — which can be computed as a backward clause:

```ill
%% Total difficulty along a chain ending at block N
total_difficulty/genesis: total_difficulty genesis_hash 0.

total_difficulty/step: total_difficulty Hash TD
  <- !block N Hash ParentHash V
  <- !difficulty N D
  <- total_difficulty ParentHash ParentTD
  <- plus ParentTD D TD.
```

**Key observation:** In Phase 2, the forward engine's symexec tree IS the fork tree. Each branch represents a different validator producing the next block. The constraint solver prunes impossible branches (signing limit violations via `!signer_ok_full`). The surviving leaves represent all possible chains.

#### Phase 3 in ILL — Finality

```ill
%% ═══════════════════════════════════════════════
%% Phase 3: Deterministic Finality (AuRa-style)
%% ═══════════════════════════════════════════════

%% Count distinct signers in a range of blocks [From..To]
%% Uses a "seen set" modeled as persistent facts within the query.

distinct_signers/base: distinct_count From From 0.  %% empty range

distinct_signers/step: distinct_count From To Count
  <- !block To _ _ Signer
  <- inc PrevTo To
  <- (
    %% Case 1: Signer already counted → don't increment
    (!already_seen Signer From To * distinct_count From PrevTo Count)
    +
    %% Case 2: New signer → increment
    (!not_seen Signer From To * distinct_count From PrevTo PrevCount
     * !inc PrevCount Count)
  ).

%% Finality check: block K is finalized when the suffix [K..Tip]
%% contains ≥ threshold distinct signers.
finalized: finalized K
  <- current_tip _ Tip
  <- distinct_count K Tip Count
  <- threshold Threshold
  <- gte Count Threshold.

%% threshold = floor(n/2) + 1
threshold/3: threshold 2 <- num_validators 3.
threshold/5: threshold 3 <- num_validators 5.
```

#### ILL vs JS — When to Use Which

| Aspect | JS implementation | ILL implementation |
|---|---|---|
| **Strengths** | Explicit control flow, easy debugging, familiar | Double-spend prevention is structural, fork exploration is automatic (symexec), consensus invariants are type-checked |
| **Weaknesses** | Must manually enforce linearity, fork handling is imperative | Signing limit lookback is awkward, no real-time scheduling, performance |
| **Best for** | Production-like MVP, testing, integration | Formal reasoning, proving properties, understanding the logic |
| **LOC** | ~180 | ~80 (excluding arithmetic primitives) |

**The deep insight:** In ILL, the consensus invariants aren't runtime checks — they're **structural properties**. Double-spending is impossible because linear resources can only be consumed once. The signing limit is a provability constraint. Fork choice is a search over the proof space. The ILL encoding doesn't just *implement* PoA — it *proves* that the consensus is correct by construction.

---

### CALC Integration Points

Identical across all three phases — consensus only decides block ordering:

| CALC API | PoA role |
|---|---|
| `kernel.verifyTree(proof)` | Validate proof submissions in blocks (`verifyProof` callback) |
| `Store.get(hash)` / `Store.put(term)` | Read/write content-addressed state (resource hashes) |
| `state.linear` (Set of hashes) | Resource pool — consumed/produced atomically per block |
| `state.persistent` (Set of hashes) | Reusable knowledge (rules under `!`) — never consumed |
| `forward.run(state, rules)` | Off-chain: provers search for proofs to submit as transactions |

```
┌───────────────────────────────────────────────────────────┐
│  PoA Consensus Layer                                      │
│                                                           │
│  produceBlock(validatorId, tree, proofSubmissions)         │
│       │                                                   │
│       ▼                                                   │
│  insert(block)                                            │
│       │                                                   │
│       ├──► validateBlockP2()                              │
│       │       ├── parentHash, number, timestamp           │
│       │       ├── proposerId ∈ validators?                │
│       │       ├── signerAllowed? (signing limit)          │
│       │       ├── difficulty matches in-turn/out-of-turn? │
│       │       └── verifyProof(sub.proof) ─── [L1 kernel]  │
│       │                                                   │
│       ├──► computeResources(parentHash)                   │
│       │       └── consumed ∈ pool? ─── [linear logic]     │
│       │                                                   │
│       └──► fork choice: bestTip() by totalDifficulty      │
│               └── finality check ─── [Phase 3]            │
└───────────────────────────────────────────────────────────┘
```

### What PoA Doesn't Teach (and PoS Does)

- How economic incentives align validator behavior
- How finality works without trusting validators
- How attestation aggregation scales
- How slashing deters misbehavior

These are important for understanding Ethereum, but they're orthogonal to validating the THY_0011 mapping of proofs-as-transactions onto linear logic.

### Implementation Notes

- Single file: `lib/consensus/poa-mvp.js` (~180 LOC for all 3 phases)
- Test file: `tests/consensus/poa-mvp.test.js`
- Pure in-memory, no networking, no persistence
- Phase 1 tests: happy path, wrong proposer, invalid proof, double-spend
- Phase 2 tests: missed block recovery, fork resolution, signing limit
- Phase 3 tests: finality advancement, finality with minority, finality-respecting fork choice
- **Recommended**: implement Phase 1 first, verify CALC integration works, then add Phase 2 + 3

### Comparison with Real PoA Protocols

| Feature | Clique (EIP-225) | AuRa (Gnosis) | Our PoA (Phase 1→3) |
|---|---|---|---|
| Scheduling | `block_num % n` | `floor(time/t) % n` | `block_num % n` |
| Missed blocks | Out-of-turn with delay | Out-of-turn + EmptyStep | Phase 1: stall, Phase 2: out-of-turn |
| Validator changes | In-header voting | Smart contract | None (fixed) |
| Signing limit | `floor(n/2)+1` | `floor(n/2)+1` | Phase 2: same |
| Difficulty | 2 (in-turn) / 1 (out-of-turn) | `U128_MAX + parent_step - step` | Phase 2: same as Clique |
| Fork choice | Cumulative difficulty | Weighted difficulty | Phase 2: cumulative difficulty |
| Finality | Probabilistic | Deterministic (n/2+1 signers) | Phase 3: same as AuRa |
| Signatures | secp256k1 in extraData | secp256k1 in seal | In-memory identity |
| LOC | ~600 (Geth) | ~2000 (OpenEthereum) | ~180 |

## Recommendation

**Start with PoA Phase 1**, then layer features:

1. **Phase 1 — Strict round-robin** (~80 LOC): Validates CALC integration (proofs as transactions, linear resource tracking). Chain stalls if a validator is offline — acceptable for tests.
2. **Phase 2 — Fault tolerance** (~150 LOC): Out-of-turn blocks, signing limit, fork choice. Chain never stalls with honest majority.
3. **Phase 3 — Finality** (~180 LOC): AuRa-style deterministic finality. Finalized blocks can never be reverted.
4. **Phase 4 — PoS upgrade** (Option A, ~300 LOC): Add staking, attestations, Casper FFG. Uses the PoA chain as scaffolding.

## References

- [THY_0011 — PoS Consensus Adaptation for CALC](../theory/0011_pos-consensus-calc.md)
- [RES_0059 — Ethereum Proof of Stake Consensus](../research/0059_ethereum-pos-consensus.md)
- [RES_0067 — Proof of Authority Consensus Mechanisms](../research/0067_proof-of-authority-consensus.md)
