---
title: "Simplified PoS Consensus MVP"
created: 2026-02-24
modified: 2026-02-24
summary: "In-memory PoS consensus (~300 LOC) capturing Ethereum's flavor as a learning/prototyping tool for CALC"
tags: [consensus, pos, learning, prototype]
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

## References

- [THY_0011 — PoS Consensus Adaptation for CALC](../theory/0011_pos-consensus-calc.md)
- [RES_0059 — Ethereum Proof of Stake Consensus](../research/0059_ethereum-pos-consensus.md)
