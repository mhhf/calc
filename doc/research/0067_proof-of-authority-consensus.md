---
title: "Proof of Authority Consensus Mechanisms"
created: 2026-03-01
modified: 2026-03-01
summary: "Technical survey of PoA consensus: AuRa (Authority Round), Clique (EIP-225), comparison, minimal PoA design, and simplicity analysis vs PoS"
tags: [consensus, blockchain, ethereum, proof-of-authority, validators, finality, round-robin, evm]
category: "Ownership"
---

## 1. Core PoA Model

PoA is a consensus family where a **fixed set of known authorities** (validators/sealers) take turns producing blocks. No mining, no staking -- identity and reputation are the stake.

**Minimal assumptions:**
- Set of `n` authorized validators known to all participants
- Deterministic schedule assigns block production rights
- Validators sign blocks with their private key
- Any node can verify a block came from an authorized validator

**What PoA eliminates vs PoS:**

| Concern | PoS | PoA |
|---|---|---|
| Validator selection | Randomized (RANDAO, VRF) | Deterministic round-robin |
| Economic incentive | Staking + rewards + slashing | Reputation only |
| Committee formation | Per-slot/epoch random sampling | None (all validators always active) |
| Withdrawal/bonding | Complex state machine | None |
| Reward accounting | Per-block issuance + attestation rewards | Optional (can be zero) |
| Fork choice | LMD-GHOST + Casper FFG | Simple longest-chain or highest-score |
| Finality | 2 epochs (~12.8 min on Ethereum) | n/2+1 blocks (AuRa) or probabilistic (Clique) |
| State needed | Validator registry, balances, slashing records | Signer list only |

## 2. AuRa (Authority Round)

Used by Gnosis Chain (pre-merge), POA Network, and other OpenEthereum-based chains.

### 2.1 Algorithm

```
Parameters:
  n     = number of validators
  t     = step duration (seconds), typically 5
  V[]   = ordered validator set (addresses)

Step calculation:
  s = floor(unix_time / t)

Primary selection:
  primary(s) = V[s mod n]

Block production:
  Only primary(s) may produce a block at step s.
  Producing >1 block per step = misbehavior.
  Producing a block out of turn = misbehavior.
```

### 2.2 Chain Scoring (Fork Choice)

```
difficulty(block) = U128_MAX + parent_step - current_step
```

Where `parent_step` is the step of the parent block. This means:
- Consecutive blocks (no gaps) get maximum difficulty
- Skipped steps reduce difficulty
- Fork choice = **highest cumulative difficulty** (heaviest chain)

The formula ensures blocks produced on time (without skipping steps) are preferred, naturally penalizing chains with missed validators.

### 2.3 Finality

Define `SIG_SET(C[K..])` = set of distinct block authors from block K onward:

```
SIG_SET(B) = { a | exists b in B : AUTHOR(b) = a }

Finality condition:
  If |SIG_SET(C[K..])| > n/2, then C[K] and all ancestors are finalized.

Requirement: 2f + 1 <= n  (tolerates < 50% Byzantine)
```

**Finality latency:**
- Best case: `n/2 + 1` blocks = `(n/2 + 1) * t` seconds
- Worst case: `2n + 2` message round trips
- Gnosis (19 validators, t=5s): ~40 blocks = ~200 seconds

### 2.4 Empty Steps

To avoid blockchain bloat from empty blocks while maintaining finality:

```
When primary has no transactions:
  Broadcast EmptyStep(step, parent_hash) signed message
  (instead of producing an empty block)

Next non-empty block:
  Includes accumulated EmptyStep messages in seal
  EmptyStep signers receive rewards
  EmptySteps count toward finality (SIG_SET)
```

Constraints: no duplicate empty steps, must be ordered in seal.

### 2.5 Validator Set Management

Four modes (OpenEthereum):

1. **Immutable list** -- hardcoded in genesis, never changes
2. **Contract-based** -- smart contract with `getValidators()`, `InitiateChange` event, `finalizeChange()`
3. **Reporting contract** -- extends (2) with `reportBenign()` and `reportMalicious(proof)`
4. **Multi-set** -- switches between validator configs at specified block heights

Benign misbehavior: not producing a block when primary.
Malicious misbehavior: producing two blocks for same step (equivocation). Requires proof (both signed blocks).

### 2.6 Security Properties

- **Byzantine tolerance**: < 50% (tight bound per audit)
- **Liveness**: chain progresses as long as >50% of validators are honest and connected
- **Safety**: no conflicting finalized blocks under honest majority
- **Known attack**: "Cloning attack" -- validator duplicates keys across two nodes talking to different partitions. Always succeeds against AuRa. Exploits lack of key-node binding.
- **Time sensitivity**: relies on synchronized clocks (NTP). Clock skew causes validators to disagree on step numbers.

## 3. Clique (EIP-225)

Ethereum's PoA for testnets (Rinkeby, Goerli). Designed for minimal implementation effort.

### 3.1 Design Goals

- Simple enough to embed in any Ethereum client
- Compatible with existing sync (fast, light, warp)
- No custom logic in critical paths
- Validator management fully in block headers (no smart contracts)

### 3.2 Block Header Repurposing

| Field | Normal Use | Clique Use |
|---|---|---|
| `beneficiary` | Miner reward address | Vote target address (0 on checkpoint) |
| `nonce` | PoW nonce | `0xffff...` = authorize, `0x0000...` = deauthorize |
| `extraData` | Arbitrary | `[32B vanity][signers on checkpoint][65B seal]` |
| `difficulty` | PoW difficulty | 2 = in-turn, 1 = out-of-turn |
| `mixHash` | PoW mix | Reserved (zeroed) |
| `ommersHash` | Uncle blocks | Must be empty-list hash |

### 3.3 Signing Rules

```
Parameters:
  SIGNER_COUNT  = current number of authorized signers
  SIGNER_LIMIT  = floor(SIGNER_COUNT / 2) + 1
  BLOCK_PERIOD   = 15 seconds (configurable)
  EPOCH_LENGTH   = 30000 blocks

Constraints:
  Each signer may sign at most 1 of any SIGNER_LIMIT consecutive blocks.
  (Prevents any single signer from dominating)
```

### 3.4 In-Turn vs Out-of-Turn

```
In-turn condition:
  block_number % SIGNER_COUNT == signer_index

If in-turn:
  difficulty = DIFF_INTURN (2)
  Publish immediately at parent_timestamp + BLOCK_PERIOD

If out-of-turn:
  difficulty = DIFF_NOTURN (1)
  Delay by rand(SIGNER_COUNT * 500ms)
```

**Fork choice**: highest cumulative difficulty. In-turn blocks (difficulty 2) naturally preferred over out-of-turn (difficulty 1).

### 3.5 Missed Block Recovery

```
Step 0: In-turn signer publishes immediately at parent_time + BLOCK_PERIOD
Step 1: If no block after ~500ms, out-of-turn signers start creating blocks
Step 2: Each out-of-turn signer waits rand(SIGNER_COUNT * 500ms)
Step 3: First to finish waiting publishes (difficulty 1)
Result: Chain continues even if in-turn signer is down
```

### 3.6 Voting / Validator Changes

```
To add signer X:    set beneficiary=X, nonce=0xffff...ffff
To remove signer X: set beneficiary=X, nonce=0x0000...0000

Tallying:
  Votes accumulate live as chain grows.
  When a proposal reaches SIGNER_LIMIT votes: applied immediately.
  Only latest vote per (signer, target) pair counts.
  No cascading: only the voted-on beneficiary changes per block.

Epochs (every EPOCH_LENGTH blocks):
  All pending votes discarded.
  Checkpoint block contains full signer list in extraData.
  Enables stateless sync from any checkpoint.
```

### 3.7 Security

- **Tolerance**: up to `floor((SIGNER_COUNT - 1) / 2)` malicious signers
- **No immediate finality**: forks possible, reorganizations can happen
- **Censorship**: requires 51% control (any signer can only sign 1 of SIGNER_LIMIT blocks)
- **Cloning attack**: succeeds in most cases (same vulnerability as AuRa)

## 4. AuRa vs Clique Comparison

| Aspect | AuRa | Clique |
|---|---|---|
| Primary selection | `s mod n` (wall-clock step) | `block_number mod n` |
| Step duration | Fixed (e.g. 5s) | `BLOCK_PERIOD` minimum gap |
| Empty blocks | EmptyStep messages (optional) | Empty blocks produced |
| Finality | Deterministic: n/2+1 distinct signers | Probabilistic (longest chain) |
| Validator changes | Smart contract or config | In-header voting |
| Fork choice | `U128_MAX + parent_step - step` | Cumulative difficulty (2 vs 1) |
| Misbehavior reporting | Contract-based | None (social layer) |
| Implementation | OpenEthereum (Rust) | Geth (Go) |
| Complexity | Medium | Low |

### IBFT 2.0 / QBFT (BFT-based PoA, for comparison)

| Aspect | Clique | IBFT 2.0 / QBFT |
|---|---|---|
| Finality | Probabilistic | **Immediate** (no forks) |
| Fault tolerance | Up to 50% | Up to 33% (need 2/3+1 honest) |
| Min validators | 1 | 4 |
| Speed | Faster block addition | Slower (multi-round voting) |
| Forks | Possible | Impossible |

## 5. Minimal PoA Specification

The absolute simplest PoA that could work:

### 5.1 State

```
validators: Address[n]    // fixed, hardcoded, never changes
chain: Block[]            // the blockchain
```

### 5.2 Block Structure

```
Block {
  number:      uint
  parent_hash: bytes32
  timestamp:   uint
  state_root:  bytes32     // post-execution state
  tx_root:     bytes32     // transaction trie root
  signature:   bytes65     // secp256k1 signature
}
```

### 5.3 Rules

```
1. SCHEDULING:
   expected_signer(block_number) = validators[block_number % n]

2. BLOCK VALIDITY:
   - recover(signature, block_hash) must be in validators[]
   - block.timestamp >= parent.timestamp + BLOCK_PERIOD
   - block.parent_hash == hash(parent)
   - state transitions are valid

3. FORK CHOICE (simplest):
   Prefer longest valid chain.
   Tie-break: prefer chain where more blocks are signed by expected_signer.

4. MISSED BLOCKS:
   If expected_signer doesn't produce within BLOCK_PERIOD + GRACE:
     any validator may produce (lower priority).
   Chain naturally prefers in-turn blocks via scoring.

5. FINALITY:
   After n/2 + 1 blocks by distinct signers: finalized.
   (Optional: can skip and just use longest-chain.)
```

### 5.4 What This Eliminates

Compared to full Ethereum PoS:
- **No beacon chain** -- single chain only
- **No epochs/slots** -- continuous round-robin
- **No RANDAO** -- deterministic schedule
- **No attestations** -- block production implies agreement
- **No validator registry** -- hardcoded list
- **No deposits/withdrawals** -- no staking
- **No slashing** -- no economic penalties
- **No sync committees** -- all validators always active
- **No proposer/builder separation** -- proposer builds own block
- **No blob transactions** -- no data availability layer
- **No reward calculation** -- no issuance

### 5.5 State Transitions Needed

For a minimal PoA EVM chain, the state machine is just:

```
1. Verify block header (signer, parent, timestamp)
2. Execute transactions against EVM state
3. Compute new state root
4. Verify state root matches block

No consensus-specific state transitions at all.
(Unless you add validator voting, which is optional.)
```

## 6. Why PoA is Radically Simpler than PoS

The core insight: **PoA replaces cryptoeconomic game theory with a trust assumption.** By assuming validators are known and accountable off-chain, the entire economic layer disappears:

1. **Schedule is trivial**: `validator[block % n]` vs RANDAO + committee selection + lookahead
2. **No state explosion**: PoS needs validator balances, effective balances, activation/exit queues, slashing records. PoA needs one list.
3. **No cross-chain coordination**: PoS has beacon chain + execution layer + attestation aggregation. PoA is one chain.
4. **Fork choice is simple**: longest chain (or heaviest by in-turn scoring). No LMD-GHOST, no Casper FFG, no justification/finalization epochs.
5. **No economic analysis needed**: no reward curves, no MEV considerations, no proposer boost, no inactivity leak.
6. **Implementation: ~200 lines** (Clique is ~600 lines in Geth including voting; stripped version would be ~200). PoS consensus is ~50,000+ lines.

**The trade-off**: PoA requires trusting the validator set. This is acceptable for testnets, private chains, and scenarios where validators are known entities (e.g., a consortium of companies).

## References

- [EIP-225: Clique PoA](https://eips.ethereum.org/EIPS/eip-225)
- [OpenEthereum AuRa Specification](https://openethereum.github.io/Aura)
- [Gnosis Chain AuRa + POSDAO](https://docs.gnosischain.com/about/specs/consensus/aura)
- [OpenEthereum Validator Sets](https://openethereum.github.io/Validator-Set)
- [AuRa Consensus Protocol Audit](https://github.com/poanetwork/wiki/wiki/Aura-Consensus-Protocol-Audit)
- [Cloning Attack on PoA (NDSS 2020)](https://arxiv.org/abs/1902.10244)
- [Besu PoA Comparison](https://besu.hyperledger.org/private-networks/concepts/poa)
- [ethereum.org PoA Overview](https://ethereum.org/developers/docs/consensus-mechanisms/poa/)
