# Strategy Layers for Forward Rule Indexing

The strategy stack partitions forward rules across indexing layers for efficient candidate lookup during symbolic execution. Each layer claims rules it can index well; unclaimed rules fall through to the next.

## Layer Stack (ordered)

```
fingerprintLayer  →  O(1) per step, for rules with ground discriminator
discTreeLayer     →  O(depth) per fact, general-purpose trie over patterns
predicateLayer    →  O(R) linear scan (safety net, rarely activates)
```

`detectStrategy(rules)` auto-builds this stack. The fingerprint layer is added only when a dominant discriminating predicate is detected (e.g., `code(PC, OPCODE)` in EVM). The disc-tree layer claims all remaining rules.

## How the Discrimination Tree Works

Each rule's first linear trigger pattern is flattened to a **preorder tag sequence**:

```
code(_PC, push1)  →  [code, WILDCARD, atom]
stack(_V, _S)     →  [stack, WILDCARD, WILDCARD]
```

These sequences form paths in a trie. At query time, a ground fact is flattened the same way, and the trie is walked following both concrete tag matches and wildcard branches (which skip entire subtrees using arity-based size computation).

## Writing a Custom Strategy Layer

A layer has two methods:

```javascript
{
  claims(rule) → boolean,   // "can I index this rule?"
  build(rules) → {          // build index from claimed rules
    getCandidateRules(state, stateIndex) → rule[]
  }
}
```

### Example: Custom Fingerprint for Your Program

If your program has a dominant lookup pattern (like EVM's `code(PC, OPCODE)`), `detectFingerprintConfig()` auto-detects it. This works when:

1. A binary+ predicate has one ground child and one variable child across most rules
2. A pointer predicate (e.g., `pc(VALUE)`) links the current position to the lookup key

No manual configuration needed — just write rules like:
```
code(_PC, my_opcode) * pc(_PC) * ... -o { ... }
```

### Example: Domain-Specific Layer

For programs where the auto-detected layers aren't enough:

```javascript
function makeMyLayer(config) {
  return {
    claims: (rule) => rule.triggerPreds.includes(config.pred),
    build: (rules) => {
      const index = {};
      for (const rule of rules) {
        const key = extractKey(rule);  // your domain logic
        if (!index[key]) index[key] = [];
        index[key].push(rule);
      }
      return {
        getCandidateRules(state, stateIndex) {
          const key = computeKey(state);  // your domain logic
          return index[key] || [];
        }
      };
    }
  };
}
```

Then register it before the disc-tree:
```javascript
const layers = [];
layers.push(makeMyLayer({ pred: 'myPred' }));
layers.push(makeDiscTreeLayer());
const stack = buildStrategyStack(rules, layers);
```

## Performance Characteristics

| Layer | Lookup | Build | Best For |
|-------|--------|-------|----------|
| fingerprint | O(1) | O(R) | Programs with ground discriminator (EVM, instruction sets) |
| disc-tree | O(D * F_rel) | O(R * P) | General programs, 50-1000 rules |
| predicate | O(R) | O(R) | Fallback for edge cases |

Where: R = rules, D = pattern depth, F_rel = facts from relevant predicates, P = pattern size.

The disc-tree only scans facts from predicates that appear in its indexed rules, so it's efficient even when the state has many unrelated facts.
