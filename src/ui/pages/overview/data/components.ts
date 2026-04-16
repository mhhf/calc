/**
 * Canonical component registry.
 *
 * Every architecturally-significant component in CALC appears here exactly
 * once. Views project onto this list via filter/groupBy.
 *
 * Editorial principles:
 *   - One entry per cohesive module (file or tight directory).
 *   - `summary` is a single active-voice line.
 *   - `files` points at the *primary* source, not every related file.
 *   - `trust` is the soundness impact of a bug, not the complexity.
 *   - `stages` is *when code runs*, not when it's authored.
 *   - Keep the list manageable (~45 entries) — the Atlas stays legible.
 */

import type { Component } from './types';

export const COMPONENTS: Component[] = [
  // ─── Kernel (trust=kernel) ─────────────────────────────────────────
  {
    id: 'kernel.store',
    name: 'Content-Addressed Store',
    summary: 'Formulas are hashes (numbers); O(1) equality by identity',
    files: ['lib/kernel/store.js'],
    trust: 'kernel', specificity: 'framework',
    stages: ['parse', 'compile', 'execute', 'certify', 'present'],
    modes: ['backward', 'forward', 'symbolic', 'certification'],
    deepDive: 'prover',
    cluster: 'kernel',
  },
  {
    id: 'kernel.sequent',
    name: 'Sequent',
    summary: 'Sequent construction, context multisets, display encoding',
    files: ['lib/kernel/sequent.js'],
    trust: 'kernel', specificity: 'framework',
    stages: ['execute', 'present'], modes: ['backward'],
    deepDive: 'prover', cluster: 'kernel',
  },
  {
    id: 'kernel.unify',
    name: 'Unify',
    summary: 'First-order unification + occurs check',
    files: ['lib/kernel/unify.js'],
    trust: 'kernel', specificity: 'framework',
    stages: ['execute'], modes: ['backward', 'forward', 'symbolic'],
    deepDive: 'prover', cluster: 'kernel',
  },
  {
    id: 'kernel.substitute',
    name: 'Substitute',
    summary: 'Capture-avoiding substitution over content-addressed terms',
    files: ['lib/kernel/substitute.js'],
    trust: 'kernel', specificity: 'framework',
    stages: ['execute'], modes: ['backward', 'forward'],
    deepDive: 'prover', cluster: 'kernel',
  },
  {
    id: 'kernel.ast',
    name: 'AST',
    summary: 'Constructor arity, predicate head, child accessors',
    files: ['lib/kernel/ast.js'],
    trust: 'kernel', specificity: 'framework',
    stages: ['parse', 'compile', 'execute'], modes: ['backward', 'forward', 'symbolic'],
    deepDive: 'prover', cluster: 'kernel',
  },
  {
    id: 'kernel.eq-theory',
    name: 'Equational Theories',
    summary: 'Pluggable cross-tag matching (strlit, binlit, sha3)',
    files: ['lib/kernel/eq-theory.js'],
    trust: 'kernel', specificity: 'framework',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'prover', cluster: 'kernel',
  },
  {
    id: 'prover.kernel',
    name: 'Proof Verifier (L1)',
    summary: 'Re-derives every step from rule premises; trust anchor',
    files: ['lib/prover/kernel.js'],
    trust: 'kernel', specificity: 'framework',
    stages: ['execute', 'certify'], modes: ['backward', 'certification'],
    deepDive: 'prover', cluster: 'prover.kernel',
  },

  // ─── Backward Prover Stack (trust=infrastructure) ──────────────────
  {
    id: 'prover.generic',
    name: 'Generic Search (L2)',
    summary: 'Forward/backward search primitives, rule application',
    files: ['lib/prover/generic.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['execute'], modes: ['backward'],
    deepDive: 'prover', cluster: 'prover',
  },
  {
    id: 'prover.focused',
    name: 'Focused Prover (L3)',
    summary: 'Andreoli focusing: alternating positive/negative phases',
    files: ['lib/prover/focused.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['execute'], modes: ['backward'],
    deepDive: 'prover', cluster: 'prover',
  },
  {
    id: 'prover.strategy',
    name: 'Strategy (L4)',
    summary: 'Manual (interactive) and auto (iterative deepening) search',
    files: ['lib/prover/strategy/'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['execute'], modes: ['backward'],
    deepDive: 'prover', cluster: 'prover',
  },
  {
    id: 'prover.bridge',
    name: 'Monad Bridge',
    summary: 'Lax monad {A} shifts polarity; routes backward → forward',
    files: ['lib/prover/bridge.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['execute'], modes: ['backward', 'forward'],
    deepDive: 'prover', cluster: 'prover',
    details: 'Three profiles: full (opaque), guided (oracle + verified ILL terms), off (pure backward).',
  },
  {
    id: 'prover.rule-interpreter',
    name: 'Rule Interpreter',
    summary: 'Turns rule descriptors → premise computation',
    files: ['lib/prover/rule-interpreter.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['compile', 'execute'], modes: ['backward'],
    deepDive: 'prover', cluster: 'prover',
  },

  // ─── Forward Engine: Generic Core (trust=infrastructure) ───────────
  {
    id: 'engine.match',
    name: 'Match',
    summary: 'Pattern matching + tryMatch pipeline + matchOpts factories',
    files: ['lib/engine/match.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'engine', cluster: 'engine.core',
  },
  {
    id: 'engine.strategy',
    name: 'Strategy Stack',
    summary: 'Rule selection: fingerprint → disc-tree → predicate',
    files: ['lib/engine/strategy.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'engine', cluster: 'engine.core',
  },
  {
    id: 'engine.forward',
    name: 'Forward',
    summary: 'Committed-choice main loop (exec)',
    files: ['lib/engine/forward.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['execute'], modes: ['forward'],
    deepDive: 'engine', cluster: 'engine.core',
  },
  {
    id: 'engine.explore',
    name: 'Explore',
    summary: 'Exhaustive DFS with mutation/undo log',
    files: ['lib/engine/explore.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['execute'], modes: ['symbolic'],
    deepDive: 'engine', cluster: 'engine.core',
  },
  {
    id: 'engine.compile',
    name: 'Compile',
    summary: 'Rule compilation: de Bruijn slots, metavar analysis',
    files: ['lib/engine/compile.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['compile'], modes: ['forward', 'symbolic'],
    deepDive: 'compilation', cluster: 'engine.core',
  },
  {
    id: 'engine.backchain',
    name: 'Backchain',
    summary: 'SLD-style backward chaining for persistent goals',
    files: ['lib/engine/backchain.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['execute'], modes: ['backward', 'forward'],
    deepDive: 'engine', cluster: 'engine.core',
  },
  {
    id: 'engine.fact-set',
    name: 'FactSet + Arena',
    summary: 'Sorted typed-array groups + undo-log for explore',
    files: ['lib/engine/fact-set.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'engine', cluster: 'engine.core',
  },
  {
    id: 'engine.convert',
    name: 'Convert',
    summary: '.ill files → content-addressed hash state',
    files: ['lib/engine/convert.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['parse'], modes: ['forward', 'symbolic'],
    deepDive: 'compilation', cluster: 'engine.core',
  },
  {
    id: 'engine.formula-utils',
    name: 'Formula Utils',
    summary: 'Connective-aware decomposition (shared across pipeline)',
    files: ['lib/engine/formula-utils.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['compile', 'execute'], modes: ['forward', 'symbolic'],
    deepDive: 'engine', cluster: 'engine.core',
  },

  // ─── Forward Engine: LNL Layer ─────────────────────────────────────
  {
    id: 'engine.lnl.persistent',
    name: 'Persistent',
    summary: 'Persistent-goal proving: state → cache → backchain',
    files: ['lib/engine/lnl/persistent.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'engine', cluster: 'engine.lnl',
  },
  {
    id: 'engine.lnl.loli',
    name: 'Loli',
    summary: 'Dynamic rule matching for linear implications',
    files: ['lib/engine/lnl/loli.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'engine', cluster: 'engine.lnl',
  },
  {
    id: 'engine.lnl.loli-drain',
    name: 'Loli Drain',
    summary: 'Persistent-trigger loli drain (generic)',
    files: ['lib/engine/lnl/loli-drain.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['execute'], modes: ['forward'],
    deepDive: 'engine', cluster: 'engine.lnl',
  },
  {
    id: 'engine.lnl.existential',
    name: 'Existential',
    summary: '∃-variable resolution in linear contexts',
    files: ['lib/engine/lnl/existential.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'engine', cluster: 'engine.lnl',
  },

  // ─── Forward Engine: Optimization Layer ────────────────────────────
  {
    id: 'engine.opt.compiled-clauses',
    name: 'Compiled Clauses',
    summary: 'Tier-1 dispatch: zero-subgoal → direct lookup',
    files: ['lib/engine/opt/compiled-clauses.js'],
    trust: 'optimization', specificity: 'framework',
    stages: ['compile', 'execute'], modes: ['forward', 'symbolic'],
    deepDive: 'optimization', cluster: 'engine.opt',
  },
  {
    id: 'engine.opt.existential-compile',
    name: 'Existential Compile',
    summary: 'Per-goal FFI fast-path for ∃-resolution',
    files: ['lib/engine/opt/existential-compile.js'],
    trust: 'optimization', specificity: 'framework',
    stages: ['compile', 'execute'], modes: ['forward', 'symbolic'],
    deepDive: 'optimization', cluster: 'engine.opt',
  },
  {
    id: 'engine.opt.ffi',
    name: 'FFI Opt',
    summary: 'State → FFI → compiled clause → full resolution',
    files: ['lib/engine/opt/ffi.js'],
    trust: 'optimization', specificity: 'framework',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'optimization', cluster: 'engine.opt',
  },
  {
    id: 'engine.opt.fingerprint',
    name: 'Fingerprint',
    summary: 'First-argument fingerprint indexing for rule selection',
    files: ['lib/engine/opt/fingerprint.js'],
    trust: 'optimization', specificity: 'framework',
    stages: ['compile', 'execute'], modes: ['forward', 'symbolic'],
    deepDive: 'optimization', cluster: 'engine.opt',
  },
  {
    id: 'engine.opt.prediction',
    name: 'Prediction',
    summary: 'Rule applicability pre-filter before full match',
    files: ['lib/engine/opt/prediction.js'],
    trust: 'optimization', specificity: 'framework',
    stages: ['execute'], modes: ['forward'],
    deepDive: 'optimization', cluster: 'engine.opt',
  },
  {
    id: 'engine.opt.structural-memo',
    name: 'Structural Memo',
    summary: 'Control-hash → subtree skip for explore',
    files: ['lib/engine/opt/structural-memo.js'],
    trust: 'optimization', specificity: 'framework',
    stages: ['execute'], modes: ['symbolic'],
    deepDive: 'optimization', cluster: 'engine.opt',
  },

  // ─── Forward Engine: ILL Layer (logic) ─────────────────────────────
  {
    id: 'engine.ill.calculus-config',
    name: 'Calculus Config',
    summary: 'ILL layered config (L0–L6) — single assembly point',
    files: ['lib/engine/ill/calculus-config.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['define', 'compile'], modes: ['forward', 'symbolic'],
    deepDive: 'engine', cluster: 'engine.ill',
  },
  {
    id: 'engine.ill.backchain-ill',
    name: 'Backchain ILL',
    summary: 'ILL-specific backchainer defaults (explicit initILL)',
    files: ['lib/engine/ill/backchain-ill.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['execute'], modes: ['backward'],
    deepDive: 'engine', cluster: 'engine.ill',
  },
  {
    id: 'engine.ill.binlit-theory',
    name: 'Binlit Theory',
    summary: 'Equational theory: binlit ↔ i/o/e (binary arithmetic)',
    files: ['lib/engine/ill/binlit-theory.js'],
    trust: 'infrastructure', specificity: 'theory',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'applications', cluster: 'engine.ill',
  },
  {
    id: 'engine.ill.bytecode-normalize',
    name: 'Bytecode Normalize',
    summary: 'EVM bytecode → trie / arrlit / semantic',
    files: ['lib/engine/ill/bytecode-normalize.js'],
    trust: 'infrastructure', specificity: 'program',
    stages: ['parse'], modes: ['forward', 'symbolic'],
    deepDive: 'applications', cluster: 'engine.ill',
  },
  {
    id: 'engine.ill.connectives',
    name: 'ILL Connectives',
    summary: 'Connective table: ⊗, ⊸, !, &, ⊕, ∃, ∀, {·}',
    files: ['lib/engine/ill/connectives.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['define', 'parse'], modes: ['backward', 'forward'],
    deepDive: 'engine', cluster: 'engine.ill',
  },
  {
    id: 'engine.ill.ffi',
    name: 'FFI Modules',
    summary: 'Arithmetic + memory primitives (binlit, sha3, memory, arrlit)',
    files: ['lib/engine/ill/ffi/'],
    trust: 'optimization', specificity: 'theory',
    stages: ['execute'], modes: ['forward', 'symbolic'],
    deepDive: 'optimization', cluster: 'engine.ill',
  },

  // ─── Parser System ─────────────────────────────────────────────────
  {
    id: 'parser.earley',
    name: 'Earley Core',
    summary: 'Recognizer + chart + extraction; shared across 3 paths',
    files: ['lib/parser/earley.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['parse'], modes: ['backward', 'forward', 'symbolic'],
    deepDive: 'parser', cluster: 'parser',
  },
  {
    id: 'parser.earley-grammar',
    name: 'Earley Grammar',
    summary: 'Generates BNF from .calc annotations (opt-in extensions)',
    files: ['lib/parser/earley-grammar.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['parse'], modes: ['backward', 'forward'],
    deepDive: 'parser', cluster: 'parser',
  },
  {
    id: 'parser.declarations',
    name: 'Declarations',
    summary: 'Extracts type/grammar/role decls from .calc files',
    files: ['lib/parser/declarations.js'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['parse'], modes: ['backward', 'forward'],
    deepDive: 'parser', cluster: 'parser',
  },
  {
    id: 'parser.sequent',
    name: 'Sequent Parser',
    summary: 'Parses sequent notation (antecedent ⊢ succedent)',
    files: ['lib/parser/sequent-parser.js'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['parse'], modes: ['backward'],
    deepDive: 'parser', cluster: 'parser',
  },
  {
    id: 'parser.meta',
    name: 'Meta Parser',
    summary: '@extends chain resolution over .calc hierarchies',
    files: ['lib/meta-parser/'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['parse'], modes: ['backward', 'forward'],
    deepDive: 'parser', cluster: 'parser',
  },
  {
    id: 'parser.rules',
    name: 'Rules Parser',
    summary: '.rules file parser (sequent notation → descriptors)',
    files: ['lib/rules/'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['parse', 'compile'], modes: ['backward'],
    deepDive: 'parser', cluster: 'parser',
  },

  // ─── Calculus / Applications ───────────────────────────────────────
  {
    id: 'calc.ill',
    name: 'ILL Calculus',
    summary: 'Intuitionistic Linear Logic: .calc + .rules + prelude',
    files: ['calculus/ill/'],
    trust: 'infrastructure', specificity: 'logic',
    stages: ['define'], modes: ['backward', 'forward'],
    deepDive: 'applications', cluster: 'applications',
  },
  {
    id: 'calc.ill.bin',
    name: 'Binary Arithmetic',
    summary: 'Bounded naturals, arithmetic, comparison',
    files: ['calculus/ill/programs/'],
    trust: 'infrastructure', specificity: 'theory',
    stages: ['define'], modes: ['backward', 'forward'],
    deepDive: 'applications', cluster: 'applications',
  },
  {
    id: 'calc.ill.evm',
    name: 'EVM Model',
    summary: 'Stack + memory + storage + PC; full EVM small-step',
    files: ['calculus/ill/programs/evm/'],
    trust: 'infrastructure', specificity: 'program',
    stages: ['define'], modes: ['forward', 'symbolic'],
    deepDive: 'applications', cluster: 'applications',
  },
  {
    id: 'calc.ill.multisig',
    name: 'Multisig',
    summary: 'Concrete + symbolic multisig contract verification',
    files: ['calculus/ill/programs/multisig/'],
    trust: 'infrastructure', specificity: 'instance',
    stages: ['define'], modes: ['symbolic'],
    deepDive: 'applications', cluster: 'applications',
  },

  // ─── ZK Certification ──────────────────────────────────────────────
  {
    id: 'zk.sequent-certifier',
    name: 'Sequent Certifier',
    summary: 'Proof term → Plonky3 witness via 14 buses + custom chips',
    files: ['zk/sequent-certifier/'],
    trust: 'infrastructure', specificity: 'framework',
    stages: ['certify'], modes: ['certification'],
    deepDive: 'zk', cluster: 'zk',
  },
  {
    id: 'zk.chips',
    name: 'ZK Chips',
    summary: 'Rule, binlit, sha3, memory, arrlit chips + custom chips',
    files: ['zk/sequent-certifier/chips/'],
    trust: 'infrastructure', specificity: 'theory',
    stages: ['certify'], modes: ['certification'],
    deepDive: 'zk', cluster: 'zk',
  },

  // ─── UI / Presentation ─────────────────────────────────────────────
  {
    id: 'ui.app',
    name: 'Web UI',
    summary: 'SolidJS + Tailwind; Sandbox, Prove, Calculus, Docs, Overview',
    files: ['src/ui/'],
    trust: 'ui', specificity: 'framework',
    stages: ['present'], modes: ['backward', 'forward', 'symbolic'],
    deepDive: 'applications', cluster: 'ui',
  },
  {
    id: 'ui.browser',
    name: 'Browser API',
    summary: 'Bundled runtime: parseFormula, render, getCalculus',
    files: ['lib/browser.js', 'out/ill.json'],
    trust: 'ui', specificity: 'framework',
    stages: ['present'], modes: ['backward', 'forward'],
    deepDive: 'applications', cluster: 'ui',
  },
];

/** Fast id → component index (O(1) lookup for cross-view linking). */
export const COMPONENT_BY_ID: Map<string, Component> =
  new Map(COMPONENTS.map(c => [c.id, c]));

export function getComponent(id: string): Component | undefined {
  return COMPONENT_BY_ID.get(id);
}

/** Filter helpers — keep views terse. */
export function componentsByDeepDive(dive: string): Component[] {
  return COMPONENTS.filter(c => c.deepDive === dive);
}
export function componentsByCluster(cluster: string): Component[] {
  return COMPONENTS.filter(c => c.cluster === cluster);
}
export function componentsByTrust(trust: string): Component[] {
  return COMPONENTS.filter(c => c.trust === trust);
}
