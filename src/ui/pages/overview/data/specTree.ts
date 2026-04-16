/**
 * Specificity tree — hierarchical view of domain knowledge.
 *
 * Root is the calculus-agnostic framework. Each child adds a commitment:
 * a logic (ILL), a theory (binary arithmetic, strlit), a program (EVM),
 * an instance (multisig). Every node carries a specificity level plus
 * optional component id pointers for the Atlas / DetailPanel.
 */

import type { Specificity } from './types';

export interface SpecNode {
  id: string;
  name: string;
  summary: string;
  specificity: Specificity;
  /** Component ids living at this specificity level. */
  componentIds: string[];
  /** Strategies that exist specifically here (informal). */
  strategies?: string[];
  /** Optimizations that exist specifically here. */
  optimizations?: string[];
  /** ZK chips that exist specifically here. */
  chips?: string[];
  /** Future/planned indicator (rendered dim). */
  planned?: boolean;
  children?: SpecNode[];
}

export const SPEC_TREE: SpecNode = {
  id: 'root',
  name: 'CALC Framework',
  summary: 'Calculus-agnostic machinery: content-addressed store, Earley parser, focused prover core, forward-engine generic core',
  specificity: 'framework',
  componentIds: [
    'kernel.store', 'kernel.ast', 'kernel.sequent', 'kernel.unify', 'kernel.substitute',
    'prover.kernel', 'prover.generic', 'prover.strategy', 'prover.rule-interpreter',
    'engine.match', 'engine.strategy', 'engine.forward', 'engine.explore',
    'engine.compile', 'engine.backchain', 'engine.fact-set', 'engine.convert',
    'engine.formula-utils',
    'parser.earley', 'parser.earley-grammar', 'parser.declarations', 'parser.meta', 'parser.rules',
  ],
  strategies: ['Fingerprint indexing', 'Discrimination tree', 'Predicate filter (catch-all)'],
  optimizations: ['Fingerprint', 'Structural memo (explore)', 'Prediction'],
  chips: ['Rule chip (dispatch)'],
  children: [
    {
      id: 'ill',
      name: 'ILL',
      summary: 'Intuitionistic Linear Logic — connectives, polarities, focusing discipline',
      specificity: 'logic',
      componentIds: [
        'prover.focused', 'prover.bridge',
        'engine.lnl.persistent', 'engine.lnl.loli', 'engine.lnl.loli-drain', 'engine.lnl.existential',
        'engine.ill.calculus-config', 'engine.ill.backchain-ill', 'engine.ill.connectives',
        'parser.sequent',
        'calc.ill',
      ],
      strategies: ['Andreoli focusing (L3)', 'LNL persistent/linear split', 'Loli dynamic rules'],
      optimizations: ['Compiled clauses (opt)', 'Existential compile (opt)'],
      chips: ['Bang chip', 'Tensor chip', 'With chip', 'Oplus chip'],
      children: [
        {
          id: 'bin',
          name: 'Binary Arithmetic',
          summary: 'Bounded naturals + comparison + FFI acceleration. Theory of plus/times/eq/lt.',
          specificity: 'theory',
          componentIds: ['engine.ill.binlit-theory', 'engine.ill.ffi', 'calc.ill.bin'],
          strategies: ['binlit ↔ i/o/e normalization'],
          optimizations: ['FFI opt (state → FFI → compiled → clause)'],
          chips: ['Binlit chip (plus/times/eq/lt)'],
          children: [],
        },
        {
          id: 'strings',
          name: 'String / sha3',
          summary: 'String literals + Keccak-256 hashing. FFI-backed for speed.',
          specificity: 'theory',
          componentIds: [],
          strategies: ['strlit equational theory'],
          optimizations: ['FFI-accelerated sha3'],
          chips: ['Sha3 chip'],
          children: [],
        },
        {
          id: 'evm',
          name: 'EVM Model',
          summary: 'Stack + memory + storage + PC. Full EVM small-step semantics.',
          specificity: 'program',
          componentIds: ['engine.ill.bytecode-normalize', 'calc.ill.evm'],
          strategies: ['Program counter fingerprint', 'Opcode dispatch'],
          optimizations: ['Per-opcode FFI fast paths', 'Memory as arrlit'],
          chips: ['Memory chip', 'Arrlit chip', 'Custom opcode chips'],
          children: [
            {
              id: 'multisig',
              name: 'Multisig',
              summary: 'Concrete + symbolic multisig-contract verification. Chunked/tree/flat witness paths.',
              specificity: 'instance',
              componentIds: ['calc.ill.multisig'],
              strategies: ['Symbolic execution (explore)', 'Chunked witness'],
              optimizations: ['Structural memo (explore)'],
              chips: ['Custom chip (contract-specific)'],
              children: [],
            },
          ],
        },
      ],
    },
    {
      id: 'numal',
      name: 'NumAL',
      summary: 'Numerical/algebraic calculus (planned). Would live alongside ILL, sharing the framework.',
      specificity: 'logic',
      componentIds: [],
      planned: true,
      children: [],
    },
  ],
};
