/**
 * Named vertical layers within each stack.
 *
 * The Trust Stack view places backward prover + forward engine side-by-side
 * as genuine stacks (enforced by tests/engine/layer-dag.test.js). Deep-dive
 * pages reuse the same layer definitions for their layer diagrams.
 */

import type { Layer } from './types';

export const LAYERS: Layer[] = [
  // ─── Backward prover — genuine stack (Kernel → Generic → Focused → Strategy)
  {
    id: 'prover.l4',
    name: 'L4 · Strategy',
    stack: 'prover',
    order: 0,
    trust: 'infrastructure',
    role: 'Manual (interactive) and auto (iterative deepening) search',
    componentIds: ['prover.strategy'],
  },
  {
    id: 'prover.l3',
    name: 'L3 · Focused',
    stack: 'prover',
    order: 1,
    trust: 'infrastructure',
    role: 'Andreoli focusing: alternating positive/negative phases',
    componentIds: ['prover.focused'],
  },
  {
    id: 'prover.l2',
    name: 'L2 · Generic',
    stack: 'prover',
    order: 2,
    trust: 'infrastructure',
    role: 'Search primitives + rule-interpreter bridge',
    componentIds: ['prover.generic', 'prover.rule-interpreter'],
  },
  {
    id: 'prover.l1',
    name: 'L1 · Kernel',
    stack: 'prover',
    order: 3,
    trust: 'kernel',
    role: 'Proof verification — re-derives every step from premises',
    componentIds: ['prover.kernel'],
  },

  // ─── Forward engine — genuine 3-layer stack (Generic Core → LNL → ILL) + cross-cutting opt
  {
    id: 'engine.ill',
    name: 'ILL',
    stack: 'engine',
    order: 0,
    trust: 'infrastructure',
    role: 'ILL-specific assembly: connectives, theories, FFI, backchain defaults',
    componentIds: [
      'engine.ill.calculus-config',
      'engine.ill.backchain-ill',
      'engine.ill.binlit-theory',
      'engine.ill.bytecode-normalize',
      'engine.ill.connectives',
      'engine.ill.ffi',
    ],
  },
  {
    id: 'engine.lnl',
    name: 'LNL',
    stack: 'engine',
    order: 1,
    trust: 'infrastructure',
    role: 'Linear + persistent distinction (loli, existential)',
    componentIds: [
      'engine.lnl.persistent',
      'engine.lnl.loli',
      'engine.lnl.loli-drain',
      'engine.lnl.existential',
    ],
  },
  {
    id: 'engine.core',
    name: 'Generic Core',
    stack: 'engine',
    order: 2,
    trust: 'infrastructure',
    role: 'Pattern matching, rule selection, exec/explore, compile, convert',
    componentIds: [
      'engine.match', 'engine.strategy', 'engine.forward', 'engine.explore',
      'engine.compile', 'engine.backchain', 'engine.fact-set',
      'engine.convert', 'engine.formula-utils',
    ],
  },

  // ─── Foundation layer shared by both stacks
  {
    id: 'foundation.kernel',
    name: 'Content-Addressed Store + Kernel Ops',
    stack: 'foundation',
    order: 0,
    trust: 'kernel',
    role: 'Hash-consed AST; unify; substitute; equational theories',
    componentIds: [
      'kernel.store', 'kernel.ast', 'kernel.sequent',
      'kernel.unify', 'kernel.substitute', 'kernel.eq-theory',
    ],
  },
];

/** Get layers in stack, ordered top → bottom. */
export function layersByStack(stack: string): Layer[] {
  return LAYERS.filter(l => l.stack === stack).sort((a, b) => a.order - b.order);
}
