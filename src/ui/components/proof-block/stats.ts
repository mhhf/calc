/**
 * Per-subtree stats for a proof-tree/v1 tree.
 *
 * Walks the tree once, bottom-up, and returns a Map keyed by node.id to the
 * stats for the subtree rooted at that node. Used by:
 *   - fold-stubs to label collapsed branches with their size/depth
 *   - rule-chip tooltips to reveal subtree shape on hover
 *   - "jump to largest subtree" UI (future)
 *
 * Pure function of the tree. Recomputed on tree change, not layout change.
 */
import type { ProofNode } from './types';

export interface SubtreeStats {
  /** Total number of proof nodes in the subtree, including the root. */
  nodes: number;
  /** Longest root-to-leaf path length in the subtree (this node counts as 1). */
  depth: number;
  /** Max premise count across all nodes in the subtree (1 = linear). */
  branching: number;
  /** Number of leaves (nodes with no premises) in the subtree. */
  leaves: number;
}

export type StatsMap = Map<string, SubtreeStats>;

export function computeStats(root: ProofNode): StatsMap {
  const out: StatsMap = new Map();
  visit(root, out);
  return out;
}

function visit(node: ProofNode, out: StatsMap): SubtreeStats {
  let nodes = 1;
  let depth = 1;
  let branching = node.premises.length;
  let leaves = node.premises.length === 0 ? 1 : 0;
  for (const p of node.premises) {
    const sub = visit(p, out);
    nodes += sub.nodes;
    depth = Math.max(depth, sub.depth + 1);
    branching = Math.max(branching, sub.branching);
    leaves += sub.leaves;
  }
  const stats = { nodes, depth, branching, leaves };
  out.set(node.id, stats);
  return stats;
}

/** Short human-readable badge: `42 · ↓7` (42 nodes, depth 7). */
export function badge(stats: SubtreeStats | undefined): string {
  if (!stats) return '';
  return `${stats.nodes} · ↓${stats.depth}`;
}

/** Longer tooltip: `42 nodes · depth 7 · branching 2 · 15 leaves`. */
export function tooltip(stats: SubtreeStats | undefined): string {
  if (!stats) return '';
  return `${stats.nodes} nodes · depth ${stats.depth} · branching ${stats.branching} · ${stats.leaves} leaves`;
}
