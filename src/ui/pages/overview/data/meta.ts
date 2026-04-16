/**
 * Metadata for the four axis views and seven deep dives.
 * Sub-nav, landing cards, and page headers all read from here.
 */

import type { DeepDiveMeta, ViewMeta } from './types';

export const VIEWS: ViewMeta[] = [
  {
    id: 'trust',
    slug: 'trust',
    title: 'Trust Stack',
    question: 'What if this code has a bug?',
    blurb: 'Two parallel genuine stacks on a shared foundation; kernel is the trust anchor.',
    glyph: '⬣',
  },
  {
    id: 'specificity',
    slug: 'specificity',
    title: 'Specificity Tree',
    question: 'How domain-specific is this code?',
    blurb: 'Framework → Logic → Theory → Program → Instance. Strategies and optimizations at every level.',
    glyph: '◆',
  },
  {
    id: 'pipeline',
    slug: 'pipeline',
    title: 'Pipeline',
    question: 'When does this code run?',
    blurb: 'Define → Parse → Compile → Execute → Certify → Present. Fusion-symex is a gradient, not a boundary.',
    glyph: '▸',
  },
  {
    id: 'atlas',
    slug: 'atlas',
    title: 'Component Atlas',
    question: 'Where is X? What properties does it have?',
    blurb: 'Searchable, filterable, sortable index of every component.',
    glyph: '☰',
  },
];

export const DEEP_DIVES: DeepDiveMeta[] = [
  {
    id: 'prover',
    slug: 'prover',
    title: 'Backward Prover',
    oneLiner: 'Kernel → Generic → Focused → Strategy',
    blurb: 'Genuine 4-layer stack: each layer adds search discipline on top of a verified kernel.',
    glyph: '⊢',
  },
  {
    id: 'engine',
    slug: 'engine',
    title: 'Forward Engine',
    oneLiner: 'Stackified 3-layer: Generic Core → LNL → ILL',
    blurb: 'matchOpts composition via 4 frozen protocol factories; strategy stack; optimization injection.',
    glyph: '↠',
  },
  {
    id: 'compilation',
    slug: 'compilation',
    title: 'Compilation Pipeline',
    oneLiner: 'Parse → Compile → Compose → Assemble → Runtime → Certify',
    blurb: 'Fusion-symex spectrum: grade-0 → BB fusion → chain → SROA → symbolic exec.',
    glyph: '⇝',
  },
  {
    id: 'optimization',
    slug: 'optimization',
    title: 'Optimization',
    oneLiner: 'Six cross-cutting modules; profile matrix (bare/fast/evm)',
    blurb: 'Optimizations wrap() lower-layer functions — not a stack layer.',
    glyph: '⚙',
  },
  {
    id: 'zk',
    slug: 'zk',
    title: 'ZK Certification',
    oneLiner: 'Proof term → 14 buses → Plonky3 chips',
    blurb: 'Tree and flat paths; custom chips; witness → verification.',
    glyph: '◊',
  },
  {
    id: 'parser',
    slug: 'parser',
    title: 'Parser System',
    oneLiner: 'Three paths through one Earley',
    blurb: 'Meta, program, rule — one engine, opt-in grammar extensions.',
    glyph: '⟂',
  },
  {
    id: 'applications',
    slug: 'applications',
    title: 'Applications',
    oneLiner: 'ILL → binary arithmetic → EVM → multisig',
    blurb: 'Execution modes (concrete vs symbolic). EVM state evolution. Program specificity.',
    glyph: '◉',
  },
];
