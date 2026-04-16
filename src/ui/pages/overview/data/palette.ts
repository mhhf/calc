/**
 * Shared color palette for axis views.
 *
 * Trust coloring (green → yellow → orange → gray) is the canonical
 * cross-view identity — the same component wears the same color in every
 * view. Specificity and pipeline use independent but complementary palettes
 * so that filter-by-spec / filter-by-stage does not collide with trust.
 */

import type { Trust, Specificity, Stage, Mode, DeepDive } from './types';

/** Base trust palette — used as the primary color identity in all views. */
export const TRUST_COLORS: Record<Trust, { bg: string; border: string; text: string; dot: string; label: string; rank: number }> = {
  kernel: {
    bg: 'bg-emerald-50 dark:bg-emerald-900/25',
    border: 'border-emerald-400 dark:border-emerald-600',
    text: 'text-emerald-800 dark:text-emerald-200',
    dot: 'bg-emerald-500',
    label: 'Kernel',
    rank: 0,
  },
  infrastructure: {
    bg: 'bg-amber-50 dark:bg-amber-900/25',
    border: 'border-amber-400 dark:border-amber-600',
    text: 'text-amber-800 dark:text-amber-200',
    dot: 'bg-amber-500',
    label: 'Infrastructure',
    rank: 1,
  },
  optimization: {
    bg: 'bg-orange-50 dark:bg-orange-900/25',
    border: 'border-orange-400 dark:border-orange-600',
    text: 'text-orange-800 dark:text-orange-200',
    dot: 'bg-orange-500',
    label: 'Optimization',
    rank: 2,
  },
  ui: {
    bg: 'bg-gray-50 dark:bg-gray-800/50',
    border: 'border-gray-300 dark:border-gray-600',
    text: 'text-gray-700 dark:text-gray-300',
    dot: 'bg-gray-400',
    label: 'Presentation',
    rank: 3,
  },
};

/** Specificity palette — blue gradient (more generic → deeper blue). */
export const SPECIFICITY_COLORS: Record<Specificity, { bg: string; border: string; text: string; label: string; rank: number }> = {
  framework: {
    bg: 'bg-sky-50 dark:bg-sky-900/20',
    border: 'border-sky-300 dark:border-sky-700',
    text: 'text-sky-800 dark:text-sky-200',
    label: 'Framework',
    rank: 0,
  },
  logic: {
    bg: 'bg-indigo-50 dark:bg-indigo-900/20',
    border: 'border-indigo-300 dark:border-indigo-700',
    text: 'text-indigo-800 dark:text-indigo-200',
    label: 'Logic (ILL)',
    rank: 1,
  },
  theory: {
    bg: 'bg-violet-50 dark:bg-violet-900/20',
    border: 'border-violet-300 dark:border-violet-700',
    text: 'text-violet-800 dark:text-violet-200',
    label: 'Theory',
    rank: 2,
  },
  program: {
    bg: 'bg-fuchsia-50 dark:bg-fuchsia-900/20',
    border: 'border-fuchsia-300 dark:border-fuchsia-700',
    text: 'text-fuchsia-800 dark:text-fuchsia-200',
    label: 'Program',
    rank: 3,
  },
  instance: {
    bg: 'bg-pink-50 dark:bg-pink-900/20',
    border: 'border-pink-300 dark:border-pink-700',
    text: 'text-pink-800 dark:text-pink-200',
    label: 'Instance',
    rank: 4,
  },
};

/** Pipeline stages — left-to-right gradient for swim lanes. */
export const STAGE_COLORS: Record<Stage, { bg: string; border: string; text: string; label: string; order: number }> = {
  define:  { bg: 'bg-slate-100 dark:bg-slate-800',       border: 'border-slate-300 dark:border-slate-600', text: 'text-slate-800 dark:text-slate-200', label: 'Define',  order: 0 },
  parse:   { bg: 'bg-teal-100 dark:bg-teal-900/40',      border: 'border-teal-300 dark:border-teal-700',   text: 'text-teal-800 dark:text-teal-200',   label: 'Parse',   order: 1 },
  compile: { bg: 'bg-cyan-100 dark:bg-cyan-900/40',      border: 'border-cyan-300 dark:border-cyan-700',   text: 'text-cyan-800 dark:text-cyan-200',   label: 'Compile', order: 2 },
  execute: { bg: 'bg-blue-100 dark:bg-blue-900/40',      border: 'border-blue-300 dark:border-blue-700',   text: 'text-blue-800 dark:text-blue-200',   label: 'Execute', order: 3 },
  certify: { bg: 'bg-purple-100 dark:bg-purple-900/40',  border: 'border-purple-300 dark:border-purple-700', text: 'text-purple-800 dark:text-purple-200', label: 'Certify', order: 4 },
  present: { bg: 'bg-rose-100 dark:bg-rose-900/30',      border: 'border-rose-300 dark:border-rose-700',   text: 'text-rose-800 dark:text-rose-200',   label: 'Present', order: 5 },
};

export const MODE_LABEL: Record<Mode, string> = {
  backward: 'Backward',
  forward: 'Forward',
  symbolic: 'Symbolic',
  certification: 'Certification',
};

/** Deep-dive icon color for sub-nav + landing cards. */
export const DEEPDIVE_ACCENT: Record<DeepDive, string> = {
  prover: 'text-emerald-600 dark:text-emerald-400',
  engine: 'text-amber-600 dark:text-amber-400',
  compilation: 'text-cyan-600 dark:text-cyan-400',
  optimization: 'text-orange-600 dark:text-orange-400',
  zk: 'text-purple-600 dark:text-purple-400',
  parser: 'text-teal-600 dark:text-teal-400',
  applications: 'text-fuchsia-600 dark:text-fuchsia-400',
};
