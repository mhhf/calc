/**
 * ZK Certification deep dive.
 *
 * The sequent-certifier takes a proof term and produces a Plonky3 STARK
 * witness. It is wired through 14 shared buses (some Permutation, some
 * Lookup) that let chips exchange values without direct coupling.
 *
 * Chips split into two families:
 *   - Framework chips (rule dispatch, fact axiom, ctx boundary, discard, dup,
 *     subst, canonical cons) — shared across any calculus.
 *   - ROM / FFI chips (byte-check, canon-cons ROM, freevar ROM, gamma ROM,
 *     fact ROM, pred ROM, formula ROM, simple ROM, uint256 arith) — verify
 *     theory and program semantics.
 *
 * The page renders:
 *   - the 14-bus table (permutation vs lookup + role)
 *   - the chip catalogue grouped by family
 *   - witness paths: tree vs flat
 *   - the "we never re-implement the prover" property
 */

import { For } from 'solid-js';
import { useHashComponent } from './blocks/useHashComponent';
import Page from './blocks/Page';
import SectionCard from './blocks/SectionCard';
import DetailPanel from './blocks/DetailPanel';
import ComponentBox from './blocks/ComponentBox';
import { DEEP_DIVES } from './data/meta';
import { DEEPDIVE_ACCENT } from './data/palette';
import { getComponent } from './data/components';
import type { Component } from './data/types';

interface Bus {
  id: number;
  name: string;
  kind: 'permutation' | 'lookup';
  role: string;
}

const BUSES: Bus[] = [
  { id: 0,  name: 'OBLIG_BUS',         kind: 'permutation', role: 'Obligation multiset — premises of each rule invocation' },
  { id: 1,  name: 'CONTEXT_BUS',       kind: 'permutation', role: 'Linear context (Γ) across rule steps' },
  { id: 2,  name: 'FORMULA_BUS',       kind: 'lookup',      role: 'Formula interning — map hashes to canonical forms' },
  { id: 3,  name: 'DISCARD_BUS',       kind: 'lookup',      role: 'Discard traffic (weakening on !, 0L)' },
  { id: 4,  name: 'GAMMA_BUS',         kind: 'lookup',      role: 'Γ (persistent context) entries' },
  { id: 5,  name: 'SUBST_TREE_BUS',    kind: 'permutation', role: 'Substitution tree — binder boundaries and consumption' },
  { id: 6,  name: 'FREEVAR_BUS',       kind: 'lookup',      role: 'Free-variable membership under binder' },
  { id: 7,  name: 'CANON_CONS_BUS',    kind: 'lookup',      role: 'Canonical cons list encoding' },
  { id: 8,  name: 'FACT_BUS',          kind: 'lookup',      role: 'Fact axioms (grade-0 persistent facts)' },
  { id: 9,  name: 'PRED_BUS',          kind: 'lookup',      role: 'Predicate head → rule dispatch' },
  { id: 10, name: 'BYTE_CHECK_BUS',    kind: 'lookup',      role: 'Byte-range check (0..256) for uint256 arithmetic' },
  { id: 11, name: 'OBLIG_PV_BIND_BUS', kind: 'permutation', role: 'Obligation-side PV binding (proof variable scope)' },
  { id: 12, name: 'CTX_PV_BIND_BUS',   kind: 'permutation', role: 'Context-side PV binding' },
  { id: 13, name: 'FLAT_PV_BIND_BUS',  kind: 'permutation', role: 'Flat-path PV binding (tree / flat duality)' },
];

interface Chip { name: string; role: string; family: 'framework' | 'rom' | 'arith' | 'path' }
const CHIPS: Chip[] = [
  { name: 'init',              family: 'framework', role: 'Root sequent; seeds OBLIG / CONTEXT' },
  { name: 'fact_axiom',        family: 'framework', role: 'Verifies one axiom leaf against FACT_BUS' },
  { name: 'ctx_boundary',      family: 'framework', role: 'Context multiplicity check across rule boundaries' },
  { name: 'oblig_boundary',    family: 'framework', role: 'Obligation boundary — premises → conclusion' },
  { name: 'discard',           family: 'framework', role: 'Explicit weakening via DISCARD_BUS' },
  { name: 'dup',               family: 'framework', role: 'Bang duplication (!A ⊸ !A * !A)' },
  { name: 'subst',             family: 'framework', role: 'Capture-avoiding substitution check' },
  { name: 'zero_l',            family: 'framework', role: 'Left rule for 0 — discards the linear context' },
  { name: 'canon_cons_rom',    family: 'rom',       role: 'Canonical cons encoding lookup' },
  { name: 'fact_rom',          family: 'rom',       role: 'Fact axioms ROM for grade-0 persistent facts' },
  { name: 'formula_rom',       family: 'rom',       role: 'Formula → hash canonicalization ROM' },
  { name: 'freevar_rom',       family: 'rom',       role: 'Free-variable table' },
  { name: 'gamma_rom',         family: 'rom',       role: 'Persistent context lookup' },
  { name: 'pred_rom',          family: 'rom',       role: 'Predicate → rule descriptor lookup' },
  { name: 'simple_rom',        family: 'rom',       role: 'Generic key → value constant tables' },
  { name: 'byte_check_rom',    family: 'rom',       role: 'Byte-range (0..256) lookup' },
  { name: 'uint256_arith',     family: 'arith',     role: 'Full uint256 add/sub/mul/mod (for EVM)' },
  { name: 'flat_init',         family: 'path',      role: 'Flat-path root (linearized proof tree)' },
  { name: 'flat_step',         family: 'path',      role: 'Flat-path step (one rule application)' },
  { name: 'flat_final',        family: 'path',      role: 'Flat-path terminator' },
];

const FAMILIES: { id: Chip['family']; title: string; blurb: string }[] = [
  { id: 'framework', title: 'Framework chips',  blurb: 'Rule dispatch, axioms, boundaries. Shared across any calculus.' },
  { id: 'rom',       title: 'ROM chips',        blurb: 'Read-only memories — canonical lookups that encode static semantic data.' },
  { id: 'arith',     title: 'Arithmetic chips', blurb: 'Theory-level chips that verify FFI arithmetic (binlit, uint256).' },
  { id: 'path',      title: 'Path chips',       blurb: 'Tree vs flat witness-path modes. Tree is natural, flat is a linearization for shorter proofs.' },
];

function BusTable() {
  return (
    <div class="overflow-x-auto rounded border border-gray-200 dark:border-gray-700">
      <table class="w-full text-xs">
        <thead class="bg-gray-50 dark:bg-gray-900/40 border-b border-gray-200 dark:border-gray-700">
          <tr class="text-left">
            <th class="py-2 pl-3 pr-2 font-semibold text-gray-700 dark:text-gray-300 w-10">#</th>
            <th class="py-2 pr-3 font-semibold text-gray-700 dark:text-gray-300">Bus</th>
            <th class="py-2 pr-3 font-semibold text-gray-700 dark:text-gray-300">Kind</th>
            <th class="py-2 pr-3 font-semibold text-gray-700 dark:text-gray-300">Role</th>
          </tr>
        </thead>
        <tbody>
          <For each={BUSES}>
            {(b) => (
              <tr class="border-t border-gray-100 dark:border-gray-800">
                <td class="py-1.5 pl-3 pr-2 font-mono text-gray-500 dark:text-gray-400">{b.id}</td>
                <td class="py-1.5 pr-3 font-mono text-purple-700 dark:text-purple-300">{b.name}</td>
                <td class="py-1.5 pr-3">
                  <span class={`inline-flex items-center rounded px-1.5 py-0.5 text-[10px] font-medium border ${
                    b.kind === 'permutation'
                      ? 'bg-purple-50 text-purple-800 border-purple-200 dark:bg-purple-900/20 dark:text-purple-300 dark:border-purple-700'
                      : 'bg-fuchsia-50 text-fuchsia-800 border-fuchsia-200 dark:bg-fuchsia-900/20 dark:text-fuchsia-300 dark:border-fuchsia-700'
                  }`}>
                    {b.kind}
                  </span>
                </td>
                <td class="py-1.5 pr-3 text-gray-700 dark:text-gray-300 leading-snug">{b.role}</td>
              </tr>
            )}
          </For>
        </tbody>
      </table>
    </div>
  );
}

function TreeVsFlat() {
  return (
    <svg viewBox="0 0 1000 220" class="w-full max-w-4xl mx-auto" role="img" aria-label="Tree vs flat witness paths">
      <defs>
        <marker id="zk-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto-start-reverse">
          <path d="M 0 0 L 8 4 L 0 8 z" fill="currentColor" />
        </marker>
      </defs>
      {/* Tree path */}
      <g class="text-purple-700 dark:text-purple-400">
        <text x="130" y="20" text-anchor="middle" font-size="12" font-weight="700" class="fill-current">Tree path</text>
        <circle cx="130" cy="50" r="12" class="fill-purple-100 dark:fill-purple-900/40 stroke-current" stroke-width="1.5" />
        <text x="130" y="54" text-anchor="middle" font-size="10" class="fill-current">R</text>
        <line x1="130" y1="62" x2="80" y2="88" stroke="currentColor" stroke-width="1" />
        <line x1="130" y1="62" x2="180" y2="88" stroke="currentColor" stroke-width="1" />
        <circle cx="80" cy="100" r="10" class="fill-purple-100 dark:fill-purple-900/40 stroke-current" />
        <circle cx="180" cy="100" r="10" class="fill-purple-100 dark:fill-purple-900/40 stroke-current" />
        <line x1="80" y1="110" x2="50" y2="138" stroke="currentColor" stroke-width="1" />
        <line x1="80" y1="110" x2="110" y2="138" stroke="currentColor" stroke-width="1" />
        <line x1="180" y1="110" x2="210" y2="138" stroke="currentColor" stroke-width="1" />
        <circle cx="50" cy="148" r="8" class="fill-purple-100 dark:fill-purple-900/40 stroke-current" />
        <circle cx="110" cy="148" r="8" class="fill-purple-100 dark:fill-purple-900/40 stroke-current" />
        <circle cx="210" cy="148" r="8" class="fill-purple-100 dark:fill-purple-900/40 stroke-current" />
        <text x="130" y="190" text-anchor="middle" font-size="10" class="fill-gray-600 dark:fill-gray-400">
          Natural proof tree. Per-node chip rows.
        </text>
      </g>
      {/* Arrow */}
      <g class="text-gray-500 dark:text-gray-400">
        <path d="M 270 120 L 400 120" fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#zk-arrow)" />
        <text x="335" y="110" text-anchor="middle" font-size="10" class="fill-current">linearize</text>
      </g>
      {/* Flat path */}
      <g class="text-fuchsia-700 dark:text-fuchsia-400">
        <text x="700" y="20" text-anchor="middle" font-size="12" font-weight="700" class="fill-current">Flat path</text>
        <For each={[0, 1, 2, 3, 4, 5, 6]}>
          {(i) => {
            const x = 450 + i * 70;
            return (
              <>
                <rect x={x} y={90} width={55} height={30} rx={4} class="fill-fuchsia-100 dark:fill-fuchsia-900/40 stroke-current" stroke-width="1.5" />
                <text x={x + 27} y={108} text-anchor="middle" font-size="9" class="fill-current" font-family="ui-monospace">step_{i}</text>
                {i < 6 && <path d={`M ${x + 56} 105 L ${x + 69} 105`} fill="none" stroke="currentColor" stroke-width="1.2" marker-end="url(#zk-arrow)" />}
              </>
            );
          }}
        </For>
        <text x="700" y="150" text-anchor="middle" font-size="10" class="fill-gray-600 dark:fill-gray-400">
          Sequential steps bound by FLAT_PV_BIND_BUS.
        </text>
        <text x="700" y="170" text-anchor="middle" font-size="10" class="fill-gray-600 dark:fill-gray-400">
          Shorter proofs; tighter circuit.
        </text>
      </g>
    </svg>
  );
}

export default function Zk() {
  const meta = DEEP_DIVES.find(d => d.id === 'zk')!;
  const { selected, select } = useHashComponent();
  const setSelected = (c: Component | null) => select(c);

  const zkCert = getComponent('zk.sequent-certifier');
  const zkChips = getComponent('zk.chips');
  const byFamily = (f: Chip['family']) => CHIPS.filter(c => c.family === f);

  return (
    <Page
      glyph={meta.glyph}
      title={meta.title}
      subtitle="Proof term in, Plonky3 STARK out. 14 shared buses let chips exchange values; chips verify, they never re-execute."
      accentClass={DEEPDIVE_ACCENT.zk}
    >
      <SectionCard
        title="Entry points"
        subtitle="The certifier consumes a proof term produced by any CALC mode (backward, forward, symbolic) and emits a Plonky3 witness."
      >
        <div class="grid grid-cols-1 md:grid-cols-2 gap-2">
          {zkCert && <ComponentBox component={zkCert} onSelect={setSelected} selected={selected()?.id === zkCert.id} />}
          {zkChips && <ComponentBox component={zkChips} onSelect={setSelected} selected={selected()?.id === zkChips.id} />}
        </div>
      </SectionCard>

      <SectionCard
        title="14 shared buses"
        subtitle="Two bus kinds: permutation checks (multiset equality across chips) and lookups (key → value tables). Buses decouple chips from each other — a chip only sees the buses it subscribes to."
      >
        <BusTable />
      </SectionCard>

      <SectionCard
        title="Chip catalogue"
        subtitle="Chips verify small pieces of the sequent calculus. A proof of any length is a table of chip activations bound together by bus checks."
      >
        <div class="space-y-4">
          <For each={FAMILIES}>
            {(fam) => (
              <div>
                <header class="mb-2">
                  <h4 class="font-bold text-sm text-purple-800 dark:text-purple-200">{fam.title}</h4>
                  <p class="text-xs text-gray-600 dark:text-gray-400">{fam.blurb}</p>
                </header>
                <div class="grid grid-cols-1 sm:grid-cols-2 md:grid-cols-3 lg:grid-cols-4 gap-2">
                  <For each={byFamily(fam.id)}>
                    {(c) => (
                      <div class="rounded border border-purple-200 dark:border-purple-700 bg-purple-50 dark:bg-purple-900/15 p-2">
                        <div class="font-mono font-semibold text-purple-800 dark:text-purple-200 text-xs">{c.name}</div>
                        <div class="text-[11px] text-gray-700 dark:text-gray-300 mt-0.5 leading-snug">{c.role}</div>
                      </div>
                    )}
                  </For>
                </div>
              </div>
            )}
          </For>
        </div>
      </SectionCard>

      <SectionCard
        title="Tree vs flat witness paths"
        subtitle="Two encodings of the same proof. Tree keeps the natural shape; flat linearizes into a sequence of steps bound by PV-binding buses."
      >
        <TreeVsFlat />
      </SectionCard>

      <SectionCard
        title="Why ZK here (and not re-implementing the prover)"
        subtitle="A zkEVM replays execution inside a SNARK circuit. We do something different."
      >
        <div class="grid grid-cols-1 md:grid-cols-3 gap-3 text-sm">
          <div class="rounded border border-purple-200 dark:border-purple-700 bg-purple-50 dark:bg-purple-900/15 p-3">
            <div class="font-semibold text-purple-800 dark:text-purple-200">Chips verify rule application</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              Every step of the proof is one rule-chip activation. The chip checks the premises produce
              the conclusion — it does not re-run the search.
            </p>
          </div>
          <div class="rounded border border-purple-200 dark:border-purple-700 bg-purple-50 dark:bg-purple-900/15 p-3">
            <div class="font-semibold text-purple-800 dark:text-purple-200">FFI chips verify theory</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              binlit / uint256 / byte-check / sha3 chips confirm arithmetic + hashing results. They
              mirror the FFI predicates the forward engine uses.
            </p>
          </div>
          <div class="rounded border border-purple-200 dark:border-purple-700 bg-purple-50 dark:bg-purple-900/15 p-3">
            <div class="font-semibold text-purple-800 dark:text-purple-200">Per-contract, not per-trace</div>
            <p class="text-xs text-gray-700 dark:text-gray-300 mt-1">
              A certified symbolic execution covers ALL inputs (within the symbolic abstraction). One
              STARK per symbolic path; contract is verified by their union.
            </p>
          </div>
        </div>
      </SectionCard>

      <DetailPanel component={selected()} onClose={() => setSelected(null)} />
    </Page>
  );
}
