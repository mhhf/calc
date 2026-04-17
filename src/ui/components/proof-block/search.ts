/**
 * Search index for proof-tree/v1 — exact substring by default, regex via
 * `/pattern/` (leading slash escape). Pure function of (tree, query).
 *
 * Design choice: substring over fuzzy.
 *
 *   Fuzzy matching (Smith-Waterman, fzf-style) shines on filenames and
 *   symbol names, where users know roughly what they want but misremember
 *   the exact identifier. Proof terms are not like that — they're made of
 *   formal operators (`*`, `-o`, `&`, `!`), numeric indices, and fully
 *   qualified rule names. Fuzzy scoring treats every character as fungible
 *   and scatters false positives across a 500-node tree. Exact substring
 *   is predictable, zero-config, and pairs with the `/regex/` escape for
 *   the rare power-user query ("all `plus/*` rules with result > 7").
 *
 * Output:
 *   matches    — nodes whose rule or rendered sequent contains the query
 *   ancestors  — transitive parents of any match; force-expand these so
 *                matches are never hidden behind a fold-stub
 *   first      — the pre-order-first matching node id, for scroll-into-view
 *
 * Empty / invalid query → empty sets. Callers should bail out early when
 * both sets are empty (layouts skip highlight + force-expand).
 */
import type { ProofNode, ProofTreeV1 } from './types';
import { renderSequent } from './formula';

export interface SearchIndex {
  matches: Set<string>;
  ancestors: Set<string>;
  first: string | null;
  count: number;
  error: string | null;
}

export const EMPTY_SEARCH: SearchIndex = {
  matches: new Set(),
  ancestors: new Set(),
  first: null,
  count: 0,
  error: null,
};

/** Parse `/pattern/flags` into a RegExp; throw on bad regex. */
function parseRegex(q: string): RegExp {
  const m = q.match(/^\/(.*)\/([gimsuy]*)$/);
  if (!m) return new RegExp(q, 'i'); // bare `/foo` still works as regex
  return new RegExp(m[1], m[2] || 'i');
}

export function buildSearch(tree: ProofTreeV1, query: string): SearchIndex {
  const q = query.trim();
  if (!q) return EMPTY_SEARCH;

  // `/`-prefixed → regex mode; otherwise case-insensitive substring.
  const regex = q.startsWith('/');
  let test: (s: string) => boolean;
  try {
    if (regex) {
      const re = parseRegex(q);
      test = (s) => re.test(s);
    } else {
      const needle = q.toLowerCase();
      test = (s) => s.toLowerCase().includes(needle);
    }
  } catch (e: any) {
    return { ...EMPTY_SEARCH, error: e.message || String(e) };
  }

  const matches = new Set<string>();
  const ancestors = new Set<string>();
  let first: string | null = null;
  const pool = tree.formulas;

  // Pre-order walk — first match in reading order becomes `first`.
  function walk(node: ProofNode, chain: string[]): boolean {
    const haystack =
      (node.rule || '') + '\n' + renderSequent(node.sequent, pool);
    let selfHit = false;
    try {
      selfHit = test(haystack);
    } catch {
      selfHit = false;
    }
    if (selfHit) {
      matches.add(node.id);
      if (!first) first = node.id;
    }
    let descHit = false;
    if (node.premises.length > 0) {
      chain.push(node.id);
      for (const p of node.premises) {
        if (walk(p, chain)) descHit = true;
      }
      chain.pop();
    }
    if (selfHit || descHit) {
      for (const a of chain) ancestors.add(a);
      return true;
    }
    return false;
  }

  walk(tree.root, []);
  return { matches, ancestors, first, count: matches.size, error: null };
}
