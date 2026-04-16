/**
 * URL-hash-backed component selection.
 *
 * Every overview view reads + writes the selected component through the
 * window location hash, e.g. #comp=engine.match. This lets users:
 *   - share a link that opens a specific component's detail panel
 *   - navigate between views with the selection preserved (cross-view nav)
 *   - hit back/forward to undo/redo a selection
 *
 * Nothing ReactRouter-specific: we touch history.replaceState directly and
 * listen for 'hashchange' so that back-button + external nav still work.
 */

import { createSignal, onCleanup, onMount } from 'solid-js';
import type { Component } from '../data/types';
import { getComponent } from '../data/components';

const HASH_PREFIX = '#comp=';

function readHash(): Component | null {
  if (typeof window === 'undefined') return null;
  const h = window.location.hash;
  if (!h.startsWith(HASH_PREFIX)) return null;
  const id = decodeURIComponent(h.slice(HASH_PREFIX.length));
  return getComponent(id) ?? null;
}

function writeHash(c: Component | null) {
  if (typeof window === 'undefined') return;
  const base = window.location.pathname + window.location.search;
  const url = c ? `${base}${HASH_PREFIX}${encodeURIComponent(c.id)}` : base;
  window.history.replaceState(null, '', url);
}

export function useHashComponent() {
  const [selected, setSelected] = createSignal<Component | null>(readHash());

  const sync = () => {
    const next = readHash();
    const cur = selected();
    if ((next?.id ?? null) !== (cur?.id ?? null)) setSelected(next);
  };

  onMount(() => {
    window.addEventListener('hashchange', sync);
    onCleanup(() => window.removeEventListener('hashchange', sync));
  });

  const select = (c: Component | null) => {
    writeHash(c);
    setSelected(c);
  };

  return { selected, select };
}
