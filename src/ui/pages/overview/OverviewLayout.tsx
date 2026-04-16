/**
 * Overview sub-navigation shell.
 *
 * Two-tier nav: [Views] (axis projections) | [Dives] (deep-dive pages).
 * Active tab is inferred from the URL; the outlet renders the active page.
 */

import { For, ParentProps } from 'solid-js';
import { A, useLocation } from '@solidjs/router';
import ErrorBoundary from '../../components/common/ErrorBoundary';
import { VIEWS, DEEP_DIVES } from './data/meta';

interface NavItem { path: string; label: string; }

const viewItems: NavItem[] = [
  { path: '/overview', label: 'Home' },
  ...VIEWS.map(v => ({ path: `/overview/${v.slug}`, label: v.title.replace(' Stack', '').replace(' Tree', '') })),
];

const diveItems: NavItem[] = DEEP_DIVES.map(d => ({
  path: `/overview/${d.slug}`,
  label: d.title.split(' ')[0],
}));

function isActive(item: NavItem, pathname: string): boolean {
  if (item.path === '/overview') return pathname === '/overview' || pathname === '/overview/';
  return pathname === item.path;
}

function NavRow(props: { items: NavItem[]; label: string; variant: 'views' | 'dives' }) {
  const location = useLocation();
  return (
    <div class="flex items-center gap-3 flex-wrap">
      <span class="text-[10px] uppercase tracking-wider font-semibold text-gray-500 dark:text-gray-400 w-16">
        {props.label}
      </span>
      <div class="flex gap-1 flex-wrap">
        <For each={props.items}>
          {(item) => (
            <A
              href={item.path}
              class={`px-3 py-1 rounded-md text-sm font-medium transition-colors ${
                isActive(item, location.pathname)
                  ? (props.variant === 'views'
                      ? 'bg-blue-600 text-white dark:bg-blue-500'
                      : 'bg-gray-800 text-white dark:bg-gray-200 dark:text-gray-900')
                  : 'text-gray-600 dark:text-gray-400 hover:text-gray-900 dark:hover:text-white hover:bg-gray-200 dark:hover:bg-gray-700'
              }`}
            >
              {item.label}
            </A>
          )}
        </For>
      </div>
    </div>
  );
}

export default function OverviewLayout(props: ParentProps) {
  return (
    <div class="flex flex-col">
      <nav class="bg-gradient-to-b from-white to-gray-50 dark:from-gray-800 dark:to-gray-900 border-b border-gray-200 dark:border-gray-700">
        <div class="max-w-7xl mx-auto px-4 py-3 space-y-2">
          <NavRow label="Views" items={viewItems} variant="views" />
          <NavRow label="Dives" items={diveItems} variant="dives" />
        </div>
      </nav>
      <div class="flex-1">
        <ErrorBoundary>{props.children}</ErrorBoundary>
      </div>
    </div>
  );
}
