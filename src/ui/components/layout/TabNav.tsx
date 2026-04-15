import { A, useLocation } from '@solidjs/router';

interface Tab {
  path: string;
  label: string;
  /** Additional path prefixes that activate this tab */
  also?: string[];
}

const mainTabs: Tab[] = [
  { path: '/', label: 'Sandbox' },
  { path: '/prove', label: 'Prove' },
  { path: '/calculus', label: 'Calculus' },
  { path: '/health', label: 'Health' },
  { path: '/meta', label: 'Meta' },
  { path: '/docs', label: 'Docs', also: ['/theory', '/def'] },
];

function isActive(tab: Tab, pathname: string) {
  if (tab.path === '/') return pathname === '/';
  const prefixes = [tab.path, ...(tab.also || [])];
  return prefixes.some(p => pathname === p || pathname.startsWith(p + '/'));
}

export default function TabNav() {
  const location = useLocation();

  return (
    <nav class="bg-white dark:bg-gray-800 border-b border-gray-200 dark:border-gray-700">
      <div class="max-w-7xl mx-auto px-4">
        <div class="flex gap-1">
          {mainTabs.map((tab) => (
            <A
              href={tab.path}
              class="tab-link"
              classList={{ active: isActive(tab, location.pathname) }}
              end={tab.path === '/'}
            >
              {tab.label}
            </A>
          ))}
        </div>
      </div>
    </nav>
  );
}
