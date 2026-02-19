import { A, useLocation } from '@solidjs/router';

const mainTabs = [
  { path: '/', label: 'Sandbox' },
  { path: '/prove', label: 'Prove' },
  { path: '/calculus', label: 'Calculus' },
  { path: '/health', label: 'Health' },
  { path: '/meta', label: 'Meta' },
];

const docTabs = [
  { path: '/research', label: 'Research' },
  { path: '/docs', label: 'Docs' },
  { path: '/dev', label: 'Dev' },
  { path: '/todo', label: 'Todo' },
];

function isActive(tab: { path: string }, pathname: string) {
  return tab.path === '/'
    ? pathname === '/'
    : pathname === tab.path || pathname.startsWith(tab.path + '/');
}

export default function TabNav() {
  const location = useLocation();

  return (
    <nav class="bg-white dark:bg-gray-800 border-b border-gray-200 dark:border-gray-700">
      <div class="max-w-7xl mx-auto px-4">
        <div class="flex gap-1 justify-between">
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
          <div class="flex gap-1">
            {docTabs.map((tab) => (
              <A
                href={tab.path}
                class="tab-link tab-link-doc"
                classList={{ active: isActive(tab, location.pathname) }}
              >
                {tab.label}
              </A>
            ))}
          </div>
        </div>
      </div>
    </nav>
  );
}
