import { A, useLocation } from '@solidjs/router';

const tabs = [
  { path: '/', label: 'Sandbox' },
  { path: '/prove', label: 'Prove' },
  { path: '/calculus', label: 'Calculus' },
  { path: '/meta', label: 'Meta' },
];

export default function TabNav() {
  const location = useLocation();

  return (
    <nav class="bg-white dark:bg-gray-800 border-b border-gray-200 dark:border-gray-700">
      <div class="max-w-7xl mx-auto px-4">
        <div class="flex gap-1">
          {tabs.map((tab) => (
            <A
              href={tab.path}
              class="tab-link"
              classList={{
                active: location.pathname === tab.path,
              }}
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
