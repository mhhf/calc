import { A, useLocation } from '@solidjs/router';

// Inlined by vite.config.ts `define`. See flake.nix `preBuild` for the
// build-time source (`self.shortRev` / `dirtyShortRev` / "dev").
declare const __GIT_COMMIT__: string;

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
  { path: '/overview', label: 'Overview' },
];

function isActive(tab: Tab, pathname: string) {
  if (tab.path === '/') return pathname === '/';
  const prefixes = [tab.path, ...(tab.also || [])];
  return prefixes.some(p => pathname === p || pathname.startsWith(p + '/'));
}

const commitHash = typeof __GIT_COMMIT__ !== 'undefined' ? __GIT_COMMIT__ : 'dev';

export default function TabNav() {
  const location = useLocation();

  return (
    <nav class="bg-white dark:bg-gray-800 border-b border-gray-200 dark:border-gray-700">
      <div class="max-w-7xl mx-auto px-4">
        <div class="flex gap-1 items-center">
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
          <a
            href={`https://git3.denis.page/calc/commit/${commitHash}`}
            target="_blank"
            rel="noopener noreferrer"
            title={`Running build ${commitHash}`}
            class="ml-auto text-xs font-mono text-gray-500 dark:text-gray-400 hover:text-gray-700 dark:hover:text-gray-200 px-2 py-1 rounded border border-gray-200 dark:border-gray-700"
          >
            {commitHash}
          </a>
        </div>
      </div>
    </nav>
  );
}
