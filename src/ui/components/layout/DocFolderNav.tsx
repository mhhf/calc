import { A, useLocation } from '@solidjs/router';

const FOLDERS = [
  { key: 'docs', label: 'Documentation' },
  { key: 'theory', label: 'Theory' },
  { key: 'def', label: 'Definitions' },
];

export default function DocFolderNav() {
  const location = useLocation();
  const active = () => location.pathname.split('/')[1];

  return (
    <nav class="flex gap-1 mb-6">
      {FOLDERS.map(f => (
        <A
          href={`/${f.key}`}
          class="px-3 py-1.5 text-sm rounded-md transition-colors"
          classList={{
            'bg-blue-600 text-white': active() === f.key,
            'text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-700': active() !== f.key,
          }}
        >
          {f.label}
        </A>
      ))}
    </nav>
  );
}
