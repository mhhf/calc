import { createResource, createSignal, createMemo, For, Show } from 'solid-js';
import { A } from '@solidjs/router';

interface TodoEntry {
  slug: string;
  title: string;
  summary: string;
  tags: string[];
  status: string;
  priority?: number;
  type?: string;
  depends_on: string[];
  required_by: string[];
}

const TYPE_COLORS: Record<string, string> = {
  bug:            'bg-red-100 text-red-800',
  research:       'bg-purple-100 text-purple-800',
  design:         'bg-blue-100 text-blue-800',
  implementation: 'bg-emerald-100 text-emerald-800',
  tooling:        'bg-gray-200 text-gray-700',
};

const STATUS_COLORS: Record<string, string> = {
  planning:                   'bg-gray-200 text-gray-700',
  researching:                'bg-purple-100 text-purple-700',
  'ready for implementation': 'bg-teal-100 text-teal-800',
  'in progress':              'bg-blue-100 text-blue-800',
  done:                       'bg-green-100 text-green-800',
};

function priorityColor(p: number): string {
  if (p >= 9) return 'bg-red-500 text-white';
  if (p >= 7) return 'bg-orange-400 text-white';
  if (p >= 4) return 'bg-yellow-400 text-gray-900';
  return 'bg-gray-300 text-gray-700';
}

/** Extract the 4-digit TODO number from slug like "0001_loli-..." */
function todoId(slug: string): string {
  const m = slug.match(/^(\d{4})/);
  return m ? m[1] : slug;
}

/** Parse TODO_NNNN references to slugs — returns the 4-digit number */
function parseTodoRef(ref: string): string | null {
  const m = ref.match(/TODO_(\d{4})/);
  return m ? m[1] : null;
}

async function fetchTodos(): Promise<TodoEntry[]> {
  const res = await fetch('/api/docs/todo');
  if (!res.ok) throw new Error(`Failed to fetch: ${res.status}`);
  return res.json();
}

const ALL_TYPES = ['bug', 'research', 'design', 'implementation', 'tooling'];

export default function TodoIndex() {
  const [todos] = createResource(fetchTodos);
  const [typeFilter, setTypeFilter] = createSignal<string | null>(null);
  const [statusFilter, setStatusFilter] = createSignal<string | null>(null);

  const filtered = createMemo(() => {
    let items = todos() || [];
    const tf = typeFilter();
    const sf = statusFilter();
    if (tf) items = items.filter(t => t.type === tf);
    if (sf) items = items.filter(t => t.status === sf);
    // Sort: priority descending, then ID ascending
    return [...items].sort((a, b) => {
      const pa = a.priority ?? 0, pb = b.priority ?? 0;
      if (pa !== pb) return pb - pa;
      return todoId(a.slug).localeCompare(todoId(b.slug));
    });
  });

  const statusCounts = createMemo(() => {
    const counts: Record<string, number> = {};
    for (const t of todos() || []) {
      counts[t.status] = (counts[t.status] || 0) + 1;
    }
    return counts;
  });

  return (
    <div class="mx-auto p-6" style="max-width: 1280px">
      <div class="flex items-baseline justify-between mb-4">
        <h2 class="text-2xl font-bold text-gray-900 dark:text-white">
          Todo
        </h2>
        <Show when={todos()}>
          <span class="text-sm text-gray-500">{filtered().length} items</span>
        </Show>
      </div>

      {/* Filters */}
      <Show when={todos()}>
        <div class="flex flex-wrap gap-4 mb-6">
          {/* Type filter */}
          <div class="flex flex-wrap gap-1">
            <button
              class="px-2 py-1 text-xs rounded transition-colors"
              classList={{
                'bg-gray-800 text-white': typeFilter() === null,
                'bg-gray-100 text-gray-600 hover:bg-gray-200': typeFilter() !== null,
              }}
              onClick={() => setTypeFilter(null)}
            >
              All types
            </button>
            <For each={ALL_TYPES}>
              {(t) => (
                <button
                  class="px-2 py-1 text-xs rounded transition-colors"
                  classList={{
                    'ring-2 ring-gray-800 ring-offset-1': typeFilter() === t,
                    [TYPE_COLORS[t] || '']: true,
                  }}
                  onClick={() => setTypeFilter(typeFilter() === t ? null : t)}
                >
                  {t}
                </button>
              )}
            </For>
          </div>
          {/* Status filter */}
          <div class="flex flex-wrap gap-1">
            <For each={Object.keys(statusCounts())}>
              {(s) => (
                <button
                  class="px-2 py-1 text-xs rounded transition-colors"
                  classList={{
                    'ring-2 ring-gray-800 ring-offset-1': statusFilter() === s,
                    [STATUS_COLORS[s] || 'bg-gray-100 text-gray-600']: true,
                  }}
                  onClick={() => setStatusFilter(statusFilter() === s ? null : s)}
                >
                  {s} ({statusCounts()[s]})
                </button>
              )}
            </For>
          </div>
        </div>
      </Show>

      <Show when={todos.loading}>
        <p class="text-gray-500">Loading...</p>
      </Show>

      <Show when={todos.error}>
        <p class="text-red-500">Error: {todos.error?.message}</p>
      </Show>

      <Show when={todos()}>
        <div class="space-y-2">
          <For each={filtered()}>
            {(todo) => {
              const id = todoId(todo.slug);
              const p = todo.priority ?? 0;
              return (
                <A
                  href={`/todo/${todo.slug}`}
                  class="block rounded-lg border border-gray-200 dark:border-gray-700 hover:border-blue-400 dark:hover:border-blue-500 transition-colors bg-white dark:bg-gray-800"
                >
                  <div class="flex items-start gap-3 p-3">
                    {/* Priority badge */}
                    <div
                      class={`shrink-0 w-8 h-8 rounded flex items-center justify-center text-sm font-bold ${priorityColor(p)}`}
                    >
                      {p}
                    </div>

                    {/* Main content */}
                    <div class="flex-1 min-w-0">
                      {/* Top row: ID + Title + Type + Status */}
                      <div class="flex items-center gap-2 flex-wrap">
                        <span class="font-mono text-xs text-gray-400 shrink-0">
                          TODO_{id}
                        </span>
                        <span class="font-semibold text-gray-900 dark:text-white truncate">
                          {todo.title}
                        </span>
                        <Show when={todo.type}>
                          <span class={`shrink-0 px-1.5 py-0.5 text-[10px] font-medium uppercase rounded ${TYPE_COLORS[todo.type!] || 'bg-gray-100 text-gray-600'}`}>
                            {todo.type}
                          </span>
                        </Show>
                        <Show when={todo.status}>
                          <span class={`shrink-0 px-1.5 py-0.5 text-[10px] rounded ${STATUS_COLORS[todo.status] || 'bg-gray-100 text-gray-600'}`}>
                            {todo.status}
                          </span>
                        </Show>
                      </div>

                      {/* Summary */}
                      <Show when={todo.summary}>
                        <p class="text-sm text-gray-500 dark:text-gray-400 mt-0.5 truncate">
                          {todo.summary}
                        </p>
                      </Show>

                      {/* Dependencies + Tags row */}
                      <div class="flex items-center gap-3 mt-1.5 flex-wrap text-xs">
                        {/* Dependencies */}
                        <Show when={todo.depends_on?.length}>
                          <span class="text-gray-400">
                            needs:{' '}
                            <For each={todo.depends_on}>
                              {(dep, i) => {
                                const depId = parseTodoRef(dep);
                                return (
                                  <>
                                    {i() > 0 && ', '}
                                    <span class="font-mono text-orange-600 dark:text-orange-400">
                                      {depId ? depId : dep}
                                    </span>
                                  </>
                                );
                              }}
                            </For>
                          </span>
                        </Show>
                        <Show when={todo.required_by?.length}>
                          <span class="text-gray-400">
                            blocks:{' '}
                            <For each={todo.required_by}>
                              {(dep, i) => {
                                const depId = parseTodoRef(dep);
                                return (
                                  <>
                                    {i() > 0 && ', '}
                                    <span class="font-mono text-blue-600 dark:text-blue-400">
                                      {depId ? depId : dep}
                                    </span>
                                  </>
                                );
                              }}
                            </For>
                          </span>
                        </Show>

                        {/* Tags */}
                        <Show when={todo.tags?.length}>
                          <div class="flex gap-1 flex-wrap">
                            <For each={todo.tags}>
                              {(tag) => (
                                <span class="px-1 py-0 bg-gray-100 dark:bg-gray-700 text-gray-500 dark:text-gray-400 rounded">
                                  {tag}
                                </span>
                              )}
                            </For>
                          </div>
                        </Show>
                      </div>
                    </div>
                  </div>
                </A>
              );
            }}
          </For>
        </div>
      </Show>
    </div>
  );
}
