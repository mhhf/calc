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
  subsumed:                   'bg-gray-200 text-gray-500',
};

const CLOSED_STATUSES = new Set(['done', 'subsumed']);

/** Compute up to 3 recommended TODOs: unblocked, highest priority, active */
function computeRecommended(todos: TodoEntry[]): Set<string> {
  const closedIds = new Set(
    todos.filter(t => CLOSED_STATUSES.has(t.status)).map(t => todoId(t.slug))
  );
  const unblocked = todos.filter(t => {
    if (CLOSED_STATUSES.has(t.status)) return false;
    if (!t.depends_on?.length) return true;
    return t.depends_on.every(dep => {
      const depId = dep.match(/TODO_(\d{4})/)?.[1];
      return depId ? closedIds.has(depId) : false;
    });
  });
  unblocked.sort((a, b) => (b.priority ?? 0) - (a.priority ?? 0));
  return new Set(unblocked.slice(0, 3).map(t => t.slug));
}

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

function isClosed(todo: TodoEntry): boolean {
  return CLOSED_STATUSES.has(todo.status);
}

export default function TodoIndex() {
  const [todos] = createResource(fetchTodos);
  const [typeFilter, setTypeFilter] = createSignal<string | null>(null);
  const [statusFilter, setStatusFilter] = createSignal<string | null>(null);

  const applyFilters = (items: TodoEntry[]) => {
    const tf = typeFilter();
    const sf = statusFilter();
    if (tf) items = items.filter(t => t.type === tf);
    if (sf) items = items.filter(t => t.status === sf);
    return items;
  };

  const activeItems = createMemo(() => {
    const all = todos() || [];
    const items = applyFilters(all.filter(t => !isClosed(t)));
    return [...items].sort((a, b) => {
      const pa = a.priority ?? 0, pb = b.priority ?? 0;
      if (pa !== pb) return pb - pa;
      return todoId(a.slug).localeCompare(todoId(b.slug));
    });
  });

  const doneItems = createMemo(() => {
    const all = todos() || [];
    const items = applyFilters(all.filter(t => isClosed(t)));
    return [...items].sort((a, b) => todoId(a.slug).localeCompare(todoId(b.slug)));
  });

  const recommended = createMemo(() => computeRecommended(todos() || []));

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
          <span class="text-sm text-gray-500">
            {activeItems().length} active
            <Show when={doneItems().length}>
              {' '}&middot; {doneItems().length} closed
            </Show>
          </span>
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
        {/* Active items */}
        <div class="space-y-2">
          <For each={activeItems()}>
            {(todo) => <TodoCard todo={todo} recommended={recommended().has(todo.slug)} />}
          </For>
        </div>

        {/* Done / subsumed section */}
        <Show when={doneItems().length}>
          <div class="mt-8">
            <h3 class="text-sm font-medium text-gray-400 dark:text-gray-500 uppercase tracking-wide mb-2">
              Done
            </h3>
            <div class="space-y-1">
              <For each={doneItems()}>
                {(todo) => <TodoCard todo={todo} muted />}
              </For>
            </div>
          </div>
        </Show>
      </Show>
    </div>
  );
}

function TodoCard(props: { todo: TodoEntry; muted?: boolean; recommended?: boolean }) {
  const todo = props.todo;
  const id = todoId(todo.slug);

  return (
    <A
      href={`/todo/${todo.slug}`}
      class="block rounded-lg border transition-colors"
      classList={{
        'border-gray-200 dark:border-gray-700 hover:border-blue-400 dark:hover:border-blue-500 bg-white dark:bg-gray-800': !props.muted,
        'border-gray-100 dark:border-gray-800 hover:border-gray-300 dark:hover:border-gray-600 bg-gray-50 dark:bg-gray-900 opacity-60': !!props.muted,
      }}
    >
      <div class="flex items-start gap-3 p-3">
        {/* Priority badge — active items only */}
        <Show when={!props.muted}>
          {(() => {
            const p = todo.priority ?? 0;
            return (
              <div
                class={`shrink-0 w-8 h-8 rounded flex items-center justify-center text-sm font-bold ${priorityColor(p)}`}
              >
                {p}
              </div>
            );
          })()}
        </Show>

        <div class="flex-1 min-w-0">
          {/* Recommended star — top right */}
          <Show when={props.recommended}>
            <div class="float-right ml-2" title="Recommended: unblocked, high priority">
              <span class="text-amber-400 text-lg">&#9733;</span>
            </div>
          </Show>
          {/* Top row: ID + Title + Type + Status */}
          <div class="flex items-center gap-2 flex-wrap">
            <span class="font-mono text-xs text-gray-400 shrink-0">
              TODO_{id}
            </span>
            <span
              class="font-semibold truncate"
              classList={{
                'text-gray-900 dark:text-white': !props.muted,
                'text-gray-500 dark:text-gray-400': !!props.muted,
              }}
            >
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
}
