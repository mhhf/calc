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
  cluster?: string;
  starred?: boolean;
}

const TYPE_COLORS: Record<string, string> = {
  bug:            'bg-red-100 text-red-800 dark:bg-red-900/30 dark:text-red-400',
  research:       'bg-gray-200 text-gray-700 dark:bg-gray-700 dark:text-gray-300',
  design:         'bg-gray-200 text-gray-700 dark:bg-gray-700 dark:text-gray-300',
  implementation: 'bg-gray-200 text-gray-700 dark:bg-gray-700 dark:text-gray-300',
  tooling:        'bg-gray-200 text-gray-700 dark:bg-gray-700 dark:text-gray-300',
};

const STATUS_COLORS: Record<string, string> = {
  planning:                   'bg-gray-200 text-gray-700 dark:bg-gray-700 dark:text-gray-300',
  researching:                'bg-gray-200 text-gray-700 dark:bg-gray-700 dark:text-gray-300',
  'ready for implementation': 'bg-gray-200 text-gray-700 dark:bg-gray-700 dark:text-gray-300',
  'in progress':              'bg-gray-200 text-gray-700 dark:bg-gray-700 dark:text-gray-300',
  done:                       'bg-green-100 text-green-800 dark:bg-green-900/30 dark:text-green-400',
  subsumed:                   'bg-gray-200 text-gray-500 dark:bg-gray-700 dark:text-gray-400',
  backlogged:                 'bg-gray-200 text-gray-500 dark:bg-gray-700 dark:text-gray-400',
};

const CLOSED_STATUSES = new Set(['done', 'subsumed', 'backlogged']);

async function toggleStar(slug: string, current: boolean): Promise<boolean> {
  const res = await fetch(`/api/docs/todo/${slug}/star`, {
    method: 'PATCH',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ starred: !current }),
  });
  if (!res.ok) throw new Error(`Failed to toggle star: ${res.status}`);
  return !current;
}

function priorityColor(p: number): string {
  if (p >= 9) return 'bg-blue-500 text-white dark:bg-blue-600';
  if (p >= 7) return 'bg-blue-100 text-blue-800 dark:bg-blue-900/30 dark:text-blue-300';
  return 'bg-gray-200 text-gray-600 dark:bg-gray-700 dark:text-gray-300';
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

function TodoTocIndex(props: { todos: TodoEntry[] }) {
  const activeTodos = createMemo(() =>
    props.todos.filter(t => !isClosed(t))
  );

  const grouped = createMemo(() => {
    const groups: Record<string, TodoEntry[]> = {};
    for (const t of activeTodos()) {
      const cat = t.cluster || 'Other';
      (groups[cat] ??= []).push(t);
    }
    // Sort within each group by ID
    for (const cat of Object.keys(groups)) {
      groups[cat].sort((a, b) => todoId(a.slug).localeCompare(todoId(b.slug)));
    }
    // Named clusters first (alphabetically), then "Other" last
    const ordered: [string, TodoEntry[]][] = [];
    const cats = Object.keys(groups).filter(c => c !== 'Other').sort();
    for (const cat of cats) ordered.push([cat, groups[cat]]);
    if (groups['Other']) ordered.push(['Other', groups['Other']]);
    return ordered;
  });

  return (
    <Show when={grouped().length > 0}>
      <div class="prose-research">
        <nav class="toc">
          <span class="toc-title">Index</span>
          <ul>
            <For each={grouped()}>
              {([category, categoryTodos]) => (
                <li>
                  <a
                    href={`#cluster-${category.toLowerCase().replace(/\s+/g, '-')}`}
                    onClick={(e) => {
                      e.preventDefault();
                      document.getElementById(`cluster-${category.toLowerCase().replace(/\s+/g, '-')}`)?.scrollIntoView({ behavior: 'smooth' });
                    }}
                  >
                    {category}
                  </a>
                  <ul>
                    <For each={categoryTodos}>
                      {(todo) => {
                        const id = todoId(todo.slug);
                        return (
                          <li>
                            <a
                              href={`#todo-${id}`}
                              onClick={(e) => {
                                e.preventDefault();
                                document.getElementById(`todo-${id}`)?.scrollIntoView({ behavior: 'smooth' });
                              }}
                            >
                              <span class="font-mono text-xs text-gray-400">TODO_{id} </span>
                              {todo.title}
                            </a>
                          </li>
                        );
                      }}
                    </For>
                  </ul>
                </li>
              )}
            </For>
          </ul>
        </nav>
      </div>
    </Show>
  );
}

export default function TodoIndex() {
  const [todos, { mutate }] = createResource(fetchTodos);
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

  const handleToggleStar = async (slug: string, current: boolean) => {
    const newVal = await toggleStar(slug, current);
    mutate(prev => prev?.map(t => t.slug === slug ? { ...t, starred: newVal } : t));
  };

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

      {/* TOC index */}
      <Show when={todos()}>
        <TodoTocIndex todos={todos()!} />
      </Show>

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
            {(todo) => (
              <div class="flex items-center gap-2">
                <div class="flex-1 min-w-0">
                  <TodoCard todo={todo} />
                </div>
                <button
                  class="shrink-0 text-xl leading-none p-1 transition-colors"
                  classList={{
                    'text-amber-400 hover:text-amber-300': !!todo.starred,
                    'text-gray-300 dark:text-gray-600 hover:text-amber-400': !todo.starred,
                  }}
                  title={todo.starred ? 'Unstar' : 'Star — mark as current focus'}
                  onClick={() => handleToggleStar(todo.slug, !!todo.starred)}
                >
                  &#9733;
                </button>
              </div>
            )}
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

function TodoCard(props: { todo: TodoEntry; muted?: boolean }) {
  const todo = props.todo;
  const id = todoId(todo.slug);

  return (
    <A
      id={`todo-${id}`}
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
              <span class={`shrink-0 px-1.5 py-0.5 text-xs font-medium uppercase rounded ${TYPE_COLORS[todo.type!] || 'bg-gray-100 text-gray-600'}`}>
                {todo.type}
              </span>
            </Show>
            <Show when={todo.status}>
              <span class={`shrink-0 px-1.5 py-0.5 text-xs rounded ${STATUS_COLORS[todo.status] || 'bg-gray-100 text-gray-600'}`}>
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
                        <span class="font-mono text-gray-500 dark:text-gray-400">
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
                        <span class="font-mono text-gray-500 dark:text-gray-400">
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
