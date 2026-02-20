import { lazy, Suspense, ParentProps } from 'solid-js';
import Shell from './components/layout/Shell';
import TabNav from './components/layout/TabNav';
import Loading from './components/common/Loading';

// Lazy load pages for code splitting
const Sandbox = lazy(() => import('./pages/Sandbox'));
const CalculusOverview = lazy(() => import('./pages/CalculusOverview'));
const CalculusHealth = lazy(() => import('./pages/CalculusHealth'));
const MetaOverview = lazy(() => import('./pages/MetaOverview'));
const ManualProof = lazy(() => import('./pages/ManualProof'));
const DocIndex = lazy(() => import('./pages/DocIndex'));
const DocPage = lazy(() => import('./pages/DocPage'));
const TodoIndex = lazy(() => import('./pages/TodoIndex'));

// Root layout wrapper for all routes
export function RootLayout(props: ParentProps) {
  return (
    <Shell>
      <TabNav />
      <main class="flex-1 overflow-auto">
        <Suspense fallback={<Loading />}>
          {props.children}
        </Suspense>
      </main>
    </Shell>
  );
}

// Route definitions exported for use in index.tsx
export const routes = [
  { path: '/', component: Sandbox },
  { path: '/prove', component: ManualProof },
  { path: '/calculus', component: CalculusOverview },
  { path: '/health', component: CalculusHealth },
  { path: '/meta', component: MetaOverview },
  { path: '/research', component: DocIndex },
  { path: '/research/:slug', component: DocPage },
  { path: '/docs', component: DocIndex },
  { path: '/docs/:slug', component: DocPage },
  { path: '/theory', component: DocIndex },
  { path: '/theory/:slug', component: DocPage },
  { path: '/dev', component: DocIndex },
  { path: '/dev/:slug', component: DocPage },
  { path: '/todo', component: TodoIndex },
  { path: '/todo/:slug', component: DocPage },
];
