import { lazy, Suspense, ParentProps } from 'solid-js';
import Shell from './components/layout/Shell';
import TabNav from './components/layout/TabNav';
import Loading from './components/common/Loading';

// Lazy load pages for code splitting
const Sandbox = lazy(() => import('./pages/Sandbox'));
const CalculusOverview = lazy(() => import('./pages/CalculusOverview'));
const MetaOverview = lazy(() => import('./pages/MetaOverview'));
const ManualProof = lazy(() => import('./pages/ManualProof'));

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
  { path: '/meta', component: MetaOverview },
];
