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

// Architecture Overview (TODO_0205)
const OverviewLayout = lazy(() => import('./pages/overview/OverviewLayout'));
const OverviewLanding = lazy(() => import('./pages/overview/Landing'));
const OverviewTrust = lazy(() => import('./pages/overview/TrustStack'));
const OverviewSpecificity = lazy(() => import('./pages/overview/Specificity'));
const OverviewPipeline = lazy(() => import('./pages/overview/Pipeline'));
const OverviewAtlas = lazy(() => import('./pages/overview/Atlas'));
const OverviewProver = lazy(() => import('./pages/overview/Prover'));
const OverviewEngine = lazy(() => import('./pages/overview/Engine'));
const OverviewCompilation = lazy(() => import('./pages/overview/Compilation'));
const OverviewOptimization = lazy(() => import('./pages/overview/Optimization'));
const OverviewZk = lazy(() => import('./pages/overview/Zk'));
const OverviewParser = lazy(() => import('./pages/overview/Parser'));
const OverviewApps = lazy(() => import('./pages/overview/Apps'));

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
  // Doc folders
  { path: '/theory', component: DocIndex },
  { path: '/theory/:slug', component: DocPage },
  { path: '/def', component: DocIndex },
  { path: '/def/:slug', component: DocPage },
  { path: '/docs', component: DocIndex },
  { path: '/docs/:slug', component: DocPage },
  // Architecture Overview — nested routes under OverviewLayout
  {
    path: '/overview',
    component: OverviewLayout,
    children: [
      { path: '/', component: OverviewLanding },
      { path: '/trust', component: OverviewTrust },
      { path: '/specificity', component: OverviewSpecificity },
      { path: '/pipeline', component: OverviewPipeline },
      { path: '/atlas', component: OverviewAtlas },
      { path: '/prover', component: OverviewProver },
      { path: '/engine', component: OverviewEngine },
      { path: '/compilation', component: OverviewCompilation },
      { path: '/optimization', component: OverviewOptimization },
      { path: '/zk', component: OverviewZk },
      { path: '/parser', component: OverviewParser },
      { path: '/applications', component: OverviewApps },
    ],
  },
];
