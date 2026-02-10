import { lazy, Suspense } from "solid-js";
import Loading from "../../components/common/Loading";

const MetaOverview = lazy(() => import("../../pages/MetaOverview"));

export default function MetaPage() {
  return (
    <Suspense fallback={<Loading />}>
      <MetaOverview />
    </Suspense>
  );
}
