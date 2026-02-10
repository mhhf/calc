import { lazy, Suspense } from "solid-js";
import Loading from "../../components/common/Loading";

const CalculusOverview = lazy(() => import("../../pages/CalculusOverview"));

export default function CalculusPage() {
  return (
    <Suspense fallback={<Loading />}>
      <CalculusOverview />
    </Suspense>
  );
}
