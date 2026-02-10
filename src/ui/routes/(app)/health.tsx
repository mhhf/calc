import { lazy, Suspense } from "solid-js";
import Loading from "../../components/common/Loading";

const CalculusHealth = lazy(() => import("../../pages/CalculusHealth"));

export default function HealthPage() {
  return (
    <Suspense fallback={<Loading />}>
      <CalculusHealth />
    </Suspense>
  );
}
