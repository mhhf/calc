import { lazy, Suspense } from "solid-js";
import Loading from "../../components/common/Loading";

const ManualProof = lazy(() => import("../../pages/ManualProof"));

export default function ProvePage() {
  return (
    <Suspense fallback={<Loading />}>
      <ManualProof />
    </Suspense>
  );
}
