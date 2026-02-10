import { lazy, Suspense } from "solid-js";
import Loading from "../../components/common/Loading";

const Sandbox = lazy(() => import("../../pages/Sandbox"));

export default function HomePage() {
  return (
    <Suspense fallback={<Loading />}>
      <Sandbox />
    </Suspense>
  );
}
