import { ParentProps } from "solid-js";
import Shell from "../components/layout/Shell";
import TabNav from "../components/layout/TabNav";

// Layout for main app pages (sandbox, calculus, etc.)
export default function AppLayout(props: ParentProps) {
  return (
    <Shell>
      <TabNav />
      <main class="flex-1 overflow-auto">
        {props.children}
      </main>
    </Shell>
  );
}
