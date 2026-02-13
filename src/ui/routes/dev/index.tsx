import { createAsync, cache } from "@solidjs/router";
import { Title } from "@solidjs/meta";
import { Show, Suspense } from "solid-js";
import fs from "fs";
import path from "path";
import { processDocument, clientHydrationScript } from "../../lib/markdown";

const DEV_DIR = path.resolve(process.cwd(), "doc/dev");

const getDevIndex = cache(async () => {
  "use server";

  const filePath = path.join(DEV_DIR, "index.md");
  const content = fs.readFileSync(filePath, "utf-8");
  const doc = await processDocument(content, { basePath: '/dev', slug: 'index' });

  return { title: doc.title, html: doc.html };
}, "dev-index");

export const route = {
  load: () => getDevIndex(),
};

export default function DevIndex() {
  const doc = createAsync(() => getDevIndex());

  return (
    <Suspense fallback={<div class="text-gray-500">Loading dev index...</div>}>
      <Show when={doc()}>
        {(data) => (
          <>
            <Title>{data().title} - CALC</Title>
            <article class="prose-research" innerHTML={data().html} />
            <div innerHTML={clientHydrationScript} />
          </>
        )}
      </Show>
    </Suspense>
  );
}
