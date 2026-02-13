import { createAsync, cache } from "@solidjs/router";
import { Title } from "@solidjs/meta";
import { Show, Suspense } from "solid-js";
import fs from "fs";
import path from "path";
import { processDocument, clientHydrationScript } from "../../lib/markdown";

const DOCS_DIR = path.resolve(process.cwd(), "doc/documentation");

const getDocsIndex = cache(async () => {
  "use server";

  const filePath = path.join(DOCS_DIR, "INDEX.md");
  const content = fs.readFileSync(filePath, "utf-8");
  const doc = await processDocument(content, { basePath: '/docs', slug: 'INDEX' });

  return { title: doc.title, html: doc.html };
}, "docs-index");

export const route = {
  load: () => getDocsIndex(),
};

export default function DocsIndex() {
  const doc = createAsync(() => getDocsIndex());

  return (
    <Suspense fallback={<div class="text-gray-500">Loading docs index...</div>}>
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
