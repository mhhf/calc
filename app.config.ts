import { defineConfig } from "@solidjs/start/config";
import mdx from "@mdx-js/rollup";
import remarkGfm from "remark-gfm";
import remarkFrontmatter from "remark-frontmatter";
import commonjs from "vite-plugin-commonjs";
import tailwindcss from "@tailwindcss/vite";
import { fileURLToPath } from "url";
import { dirname, resolve } from "path";

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

export default defineConfig({
  // App root is src/ui
  appRoot: "./src/ui",
  // Use SSR for server-side rendering
  server: {
    preset: "node-server",
  },
  vite: {
    plugins: [
      // Transform CommonJS modules (lib/*.js) for both dev and build
      commonjs({
        filter(id: string) {
          return id.includes('/lib/') || id.includes('/out/parser.js') || id.includes('/out/ill-v2.json');
        }
      }),
      // MDX support for research docs
      {
        enforce: "pre",
        ...mdx({
          jsxImportSource: "solid-js",
          remarkPlugins: [remarkGfm, remarkFrontmatter],
        }),
      },
      tailwindcss(),
    ],
    resolve: {
      alias: {
        '@': resolve(__dirname, 'src/ui'),
        '@lib': resolve(__dirname, 'lib'),
        // Browser stubs for Node.js modules
        'crypto': resolve(__dirname, 'src/ui/stubs/crypto.ts'),
        'cli-color': resolve(__dirname, 'src/ui/stubs/cli-color.ts'),
      },
    },
    // Handle CommonJS dependencies
    optimizeDeps: {
      include: ['katex'],
    },
    build: {
      commonjsOptions: {
        include: [/lib\/.*\.js$/, /out\/parser\.js$/, /out\/ill-v2\.json$/, /node_modules/],
        transformMixedEsModules: true,
      },
    },
  },
});
