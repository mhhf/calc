import { defineConfig } from 'vite';
import solid from 'vite-plugin-solid';
import tailwindcss from '@tailwindcss/vite';
import commonjs from 'vite-plugin-commonjs';
import viteDocs from './plugins/vite-docs';
import path from 'path';

export default defineConfig({
  plugins: [
    viteDocs(),
    // Transform CommonJS modules (lib/*.js) for both dev and build
    commonjs({
      filter(id) {
        // Transform our lib files and the generated parser
        return id.includes('/lib/') || id.includes('/out/parser.js') || id.includes('/out/ill.json');
      }
    }),
    solid(),
    tailwindcss(),
  ],
  root: path.resolve(__dirname),
  base: './',
  build: {
    outDir: '../../out/ui',
    emptyOutDir: true,
    commonjsOptions: {
      include: [/lib\/.*\.js$/, /out\/parser\.js$/, /out\/ill\.json$/, /node_modules/],
      transformMixedEsModules: true,
    },
  },
  optimizeDeps: {
    include: ['katex'],
  },
  resolve: {
    alias: {
      '@': path.resolve(__dirname),
      '@lib': path.resolve(__dirname, '../../lib'),
      // Provide browser stubs for Node.js modules
      'crypto': path.resolve(__dirname, './stubs/crypto.ts'),
      'cli-color': path.resolve(__dirname, './stubs/cli-color.ts'),
    },
  },
  server: {
    port: 3000,
  },
});
