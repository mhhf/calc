import { defineConfig } from 'vite';
import solid from 'vite-plugin-solid';
import tailwindcss from '@tailwindcss/vite';
import commonjs from 'vite-plugin-commonjs';
import path from 'path';

export default defineConfig({
  plugins: [
    // Transform CommonJS modules (lib/*.js) for both dev and build
    commonjs({
      filter(id) {
        // Transform our lib files and the generated parser
        return id.includes('/lib/') || id.includes('/out/parser.js');
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
      include: [/lib\/.*\.js$/, /out\/parser\.js$/, /node_modules/],
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
