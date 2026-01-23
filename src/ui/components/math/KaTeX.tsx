import katex from 'katex';
import { createMemo } from 'solid-js';

interface KaTeXProps {
  latex: string;
  display?: boolean;
  class?: string;
}

export default function KaTeX(props: KaTeXProps) {
  const html = createMemo(() => {
    if (!props.latex) return '';
    try {
      return katex.renderToString(props.latex, {
        displayMode: props.display ?? false,
        throwOnError: false,
        trust: true,
      });
    } catch (e) {
      console.error('KaTeX error:', e);
      return `<span class="text-red-500 font-mono text-sm">${props.latex}</span>`;
    }
  });

  return (
    <span
      class={props.class}
      innerHTML={html()}
    />
  );
}
