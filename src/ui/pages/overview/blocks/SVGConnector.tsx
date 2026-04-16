/**
 * SVG connector arrow between two points.
 *
 * Used for: pipeline swim-lane flow arrows; monad-bridge between the two
 * trust-stack columns; connection overlays on deep-dive diagrams.
 *
 * Self-contained: callers pass absolute x,y coordinates (in the parent
 * SVG's coordinate system) — no DOM coupling.
 */

import { Show } from 'solid-js';

interface Props {
  x1: number; y1: number;
  x2: number; y2: number;
  /** Stroke color class (Tailwind-compatible via currentColor). */
  colorClass?: string;
  /** Arrow head style. */
  head?: 'arrow' | 'open' | 'none';
  /** Label rendered at the midpoint. */
  label?: string;
  /** Dashed stroke (for non-import connections). */
  dashed?: boolean;
  /** Curve strength — 0 = straight line, 1 = exaggerated S-curve. */
  curve?: number;
}

export default function SVGConnector(props: Props) {
  const curveK = () => props.curve ?? 0.35;
  const dx = () => props.x2 - props.x1;
  const dy = () => props.y2 - props.y1;
  const midX = () => props.x1 + dx() / 2;
  const midY = () => props.y1 + dy() / 2;

  const path = () => {
    const cpx1 = props.x1 + dx() * curveK();
    const cpx2 = props.x2 - dx() * curveK();
    return `M ${props.x1},${props.y1} C ${cpx1},${props.y1} ${cpx2},${props.y2} ${props.x2},${props.y2}`;
  };

  return (
    <g class={props.colorClass ?? 'text-gray-500 dark:text-gray-400'}>
      <path
        d={path()}
        fill="none"
        stroke="currentColor"
        stroke-width="1.5"
        stroke-dasharray={props.dashed ? '4 4' : undefined}
        marker-end={props.head === 'none' ? undefined : 'url(#arrow-head)'}
      />
      <Show when={props.label}>
        <text x={midX()} y={midY() - 6} fill="currentColor" font-size="11" text-anchor="middle" class="font-medium">
          {props.label}
        </text>
      </Show>
    </g>
  );
}

/** Arrow-head defs. Put this once at the top of an SVG that uses SVGConnector. */
export function ArrowHeadDefs() {
  return (
    <defs>
      <marker
        id="arrow-head"
        markerWidth="8"
        markerHeight="8"
        refX="7"
        refY="4"
        orient="auto-start-reverse"
      >
        <path d="M 0 0 L 8 4 L 0 8 z" fill="currentColor" />
      </marker>
    </defs>
  );
}
