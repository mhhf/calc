/**
 * PanZoom — CSS-transform wrapper around an existing layout.
 *
 * Intentionally does not re-render as SVG/Canvas — we keep text
 * selection, native accessibility, browser find-in-page, and the same
 * renderLayout() function the non-panzoom path uses. Drag translates
 * the transform; wheel scales it cursor-centered so the point under
 * the pointer stays fixed.
 *
 * State is intentionally component-local and NOT persisted across
 * mounts — users who want to revisit a proof should re-zoom
 * deliberately. The only persisted bit is the toggle on/off flag (in
 * ProofBlock.tsx).
 *
 * Per-fixture measurements: at scale 0.3 the 255-node tensor128 proof
 * fits a ~900 px viewport, which is the kind of bird's-eye view a
 * static depth-fold cannot match.
 */
import { createSignal, type JSX } from 'solid-js';

const MIN_SCALE = 0.1;
const MAX_SCALE = 4;
// Wheel delta → scale factor: each notch changes scale by ~15%. This
// feels roughly like native page zoom on most trackpads.
const WHEEL_ZOOM_FACTOR = 1.0015;

export function PanZoom(props: { children: JSX.Element }) {
  const [tx, setTx] = createSignal(0);
  const [ty, setTy] = createSignal(0);
  const [s, setS] = createSignal(1);
  let outer: HTMLDivElement | undefined;
  let inner: HTMLDivElement | undefined;
  let drag: { x: number; y: number; tx: number; ty: number; id: number } | null = null;

  const onPointerDown = (e: PointerEvent) => {
    // Only primary-button drag; leave right-click and modifier combos
    // alone so the user can still select text, open rule-chip links,
    // etc. Starting the drag on a button/link is a no-op (let click go
    // through), so we filter interactive targets.
    if (e.button !== 0) return;
    const t = e.target as HTMLElement;
    if (t.closest('button, a, input, [role="tab"]')) return;
    drag = { x: e.clientX, y: e.clientY, tx: tx(), ty: ty(), id: e.pointerId };
    (e.currentTarget as HTMLDivElement).setPointerCapture(e.pointerId);
    e.preventDefault();
  };
  const onPointerMove = (e: PointerEvent) => {
    if (!drag || drag.id !== e.pointerId) return;
    setTx(drag.tx + (e.clientX - drag.x));
    setTy(drag.ty + (e.clientY - drag.y));
  };
  const onPointerUp = (e: PointerEvent) => {
    if (!drag || drag.id !== e.pointerId) return;
    try { (e.currentTarget as HTMLDivElement).releasePointerCapture(e.pointerId); } catch {}
    drag = null;
  };
  const onWheel = (e: WheelEvent) => {
    // Hold Shift for natural scrolling — zoom only on plain wheel so
    // trackpad/mouse wheel consistently maps to zoom inside the block.
    if (!outer) return;
    e.preventDefault();
    const factor = Math.pow(WHEEL_ZOOM_FACTOR, -e.deltaY);
    const prev = s();
    const next = Math.max(MIN_SCALE, Math.min(MAX_SCALE, prev * factor));
    if (next === prev) return;
    // Cursor-centered zoom: keep the point under the pointer fixed in
    // viewport coordinates. Math: for a transform T(p) = t + s·p, we
    // want T_new(p0) = T_old(p0), which gives t_new = t_old + (s_old − s_new)·p0
    // where p0 is the pointer in the inner element's pre-transform frame.
    const rect = outer.getBoundingClientRect();
    const cx = e.clientX - rect.left;
    const cy = e.clientY - rect.top;
    const px = (cx - tx()) / prev;
    const py = (cy - ty()) / prev;
    setS(next);
    setTx(cx - px * next);
    setTy(cy - py * next);
  };
  const reset = () => { setTx(0); setTy(0); setS(1); };

  return (
    <div
      ref={outer}
      class="calc-proof-panzoom"
      onPointerDown={onPointerDown}
      onPointerMove={onPointerMove}
      onPointerUp={onPointerUp}
      onPointerCancel={onPointerUp}
      onWheel={onWheel}
      style="position:relative;overflow:hidden;height:420px;min-height:240px;background:repeating-linear-gradient(45deg,#fafafa,#fafafa 10px,#f4f4f8 10px,#f4f4f8 20px);cursor:grab;touch-action:none;user-select:none"
    >
      <div
        ref={inner}
        style={`position:absolute;left:0;top:0;transform-origin:0 0;transform:translate(${tx()}px,${ty()}px) scale(${s()});transition:none;will-change:transform`}
      >
        {props.children}
      </div>
      <div style="position:absolute;top:0.35em;right:0.35em;display:flex;gap:0.25em;font-size:0.75em;background:rgba(255,255,255,0.85);padding:0.15em 0.35em;border:1px solid #ddd;border-radius:3px;backdrop-filter:blur(2px)">
        <span style="color:#666" title="Current zoom">{(s() * 100).toFixed(0)}%</span>
        <button
          type="button"
          onClick={reset}
          title="Reset pan + zoom"
          style="font-family:inherit;font-size:inherit;border:1px solid #ccc;background:#fff;border-radius:2px;padding:0 0.35em;cursor:pointer"
        >
          reset
        </button>
      </div>
    </div>
  );
}
