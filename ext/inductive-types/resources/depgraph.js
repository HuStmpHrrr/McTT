// The graph fits the window; the mouse wheel or a two-finger pinch zooms,
// dragging with the mouse or one finger pans, and a double click or double tap
// shows the whole graph again.
function makeGraphPannable(svg) {
  const full = svg.viewBox.baseVal;
  const home = { x: full.x, y: full.y, w: full.width, h: full.height };
  let vb = { ...home };
  svg.removeAttribute('width');
  svg.removeAttribute('height');

  const apply = () => svg.setAttribute('viewBox', `${vb.x} ${vb.y} ${vb.w} ${vb.h}`);
  // Graph units per screen pixel (the viewBox is fitted, keeping its aspect).
  const unitsPerPixel = () => {
    const r = svg.getBoundingClientRect();
    return Math.max(vb.w / r.width, vb.h / r.height);
  };
  const toGraph = (e) => {
    const p = svg.createSVGPoint();
    p.x = e.clientX; p.y = e.clientY;
    return p.matrixTransform(svg.getScreenCTM().inverse());
  };

  // Zoom by the factor k (> 1 zooms out) around the graph point p.
  const zoomAt = (p, k, base) => {
    const w = Math.min(home.w, Math.max(home.w / 40, base.w * k));
    const r = w / base.w;
    vb = { x: p.x - (p.x - base.x) * r, y: p.y - (p.y - base.y) * r, w: w, h: base.h * r };
    apply();
  };

  svg.addEventListener('wheel', (e) => {
    e.preventDefault();
    // Proportional to the wheel distance: about 10% per notch (deltaY ≈ 100 px),
    // and smooth on touchpads; line or page deltas are scaled to pixels.
    const pixels = e.deltaY * (e.deltaMode === 1 ? 33 : e.deltaMode === 2 ? 800 : 1);
    zoomAt(toGraph(e), Math.exp(Math.max(-0.5, Math.min(0.5, pixels * 0.001))), vb);
  }, { passive: false });

  // Pointers (mouse, pen, fingers) currently down on the graph. One pointer
  // pans; two pointers pinch-zoom around their midpoint and pan with it.
  const pointers = new Map();
  let gesture = null;
  const start = () => {
    const ps = [...pointers.values()];
    if (ps.length === 1) {
      gesture = { kind: 'pan', cx: ps[0].x, cy: ps[0].y, base: { ...vb }, s: unitsPerPixel(), moved: false };
    } else if (ps.length === 2) {
      const mid = { clientX: (ps[0].x + ps[1].x) / 2, clientY: (ps[0].y + ps[1].y) / 2 };
      gesture = { kind: 'pinch', d: Math.hypot(ps[0].x - ps[1].x, ps[0].y - ps[1].y) || 1,
                  mid: mid, p: toGraph(mid), base: { ...vb }, s: unitsPerPixel(), moved: true };
    } else {
      gesture = null;
    }
  };
  svg.addEventListener('pointerdown', (e) => {
    if (e.pointerType === 'mouse' && e.button !== 0) return;
    pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
    start();
  });
  window.addEventListener('pointermove', (e) => {
    if (!pointers.has(e.pointerId) || !gesture) return;
    pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
    const ps = [...pointers.values()];
    if (gesture.kind === 'pan') {
      const dx = ps[0].x - gesture.cx, dy = ps[0].y - gesture.cy;
      if (Math.abs(dx) + Math.abs(dy) > 3) {
        gesture.moved = true;
        svg.classList.add('depgraph-dragging');
      }
      if (gesture.moved) {
        vb = { ...gesture.base, x: gesture.base.x - dx * gesture.s, y: gesture.base.y - dy * gesture.s };
        apply();
      }
    } else if (gesture.kind === 'pinch' && ps.length === 2) {
      const d = Math.hypot(ps[0].x - ps[1].x, ps[0].y - ps[1].y) || 1;
      zoomAt(gesture.p, gesture.d / d, gesture.base);
      // Follow the fingers' midpoint as well.
      const mx = (ps[0].x + ps[1].x) / 2 - gesture.mid.clientX;
      const my = (ps[0].y + ps[1].y) / 2 - gesture.mid.clientY;
      const s = gesture.s * (vb.w / gesture.base.w);
      vb.x -= mx * s; vb.y -= my * s;
      apply();
    }
  });
  // The click that ends a drag must not follow a link or toggle an edge.
  let suppressClickUntil = 0;
  svg.addEventListener('click', (e) => {
    if (Date.now() < suppressClickUntil) { e.preventDefault(); e.stopPropagation(); }
  }, { capture: true });
  // A double tap shows the whole graph (touch screens send no dblclick here).
  let lastTap = 0;
  const end = (e) => {
    if (!pointers.has(e.pointerId)) return;
    const wasTap = gesture && gesture.kind === 'pan' && !gesture.moved && pointers.size === 1;
    if (gesture && gesture.moved) suppressClickUntil = Date.now() + 300;
    pointers.delete(e.pointerId);
    svg.classList.remove('depgraph-dragging');
    start();                     // a remaining finger continues as a pan
    if (wasTap && e.pointerType === 'touch') {
      if (Date.now() - lastTap < 300) { vb = { ...home }; apply(); lastTap = 0; }
      else lastTap = Date.now();
    }
  };
  window.addEventListener('pointerup', end);
  window.addEventListener('pointercancel', end);
  svg.addEventListener('dblclick', (e) => {
    e.preventDefault();
    vb = { ...home };
    apply();
  });
}

function makeEdgesInteractive(evt) {
  let svg = evt.target;
  makeGraphPannable(svg);
  let viewBox = svg.viewBox.baseVal;
  let edges = document.getElementsByClassName('edge');

  Array.from(edges).forEach((edge) => {
    edge.addEventListener('click', clickEdge);
  });

  function clickEdge() {
    let edge = this;
    if (edge.classList.contains("edge-highlight")) {
      edge.classList.remove("edge-highlight");
      edge.classList.remove("text-highlight-edges");
    } else {
      edge.classList.add("edge-highlight");
      edge.classList.add("text-highlight-edges");
      animateEdge(edge);
    }
  }

  function animateEdge(edge) {
    let path = edge.querySelector('path');
    let polygon = edge.querySelector('polygon');
    let width = viewBox.width;
    let length = path.getTotalLength();
    let timeUnit = length / width;
    // Clear any previous transition
    path.style.transition = path.style.WebkitTransition = 'none';
    // Set up the starting positions
    path.style.strokeDasharray = length + ' ' + length;
    path.style.strokeDashoffset = length;
    // Trigger a layout so styles are calculated & the browser
    // picks up the starting position before animating
    path.getBoundingClientRect();
    // Define the transition
    path.style.transition = path.style.WebkitTransition = 'stroke-dashoffset ' + timeUnit + 's ease-in-out';
    path.style.strokeDashoffset = '0';

    polygon.style.transition = polygon.style.WebkitTransition = 'none';
    polygon.style.opacity = '0';
    polygon.style.transition = polygon.style.WebkitTransition = 'fill-opacity ' + timeUnit/2 + 's ease-in-out ' + timeUnit + 's';
    setTimeout(() => {
      polygon.style.opacity = '1';
    }, 1000 * timeUnit);
  }
}
