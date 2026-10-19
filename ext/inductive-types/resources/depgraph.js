// The graph fits the window; the mouse wheel zooms around the pointer,
// dragging pans, and a double click shows the whole graph again.
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

  svg.addEventListener('wheel', (e) => {
    e.preventDefault();
    const p = toGraph(e);
    // Proportional to the wheel distance: about 10% per notch (deltaY ≈ 100 px),
    // and smooth on touchpads; line or page deltas are scaled to pixels.
    const pixels = e.deltaY * (e.deltaMode === 1 ? 33 : e.deltaMode === 2 ? 800 : 1);
    const factor = Math.exp(Math.max(-0.5, Math.min(0.5, pixels * 0.001)));
    const w = Math.min(home.w, Math.max(home.w / 40, vb.w * factor));
    const k = w / vb.w;
    vb = { x: p.x - (p.x - vb.x) * k, y: p.y - (p.y - vb.y) * k, w: w, h: vb.h * k };
    apply();
  }, { passive: false });

  let drag = null;
  svg.addEventListener('pointerdown', (e) => {
    if (e.button !== 0) return;
    drag = { cx: e.clientX, cy: e.clientY, x: vb.x, y: vb.y, s: unitsPerPixel(), moved: false };
  });
  window.addEventListener('pointermove', (e) => {
    if (!drag) return;
    const dx = e.clientX - drag.cx, dy = e.clientY - drag.cy;
    if (Math.abs(dx) + Math.abs(dy) > 3) {
      drag.moved = true;
      svg.classList.add('depgraph-dragging');
    }
    if (drag.moved) {
      vb.x = drag.x - dx * drag.s;
      vb.y = drag.y - dy * drag.s;
      apply();
    }
  });
  // The click that ends a drag must not follow a link or toggle an edge.
  let suppressClickUntil = 0;
  svg.addEventListener('click', (e) => {
    if (Date.now() < suppressClickUntil) { e.preventDefault(); e.stopPropagation(); }
  }, { capture: true });
  window.addEventListener('pointerup', () => {
    if (drag && drag.moved) suppressClickUntil = Date.now() + 300;
    drag = null;
    svg.classList.remove('depgraph-dragging');
  });
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
