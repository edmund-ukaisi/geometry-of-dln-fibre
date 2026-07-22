(() => {
  "use strict";
  const data = window.GRAPH_DATA;
  const nodes = data.nodes;
  const edges = data.edges;
  const canvas = document.getElementById("graph");
  const wrap = document.getElementById("graph-wrap");
  const ctx = canvas.getContext("2d", { alpha: false });
  const viewSelect = document.getElementById("view-select");
  const search = document.getElementById("search");
  const results = document.getElementById("search-results");
  const stats = document.getElementById("stats");
  const details = document.getElementById("details");
  const tooltip = document.getElementById("tooltip");
  const fitButton = document.getElementById("fit");
  const labelsButton = document.getElementById("labels");

  const moduleColors = Object.assign({
    core: "#bfdbfe", validate: "#bbf7d0", rlct: "#a5f3fc", dln: "#c7d2fe",
    aggregator: "#d1d5db", synthetic: "#fed7aa", other: "#e5e7eb"
  }, data.meta.categoryColors || {});
  const kindColors = {
    theorem: "#bfdbfe", definition: "#dbeafe", opaque: "#c7d2fe", inductive: "#bbf7d0",
    constructor: "#dcfce7", recursor: "#e2e8f0", structure: "#a7f3d0", instance: "#fde68a",
    axiom: "#fecaca", quotient: "#ddd6fe", "open obligation": "#fed7aa", goal: "#fecaca",
    "type declaration": "#bbf7d0", other: "#e5e7eb"
  };
  const nodeWidth = data.kind === "module" ? 118 : 106;
  const nodeHeight = data.kind === "module" ? 22 : 17;
  const deps = Array.from({ length: nodes.length }, () => []);
  const consumers = Array.from({ length: nodes.length }, () => []);
  for (const [source, target] of edges) {
    deps[target].push(source);
    consumers[source].push(target);
  }

  let width = 1, height = 1, dpr = window.devicePixelRatio || 1;
  let centerX = 0, centerY = 0, scale = 1;
  let dragging = false, lastX = 0, lastY = 0;
  let selected = null, hovered = null;
  let labelsMode = 0; // 0 auto, 1 on, 2 off
  let searchMatches = new Set();
  let selectedComponent = null;
  let framePending = false;

  function resize() {
    const rect = wrap.getBoundingClientRect();
    width = Math.max(1, rect.width);
    height = Math.max(1, rect.height);
    dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(width * dpr);
    canvas.height = Math.round(height * dpr);
    canvas.style.width = `${width}px`;
    canvas.style.height = `${height}px`;
    scheduleDraw();
  }

  function visibleNode(node) {
    switch (viewSelect.value) {
      case "goal": return !!node.goalCone;
      case "frontier": return !!node.frontierCone;
      case "roots": return !!node.root;
      case "component": return selectedComponent == null || node.component === selectedComponent;
      default: return true;
    }
  }

  function visibleIds() {
    const result = [];
    for (let i = 0; i < nodes.length; i++) if (visibleNode(nodes[i])) result.push(i);
    return result;
  }

  function screenToWorld(x, y) {
    return { x: (x - width / 2) / scale + centerX, y: (y - height / 2) / scale + centerY };
  }

  function worldToScreen(x, y) {
    return { x: (x - centerX) * scale + width / 2, y: (y - centerY) * scale + height / 2 };
  }

  function fit(ids = visibleIds()) {
    if (!ids.length) return;
    let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
    for (const id of ids) {
      const node = nodes[id];
      minX = Math.min(minX, node.x - nodeWidth / 2);
      maxX = Math.max(maxX, node.x + nodeWidth / 2);
      minY = Math.min(minY, node.y - nodeHeight / 2);
      maxY = Math.max(maxY, node.y + nodeHeight / 2);
    }
    centerX = (minX + maxX) / 2;
    centerY = (minY + maxY) / 2;
    scale = Math.min((width - 60) / Math.max(1, maxX - minX), (height - 60) / Math.max(1, maxY - minY));
    scale = Math.max(0.002, Math.min(5, scale));
    scheduleDraw();
  }

  function centerNode(id, targetScale = null) {
    const node = nodes[id];
    centerX = node.x;
    centerY = node.y;
    if (targetScale != null) scale = Math.max(scale, targetScale);
    selected = id;
    selectedComponent = node.component;
    renderDetails();
    scheduleDraw();
  }

  function nodeStyle(node) {
    let fill = data.kind === "module"
      ? (moduleColors[node.category] || moduleColors.other)
      : (kindColors[node.kind] || "#e2e8f0");
    let stroke = "#64748b", line = 0.7;
    if (node.goal) { fill = "#fee2e2"; stroke = "#dc2626"; line = 2.4; }
    else if (node.frontier) { fill = "#ffedd5"; stroke = "#ea580c"; line = 2; }
    else if (node.hasSorry || node.sorryCount) { fill = "#fecaca"; stroke = "#b91c1c"; line = 1.8; }
    else if (node.active) { fill = "#ede9fe"; stroke = "#7c3aed"; line = 1.5; }
    else if (node.goalCone) { stroke = "#d97706"; line = 1.1; }
    if (searchMatches.has(node.id)) { stroke = "#0ea5e9"; line = 2.5; }
    if (selected === node.id) { stroke = "#111827"; line = 3; }
    return { fill, stroke, line };
  }

  function roundedRect(x, y, w, h, r) {
    const rr = Math.min(r, w / 2, h / 2);
    ctx.beginPath();
    ctx.moveTo(x + rr, y);
    ctx.arcTo(x + w, y, x + w, y + h, rr);
    ctx.arcTo(x + w, y + h, x, y + h, rr);
    ctx.arcTo(x, y + h, x, y, rr);
    ctx.arcTo(x, y, x + w, y, rr);
    ctx.closePath();
  }

  function scheduleDraw() {
    if (framePending) return;
    framePending = true;
    requestAnimationFrame(() => { framePending = false; draw(); });
  }

  function draw() {
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.fillStyle = "#ffffff";
    ctx.fillRect(0, 0, width, height);
    ctx.save();
    ctx.translate(width / 2, height / 2);
    ctx.scale(scale, scale);
    ctx.translate(-centerX, -centerY);

    const visible = new Uint8Array(nodes.length);
    let visibleCount = 0;
    const worldLeft = centerX - width / (2 * scale) - nodeWidth;
    const worldRight = centerX + width / (2 * scale) + nodeWidth;
    const worldTop = centerY - height / (2 * scale) - nodeHeight;
    const worldBottom = centerY + height / (2 * scale) + nodeHeight;
    for (let i = 0; i < nodes.length; i++) {
      const node = nodes[i];
      if (visibleNode(node)) { visible[i] = 1; visibleCount++; }
    }

    ctx.lineWidth = Math.max(0.35 / scale, 0.32);
    ctx.strokeStyle = visibleCount > 7000 ? "rgba(100,116,139,.10)" : "rgba(100,116,139,.23)";
    ctx.beginPath();
    for (const [source, target] of edges) {
      if (!visible[source] || !visible[target]) continue;
      const a = nodes[source], b = nodes[target];
      if ((a.x < worldLeft && b.x < worldLeft) || (a.x > worldRight && b.x > worldRight) ||
          (a.y < worldTop && b.y < worldTop) || (a.y > worldBottom && b.y > worldBottom)) continue;
      ctx.moveTo(a.x, a.y - nodeHeight / 2);
      const midY = (a.y + b.y) / 2;
      ctx.bezierCurveTo(a.x, midY, b.x, midY, b.x, b.y + nodeHeight / 2);
    }
    ctx.stroke();

    const showLabels = labelsMode === 1 || (labelsMode === 0 && (scale > (data.kind === "module" ? .32 : .55) || visibleCount < 250));
    for (let i = 0; i < nodes.length; i++) {
      if (!visible[i]) continue;
      const node = nodes[i];
      if (node.x < worldLeft || node.x > worldRight || node.y < worldTop || node.y > worldBottom) continue;
      const style = nodeStyle(node);
      const x = node.x - nodeWidth / 2, y = node.y - nodeHeight / 2;
      ctx.fillStyle = style.fill;
      ctx.strokeStyle = style.stroke;
      ctx.lineWidth = style.line / Math.max(scale, .3);
      ctx.setLineDash((node.root || !node.exact && data.kind === "declaration") ? [4 / scale, 2 / scale] : []);
      roundedRect(x, y, nodeWidth, nodeHeight, 3);
      ctx.fill();
      ctx.stroke();
      ctx.setLineDash([]);
      if (showLabels || selected === i || hovered === i || searchMatches.has(i)) {
        ctx.save();
        roundedRect(x + 2, y + 1, nodeWidth - 4, nodeHeight - 2, 2);
        ctx.clip();
        ctx.fillStyle = "#0f172a";
        ctx.font = `${data.kind === "module" ? 9 : 8}px ui-sans-serif, system-ui, sans-serif`;
        ctx.textBaseline = "middle";
        ctx.fillText(node.label, x + 4, node.y, nodeWidth - 8);
        ctx.restore();
      }
    }
    ctx.restore();
  }

  function nodeAt(screenX, screenY) {
    const world = screenToWorld(screenX, screenY);
    const tolerance = Math.max(2, 4 / scale);
    for (let i = nodes.length - 1; i >= 0; i--) {
      const node = nodes[i];
      if (!visibleNode(node)) continue;
      if (Math.abs(world.x - node.x) <= nodeWidth / 2 + tolerance &&
          Math.abs(world.y - node.y) <= nodeHeight / 2 + tolerance) return i;
    }
    return null;
  }

  function escapeHtml(text) {
    return String(text).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  }

  function neighborButtons(title, ids) {
    if (!ids.length) return "";
    const shown = ids.slice().sort((a, b) => nodes[a].name.localeCompare(nodes[b].name)).slice(0, 80);
    return `<h2>${escapeHtml(title)} (${ids.length})</h2><div class="neighbor-list">${shown.map(id =>
      `<button data-node="${id}" title="${escapeHtml(nodes[id].name)}">${escapeHtml(nodes[id].label)}</button>`).join("")}${ids.length > shown.length ? `<em>…${ids.length - shown.length} more</em>` : ""}</div>`;
  }

  function renderDetails() {
    if (selected == null) {
      details.innerHTML = "<em>Select a node.</em>";
      return;
    }
    const node = nodes[selected];
    const source = node.source || node.path || "";
    const sourceText = source ? `${source}${node.line ? `:${node.line}` : ""}` : "";
    details.innerHTML = `<h2>${escapeHtml(node.label)}</h2><code>${escapeHtml(node.name)}</code>
      <dl>
        <dt>module</dt><dd>${escapeHtml(node.module || node.name)}</dd>
        <dt>kind</dt><dd>${escapeHtml(node.kind || node.category || "module")}</dd>
        <dt>height</dt><dd>${node.height} (0 = top-level root)</dd>
        <dt>component</dt><dd>${node.component} (${node.componentSize} nodes)</dd>
        <dt>dependencies</dt><dd>${deps[selected].length}</dd>
        <dt>consumers</dt><dd>${consumers[selected].length}</dd>
        <dt>status</dt><dd>${node.synthetic ? "planning overlay" : node.exact === false ? "source-derived" : node.compiled === false ? "source-only module" : node.compiled == null ? "source-scanned (no build consulted)" : "elaborated/compiled"}${node.hasSorry || node.sorryCount ? "; contains sorry" : ""}</dd>
      </dl>
      ${sourceText ? `<p><strong>source:</strong><br><code>${escapeHtml(sourceText)}</code></p>` : ""}
      <button id="component-button">Show this component</button>
      ${neighborButtons("Depends on", deps[selected])}
      ${neighborButtons("Used by", consumers[selected])}`;
    details.querySelectorAll("button[data-node]").forEach(button => {
      button.addEventListener("click", () => centerNode(Number(button.dataset.node), 1.1));
    });
    const componentButton = document.getElementById("component-button");
    componentButton.addEventListener("click", () => {
      selectedComponent = node.component;
      viewSelect.value = "component";
      updateStats();
      fit();
    });
  }

  function updateStats() {
    const ids = visibleIds();
    const idSet = new Set(ids);
    let edgeCount = 0;
    for (const [source, target] of edges) if (idSet.has(source) && idSet.has(target)) edgeCount++;
    const m = data.meta;
    stats.innerHTML = `<h2>${data.kind === "module" ? "Module" : "Declaration"} graph</h2>
      <dl><dt>visible</dt><dd>${ids.length.toLocaleString()} nodes</dd><dt>edges</dt><dd>${edgeCount.toLocaleString()}</dd>
      <dt>all nodes</dt><dd>${m.nodeCount.toLocaleString()}</dd><dt>components</dt><dd>${m.componentCount.toLocaleString()}</dd>
      <dt>top roots</dt><dd>${m.rootCount.toLocaleString()}</dd><dt>snapshot</dt><dd>${escapeHtml(m.sourceHead)}</dd></dl>
      ${m.noBuild ? `<p>source-scanned; no Lean build consulted.</p>` : m.exactCount != null ? `<p>${m.exactCount.toLocaleString()} exact elaborated; ${m.sourceDerivedCount.toLocaleString()} source-derived.</p>` : `<p>${m.compiledCount.toLocaleString()} compiled; ${m.sourceOnlyCount.toLocaleString()} source-only.</p>`}`;
  }

  function updateSearch() {
    const query = search.value.trim().toLowerCase();
    searchMatches = new Set();
    results.innerHTML = "";
    if (!query) { scheduleDraw(); return; }
    const matches = [];
    for (let i = 0; i < nodes.length; i++) {
      const node = nodes[i];
      if (node.name.toLowerCase().includes(query) || (node.module || "").toLowerCase().includes(query)) {
        searchMatches.add(i);
        matches.push(i);
      }
    }
    for (const id of matches.slice(0, 40)) {
      const button = document.createElement("button");
      button.textContent = nodes[id].name;
      button.title = nodes[id].name;
      button.addEventListener("click", () => centerNode(id, 1.3));
      results.appendChild(button);
    }
    if (matches.length > 40) {
      const more = document.createElement("em");
      more.textContent = `…${matches.length - 40} more matches`;
      results.appendChild(more);
    }
    scheduleDraw();
  }

  canvas.addEventListener("mousedown", event => {
    dragging = true; lastX = event.clientX; lastY = event.clientY;
    canvas.classList.add("dragging");
  });
  window.addEventListener("mouseup", event => {
    if (!dragging) return;
    const moved = Math.hypot(event.clientX - lastX, event.clientY - lastY);
    dragging = false; canvas.classList.remove("dragging");
    if (moved < 3) {
      const rect = canvas.getBoundingClientRect();
      const id = nodeAt(event.clientX - rect.left, event.clientY - rect.top);
      if (id != null) centerNode(id);
    }
  });
  window.addEventListener("mousemove", event => {
    const rect = canvas.getBoundingClientRect();
    const x = event.clientX - rect.left, y = event.clientY - rect.top;
    if (dragging) {
      centerX -= (event.clientX - lastX) / scale;
      centerY -= (event.clientY - lastY) / scale;
      lastX = event.clientX; lastY = event.clientY;
      tooltip.style.display = "none";
      scheduleDraw();
      return;
    }
    if (x < 0 || y < 0 || x > width || y > height) return;
    const id = nodeAt(x, y);
    if (id !== hovered) { hovered = id; scheduleDraw(); }
    if (id == null) { tooltip.style.display = "none"; return; }
    tooltip.textContent = nodes[id].name;
    tooltip.style.display = "block";
    tooltip.style.left = `${Math.min(width - 430, Math.max(5, x + 12))}px`;
    tooltip.style.top = `${Math.min(height - 50, Math.max(5, y + 12))}px`;
  });
  canvas.addEventListener("wheel", event => {
    event.preventDefault();
    const rect = canvas.getBoundingClientRect();
    const x = event.clientX - rect.left, y = event.clientY - rect.top;
    const before = screenToWorld(x, y);
    const factor = Math.exp(-event.deltaY * 0.0012);
    scale = Math.max(0.001, Math.min(12, scale * factor));
    centerX = before.x - (x - width / 2) / scale;
    centerY = before.y - (y - height / 2) / scale;
    scheduleDraw();
  }, { passive: false });

  viewSelect.addEventListener("change", () => { updateStats(); fit(); });
  search.addEventListener("input", updateSearch);
  fitButton.addEventListener("click", () => fit());
  labelsButton.addEventListener("click", () => {
    labelsMode = (labelsMode + 1) % 3;
    labelsButton.textContent = `Labels: ${["auto", "on", "off"][labelsMode]}`;
    scheduleDraw();
  });
  window.addEventListener("resize", resize);

  resize();
  updateStats();
  requestAnimationFrame(() => fit());
})();
