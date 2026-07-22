(() => {
  "use strict";
  const graph = window.GRAPH_DATA;
  const real = graph.nodes.map((node, id) => ({ ...node, id })).filter(node => !node.synthetic);
  const realSet = new Set(real.map(node => node.id));
  const canvas = document.getElementById("canvas"), stage = document.getElementById("stage");
  const ctx = canvas.getContext("2d"), tooltip = document.getElementById("tooltip");
  const scopeEl = document.getElementById("scope"), blurEl = document.getElementById("blur"), groupingEl = document.getElementById("grouping"), thresholdEl = document.getElementById("threshold");
  const statsEl = document.getElementById("stats"), detailsEl = document.getElementById("details"), legendEl = document.getElementById("legend");
  const areas = graph.meta.areas || ["other"];
  const areaColors = Object.fromEntries(areas.map((name, i) => [name, (graph.meta.areaColors || [])[i] || "#94a3b8"]));
  const kinds = ["theorem", "definition", "type declaration", "instance", "opaque", "other"];
  const kindColors = { theorem: "#60a5fa", definition: "#34d399", "type declaration": "#c084fc", instance: "#f472b6", opaque: "#ef4444", other: "#94a3b8" };
  let width = 1, height = 1, dpr = 1, model = null, selected = null, hovered = null;

  function area(node) {
    return areas[node.area] || areas[areas.length - 1];
  }
  function kind(node) {
    return kinds.includes(node.kind) ? node.kind : "other";
  }
  function inScope(node) {
    if (scopeEl.value === "goal") return node.goalCone;
    if (scopeEl.value === "frontier") return node.frontierCone;
    return true;
  }
  function rebuild() {
    const blur = Number(blurEl.value), splitKinds = groupingEl.value === "kind";
    const selectedNodes = real.filter(inScope), included = new Set(selectedNodes.map(node => node.id));
    const groups = new Map(), nodeGroup = new Map();
    for (const node of selectedNodes) {
      const a = area(node), k = kind(node), band = Math.floor(node.height / blur);
      const key = splitKinds ? `${band}|${a}|${k}` : `${band}|${a}`;
      if (!groups.has(key)) groups.set(key, { key, band, area: a, kind: splitKinds ? k : null, count: 0, kinds: Object.fromEntries(kinds.map(name => [name, 0])), modules: new Map(), internal: 0, incoming: 0, outgoing: 0 });
      const group = groups.get(key); group.count++; group.kinds[k]++; group.modules.set(node.module, (group.modules.get(node.module) || 0) + 1); nodeGroup.set(node.id, key);
    }
    const edgeMap = new Map(); let rawEdges = 0;
    for (const [source, target] of graph.edges) {
      if (!realSet.has(source) || !realSet.has(target) || !included.has(source) || !included.has(target)) continue;
      rawEdges++;
      const a = nodeGroup.get(source), b = nodeGroup.get(target);
      if (a === b) { groups.get(a).internal++; continue; }
      const key = `${a}\u0000${b}`;
      edgeMap.set(key, (edgeMap.get(key) || 0) + 1);
    }
    const groupList = [...groups.values()]; const byKey = new Map(groupList.map((group, index) => [group.key, index]));
    const ribbons = [];
    for (const [key, weight] of edgeMap) {
      const [a, b] = key.split("\u0000"), source = byKey.get(a), target = byKey.get(b);
      groups.get(a).outgoing += weight; groups.get(b).incoming += weight;
      ribbons.push({ source, target, weight });
    }
    model = { groups: groupList, ribbons, selectedNodes, rawEdges, blur, splitKinds };
    selected = null; hovered = null; layout(); renderInfo(); draw();
  }
  function layout() {
    if (!model) return;
    const maxBand = Math.max(0, ...model.groups.map(group => group.band));
    const top = 82, bottom = 52, left = 65, right = 30;
    const lane = (width - left - right) / areas.length;
    const maxCount = Math.max(1, ...model.groups.map(group => group.count));
    for (const group of model.groups) {
      const areaIndex = areas.indexOf(group.area);
      let x = left + lane * (areaIndex + .5);
      if (model.splitKinds) x += (kinds.indexOf(group.kind) - (kinds.length - 1) / 2) * Math.min(18, lane / 8);
      group.x = x;
      group.y = top + (maxBand ? group.band / maxBand : 0) * Math.max(1, height - top - bottom);
      group.r = (model.splitKinds ? 2.5 : 4) + Math.sqrt(group.count / maxCount) * (model.splitKinds ? 14 : 24);
    }
    model.maxBand = maxBand; model.maxWeight = Math.max(1, ...model.ribbons.map(edge => edge.weight));
  }
  function resize() {
    const rect = stage.getBoundingClientRect(); width = rect.width; height = rect.height; dpr = window.devicePixelRatio || 1;
    canvas.width = Math.max(1, Math.round(width * dpr)); canvas.height = Math.max(1, Math.round(height * dpr));
    canvas.style.width = `${width}px`; canvas.style.height = `${height}px`; layout(); draw();
  }
  function pie(group) {
    if (model.splitKinds) {
      ctx.beginPath(); ctx.arc(group.x, group.y, group.r, 0, Math.PI * 2); ctx.fillStyle = kindColors[group.kind]; ctx.fill(); return;
    }
    let angle = -Math.PI / 2;
    for (const name of kinds) {
      const next = angle + Math.PI * 2 * group.kinds[name] / group.count;
      if (next > angle) { ctx.beginPath(); ctx.moveTo(group.x, group.y); ctx.arc(group.x, group.y, group.r, angle, next); ctx.closePath(); ctx.fillStyle = kindColors[name]; ctx.fill(); }
      angle = next;
    }
  }
  function drawArrow(edge, source, target) {
    if (edge.weight < Math.max(10, model.maxWeight * .07)) return;
    const angle = Math.atan2(target.y - source.y, target.x - source.x), size = 3 + Math.min(5, Math.sqrt(edge.weight) / 3);
    const x = target.x - Math.cos(angle) * (target.r + 2), y = target.y - Math.sin(angle) * (target.r + 2);
    ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x - Math.cos(angle - .5) * size, y - Math.sin(angle - .5) * size); ctx.lineTo(x - Math.cos(angle + .5) * size, y - Math.sin(angle + .5) * size); ctx.closePath(); ctx.fillStyle = "rgba(226,232,240,.58)"; ctx.fill();
  }
  function draw() {
    if (!model) return;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, width, height);
    const top = 82, bottom = 52, left = 65, right = 30, lane = (width - left - right) / areas.length;
    ctx.font = "10px ui-sans-serif,system-ui"; ctx.textAlign = "center"; ctx.textBaseline = "middle";
    for (let i = 0; i < areas.length; i++) {
      const x = left + lane * (i + .5); ctx.fillStyle = areaColors[areas[i]]; ctx.globalAlpha = .9; ctx.fillText(areas[i], x, 26);
      ctx.strokeStyle = areaColors[areas[i]]; ctx.globalAlpha = .08; ctx.lineWidth = Math.max(30, lane * .72); ctx.beginPath(); ctx.moveTo(x, 48); ctx.lineTo(x, height - 28); ctx.stroke();
    }
    ctx.globalAlpha = 1; ctx.lineWidth = 1; ctx.textAlign = "left";
    for (let band = 0; band <= model.maxBand; band++) {
      const y = top + (model.maxBand ? band / model.maxBand : 0) * Math.max(1, height - top - bottom);
      ctx.strokeStyle = band % 5 === 0 ? "rgba(148,163,184,.18)" : "rgba(148,163,184,.06)"; ctx.beginPath(); ctx.moveTo(48, y); ctx.lineTo(width - right, y); ctx.stroke();
      if (band % 2 === 0 || model.maxBand < 12) { ctx.fillStyle = "rgba(148,163,184,.65)"; ctx.font = "9px ui-sans-serif"; const a = band * model.blur, b = a + model.blur - 1; ctx.fillText(a === b ? `${a}` : `${a}–${b}`, 8, y + 3); }
    }
    const threshold = Number(thresholdEl.value);
    const ribbons = model.ribbons.filter(edge => edge.weight >= threshold).sort((a, b) => a.weight - b.weight);
    ctx.globalCompositeOperation = "screen";
    for (const edge of ribbons) {
      const source = model.groups[edge.source], target = model.groups[edge.target];
      const midY = (source.y + target.y) / 2;
      ctx.beginPath(); ctx.moveTo(source.x, source.y); ctx.bezierCurveTo(source.x, midY, target.x, midY, target.x, target.y);
      ctx.strokeStyle = areaColors[source.area]; ctx.globalAlpha = .06 + .28 * Math.sqrt(edge.weight / model.maxWeight); ctx.lineWidth = .35 + 5.5 * Math.sqrt(edge.weight / model.maxWeight); ctx.stroke(); drawArrow(edge, source, target);
    }
    ctx.globalCompositeOperation = "source-over"; ctx.globalAlpha = 1;
    for (let i = 0; i < model.groups.length; i++) {
      const group = model.groups[i]; ctx.shadowColor = areaColors[group.area]; ctx.shadowBlur = 10; pie(group); ctx.shadowBlur = 0;
      ctx.beginPath(); ctx.arc(group.x, group.y, group.r + 1.5, 0, Math.PI * 2); ctx.strokeStyle = selected === i ? "#fff" : hovered === i ? "#e2e8f0" : areaColors[group.area]; ctx.lineWidth = selected === i ? 2.5 : 1; ctx.globalAlpha = selected === i || hovered === i ? 1 : .75; ctx.stroke(); ctx.globalAlpha = 1;
    }
  }
  function groupAt(x, y) {
    if (!model) return null;
    let result = null, best = Infinity;
    for (let i = 0; i < model.groups.length; i++) { const g = model.groups[i], d = Math.hypot(x - g.x, y - g.y); if (d <= g.r + 5 && d < best) { result = i; best = d; } }
    return result;
  }
  function composition(group) { return kinds.filter(name => group.kinds[name]).map(name => `${name}: ${group.kinds[name].toLocaleString()}`).join("<br>"); }
  function renderDetails() {
    if (selected == null) { detailsEl.innerHTML = "<em>Select a population node.</em>"; return; }
    const g = model.groups[selected], modules = [...g.modules].sort((a, b) => b[1] - a[1]).slice(0, 8);
    const start = g.band * model.blur, end = start + model.blur - 1;
    detailsEl.innerHTML = `<h2>${g.area}${g.kind ? ` · ${g.kind}` : ""}</h2><dl><dt>layers</dt><dd>${start === end ? start : `${start}–${end}`}</dd><dt>declarations</dt><dd>${g.count.toLocaleString()}</dd><dt>incoming flow</dt><dd>${g.incoming.toLocaleString()}</dd><dt>outgoing flow</dt><dd>${g.outgoing.toLocaleString()}</dd><dt>internal edges</dt><dd>${g.internal.toLocaleString()}</dd></dl><p>${composition(g)}</p><h2>Largest modules</h2>${modules.map(([name, count]) => `${count.toLocaleString()} · ${name}`).join("<br>")}`;
  }
  function renderInfo() {
    if (!model) return;
    const shown = model.ribbons.filter(edge => edge.weight >= Number(thresholdEl.value)).length;
    statsEl.innerHTML = `<h2>Quotient DAG</h2><dl><dt>declarations</dt><dd>${model.selectedNodes.length.toLocaleString()}</dd><dt>quotient nodes</dt><dd>${model.groups.length.toLocaleString()}</dd><dt>raw DAG edges</dt><dd>${model.rawEdges.toLocaleString()}</dd><dt>weighted ribbons</dt><dd>${shown.toLocaleString()} / ${model.ribbons.length.toLocaleString()}</dd><dt>height bands</dt><dd>${model.maxBand + 1}</dd></dl>`;
    legendEl.innerHTML = `<strong>Declaration kind</strong><br>${kinds.map(name => `<span><i style="background:${kindColors[name]};color:${kindColors[name]}"></i>${name}</span>`).join("")}<br><strong>Horizontal lanes</strong><br>${areas.map(name => `<span><i style="background:${areaColors[name]};color:${areaColors[name]}"></i>${name}</span>`).join("")}`;
    renderDetails();
  }
  for (const el of [scopeEl, blurEl, groupingEl]) el.addEventListener("change", rebuild);
  thresholdEl.addEventListener("change", () => { renderInfo(); draw(); });
  canvas.addEventListener("mousemove", event => {
    const rect = canvas.getBoundingClientRect(), x = event.clientX - rect.left, y = event.clientY - rect.top, id = groupAt(x, y); hovered = id; draw();
    if (id == null) { tooltip.style.display = "none"; return; }
    const g = model.groups[id], start = g.band * model.blur, end = start + model.blur - 1;
    tooltip.style.display = "block"; tooltip.style.left = `${Math.min(width - 370, x + 12)}px`; tooltip.style.top = `${Math.min(height - 90, y + 12)}px`;
    tooltip.innerHTML = `<strong>${g.area}${g.kind ? ` · ${g.kind}` : ""}</strong><br>layers ${start === end ? start : `${start}–${end}`}<br>${g.count.toLocaleString()} declarations<br>${composition(g)}`;
  });
  canvas.addEventListener("mouseleave", () => { hovered = null; tooltip.style.display = "none"; draw(); });
  canvas.addEventListener("click", event => { const rect = canvas.getBoundingClientRect(); selected = groupAt(event.clientX - rect.left, event.clientY - rect.top); renderDetails(); draw(); });
  window.addEventListener("resize", resize);
  rebuild(); resize();
})();
