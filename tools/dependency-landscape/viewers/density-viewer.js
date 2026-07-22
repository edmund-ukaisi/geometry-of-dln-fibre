(() => {
  "use strict";
  const graph = window.GRAPH_DATA;
  const nodes = graph.nodes.filter(node => !node.synthetic);
  const svg = document.getElementById("density");
  const scopeSelect = document.getElementById("scope");
  const classificationSelect = document.getElementById("classification");
  const scaleSelect = document.getElementById("scale");
  const summary = document.getElementById("summary");
  const legend = document.getElementById("legend");
  const tooltip = document.getElementById("tooltip");
  const NS = "http://www.w3.org/2000/svg";

  const kindOrder = ["theorem", "definition", "type declaration", "instance", "opaque", "other"];
  const kindColors = { theorem: "#2563eb", definition: "#10b981", "type declaration": "#8b5cf6", instance: "#ec4899", opaque: "#dc2626", other: "#64748b" };
  const areaOrder = graph.meta.areas || ["other"];
  const areaColors = Object.fromEntries(areaOrder.map((name, i) => [name, (graph.meta.areaColors || [])[i] || "#64748b"]));

  function kind(node) {
    return kindOrder.includes(node.kind) ? node.kind : "other";
  }
  function area(node) {
    return areaOrder[node.area] || areaOrder[areaOrder.length - 1];
  }
  function inScope(node) {
    if (scopeSelect.value === "goal") return node.goalCone;
    if (scopeSelect.value === "frontier") return node.frontierCone;
    return true;
  }
  function make(tag, attrs = {}, text = "") {
    const el = document.createElementNS(NS, tag);
    for (const [name, value] of Object.entries(attrs)) el.setAttribute(name, value);
    if (text) el.textContent = text;
    return el;
  }
  function render() {
    svg.replaceChildren();
    const byKind = classificationSelect.value === "kind";
    const order = byKind ? kindOrder : areaOrder;
    const colors = byKind ? kindColors : areaColors;
    const classify = byKind ? kind : area;
    const selected = nodes.filter(inScope);
    const maxLayer = Math.max(0, ...selected.map(node => node.height));
    const rows = Array.from({ length: maxLayer + 1 }, () => Object.fromEntries(order.map(name => [name, 0])));
    for (const node of selected) rows[node.height][classify(node)]++;
    const totals = rows.map(row => order.reduce((sum, name) => sum + row[name], 0));
    const maxTotal = Math.max(1, ...totals);
    const x0 = 105, maxWidth = 980, top = 55, rowHeight = 23;
    const chartHeight = top + (maxLayer + 1) * rowHeight + 55;
    svg.setAttribute("viewBox", `0 0 1200 ${chartHeight}`);

    for (let layer = 0; layer <= maxLayer; layer++) {
      const y = top + layer * rowHeight;
      if (layer % 2 === 0) svg.appendChild(make("rect", { x: 60, y: y - 10, width: 1090, height: rowHeight, class: "row-bg" }));
      if (layer % 5 === 0) svg.appendChild(make("line", { x1: 60, y1: y - 11, x2: 1150, y2: y - 11, class: "grid" }));
      svg.appendChild(make("text", { x: 92, y: y + 4, "text-anchor": "end", class: "layer-label" }, `layer ${layer}`));
      const total = totals[layer];
      let width;
      if (scaleSelect.value === "percent") width = total ? maxWidth : 0;
      else if (scaleSelect.value === "linear") width = maxWidth * total / maxTotal;
      else width = maxWidth * Math.sqrt(total / maxTotal);
      let x = x0;
      for (const name of order) {
        const count = rows[layer][name];
        const segmentWidth = total ? width * count / total : 0;
        if (segmentWidth > 0) {
          const rect = make("rect", { x, y: y - 8, width: segmentWidth, height: 16, fill: colors[name], class: "segment", rx: 1 });
          rect.addEventListener("mousemove", event => {
            tooltip.style.display = "block";
            tooltip.style.left = `${event.clientX + 12}px`; tooltip.style.top = `${event.clientY + 12}px`;
            tooltip.innerHTML = `<strong>Layer ${layer}</strong><br>${name}: ${count.toLocaleString()} (${(100 * count / total).toFixed(1)}%)<br>total: ${total.toLocaleString()}`;
          });
          rect.addEventListener("mouseleave", () => tooltip.style.display = "none");
          svg.appendChild(rect);
        }
        x += segmentWidth;
      }
      svg.appendChild(make("text", { x: Math.min(1137, x + 5), y: y + 3, class: "count-label" }, total.toLocaleString()));
    }
    svg.appendChild(make("text", { x: x0, y: 20, class: "axis-label" }, "HIGH LEVEL · top-level results, frontier, and dangling declarations"));
    svg.appendChild(make("text", { x: x0, y: chartHeight - 15, class: "axis-label" }, "FOUNDATIONS · declarations shared by longer dependency chains"));
    summary.textContent = `${selected.length.toLocaleString()} declarations · ${maxLayer + 1} populated height slots · largest layer ${maxTotal.toLocaleString()}`;
    legend.innerHTML = order.map(name => `<span><i style="background:${colors[name]}"></i>${name}</span>`).join("");
  }
  for (const control of [scopeSelect, classificationSelect, scaleSelect]) control.addEventListener("change", render);
  render();
})();
