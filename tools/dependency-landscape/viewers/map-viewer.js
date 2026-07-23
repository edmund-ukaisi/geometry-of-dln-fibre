(() => {
  "use strict";
  const data = window.MAP_DATA;
  const meta = data.meta || {};
  const NS = "http://www.w3.org/2000/svg";
  const svg = document.getElementById("canvas");
  const stage = document.getElementById("stage");
  const tooltip = document.getElementById("tooltip");
  const modeEl = document.getElementById("mode");
  const edgeModeEl = document.getElementById("edgemode");
  const detailsEl = document.getElementById("details");
  const timelineEl = document.getElementById("timeline");
  const playEl = document.getElementById("play");

  if (!meta.mapPath) {
    document.getElementById("summary").innerHTML =
      "<h2>No plan layer</h2><p>No expeditions/*/map/claims.yaml at this snapshot.</p>";
    return;
  }

  const nodes = data.nodes;
  const live = nodes.filter(n => n.live);
  const byId = new Map(nodes.map(n => [n.id, n]));
  const events = data.events;
  const now = Math.floor(Date.now() / 1000);

  const STATUS_COLORS = {
    conjectured: "#64748b", proposed: "#64748b",
    adjudicated: "#f59e0b", drafted: "#f59e0b",
    stated: "#38bdf8", validated: "#38bdf8",
    "skeleton-linked": "#a78bfa", adopted: "#a78bfa", building: "#a78bfa",
    proven: "#4ade80", frozen: "#4ade80", landed: "#4ade80",
    refuted: "#fb7185",
    superseded: "#475569", retired: "#475569",
  };
  const BANKED = new Set(["proven", "frozen", "landed"]);
  const EXITED = new Set(["refuted", "superseded", "retired"]);
  const KIND_GLYPH = { claim: "●", notion: "◆", route: "➤" };
  const statusColor = s => STATUS_COLORS[s] || "#e879f9";
  const isOpen = n => !BANKED.has(n.status) && !EXITED.has(n.status);

  const esc = v => String(v ?? "").replace(/[&<>"']/g,
    c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  const day = ts => new Date(ts * 1000).toISOString().slice(5, 10);
  const stamp = ts => new Date(ts * 1000).toISOString().slice(0, 16).replace("T", " ");
  const make = (tag, attrs = {}, text = "") => {
    const el = document.createElementNS(NS, tag);
    for (const [k, v] of Object.entries(attrs)) el.setAttribute(k, v);
    if (text) el.textContent = text;
    return el;
  };

  // territory verdict: this tool's independent source-scan check of the anchor
  function terr(n) {
    const t = n.territory;
    if (!t) return { cls: "none", color: "#475569", text: "no lean anchor" };
    if (!t.exists) return { cls: "missing", color: "#fb7185", text: `anchor NOT FOUND in source: ${t.decl}` };
    if (t.coneSorries > 0) return {
      cls: "sorry", color: "#fbbf24",
      text: `${t.decl} — ${t.coneSorries} sorried decl(s) in its dependency cone (${t.coneSize} decls)` };
    return { cls: "clean", color: "#4ade80", text: `${t.decl} — cone source-clean (${t.coneSize} decls)` };
  }
  const disagrees = n => n.territory && (
    (BANKED.has(n.status) && n.territory.exists && n.territory.coneSorries > 0) ||
    (n.territory.exists === false));

  // -------------------------------------------------------------- playback state
  let current = events.length - 1;
  let selected = null;
  let playing = false;
  let timer = null;
  const atTip = () => current === events.length - 1;
  // At the tip render the enriched registry nodes (territory, battery); at a
  // historical step render that commit's authored snapshot verbatim.
  const frameNodes = () => atTip() ? live : (events[current].snapshot || []);
  const frameRoots = () => atTip() ? (meta.roots || []) : (events[current].roots || []);

  // ---------------------------------------------------------------- structure
  function structureLayout(list, roots) {
    const here = new Map(list.map(n => [n.id, n]));
    const depth = new Map();
    for (const r of roots) if (here.has(r)) depth.set(r, 0);
    if (!depth.size && list.length) depth.set(list[0].id, 0);
    const wanted = edgeModeEl.value;
    const followed = wanted === "needs" ? ["needs"]
      : wanted === "hard" ? ["needs", "discharges"] : ["needs", "discharges", "conjectured-toward"];
    for (let i = 0; i <= list.length; i++) {
      let changed = false;
      for (const n of list) {
        const dn = depth.get(n.id);
        if (dn === undefined) continue;
        for (const e of n.edges) {
          if (!followed.includes(e.type)) continue;
          if (!here.has(e.to) || roots.includes(e.to)) continue;
          const cand = dn + 1;
          if ((depth.get(e.to) ?? -1) < cand) { depth.set(e.to, cand); changed = true; }
        }
      }
      if (!changed) break;
    }
    let maxD = Math.max(0, ...depth.values());
    for (const n of list) if (!depth.has(n.id)) depth.set(n.id, maxD + 1);
    maxD = Math.max(0, ...depth.values());

    const rows = Array.from({ length: maxD + 1 }, () => []);
    for (const n of list) rows[depth.get(n.id)].push(n);
    const slot = new Map();
    rows.forEach(row => row.sort((a, b) => a.id.localeCompare(b.id))
      .forEach((n, i) => slot.set(n.id, i)));
    function bary(n) {
      const ns = [];
      for (const e of n.edges) if (slot.has(e.to)) ns.push(slot.get(e.to));
      for (const m of list) for (const e of m.edges)
        if (e.to === n.id && slot.has(m.id)) ns.push(slot.get(m.id));
      return ns.length ? ns.reduce((a, b) => a + b, 0) / ns.length : slot.get(n.id);
    }
    for (let pass = 0; pass < 3; pass++) {
      for (const row of rows) {
        row.sort((a, b) => bary(a) - bary(b));
        row.forEach((n, i) => slot.set(n.id, i));
      }
    }
    return { rows };
  }

  function renderStructure() {
    svg.replaceChildren();
    const list = frameNodes();
    const ev = events[current];
    const born = new Set(atTip() ? [] : ev.births);
    const moved = new Map(atTip() ? [] : ev.transitions.map(t => [t[0], t]));
    const { rows } = structureLayout(list, frameRoots());
    const stageW = stage.clientWidth;
    const NW = 208, NH = 42, GX = 26, GY = 46;
    const rowW = rows.map(r => r.length * (NW + GX));
    const width = Math.max(stageW, ...rowW, 600);
    const height = Math.max(stage.clientHeight, rows.length * (NH + GY) + 90);
    svg.setAttribute("width", width);
    svg.setAttribute("height", height);
    svg.setAttribute("viewBox", `0 0 ${width} ${height}`);

    const defs = make("defs");
    const m = make("marker", { id: "arr-needs", viewBox: "0 0 8 8", refX: 7, refY: 4,
                               markerWidth: 6, markerHeight: 6, orient: "auto" });
    m.appendChild(make("path", { d: "M0,0 L8,4 L0,8 z", fill: "rgba(148,163,184,.7)" }));
    defs.appendChild(m);
    svg.appendChild(defs);

    const pos = new Map();
    rows.forEach((row, d) => {
      const total = row.length * (NW + GX) - GX;
      row.forEach((n, i) => {
        pos.set(n.id, {
          x: width / 2 - total / 2 + i * (NW + GX) + NW / 2,
          y: 56 + d * (NH + GY) + (i % 2 ? 7 : 0),
        });
      });
    });

    const wanted = edgeModeEl.value;
    const edgeLayer = make("g");
    svg.appendChild(edgeLayer);
    const edgeEls = [];
    for (const n of list) {
      for (const e of n.edges) {
        if (wanted === "needs" && e.type !== "needs") continue;
        if (wanted === "hard" && !["needs", "discharges"].includes(e.type)) continue;
        const a = pos.get(e.to), b = pos.get(n.id);
        if (!a || !b) continue;
        const [from, to] = e.type === "needs" ? [a, b] : [b, a];
        const bend = Math.min(70, Math.abs(from.y - to.y) * .45);
        const p = make("path", {
          d: `M${from.x},${from.y - NH / 2} C${from.x},${from.y - NH / 2 - bend} ` +
             `${to.x},${to.y + NH / 2 + bend} ${to.x},${to.y + NH / 2}`,
          class: `map-edge ${["needs", "discharges", "conjectured-toward", "refutes"].includes(e.type) ? e.type : "other"}`,
          "stroke-width": e.type === "needs" ? 1.4 : 1.1,
          "marker-end": e.type === "needs" ? "url(#arr-needs)" : "",
        });
        p.dataset.a = n.id; p.dataset.b = e.to;
        edgeLayer.appendChild(p);
        edgeEls.push(p);
      }
    }

    for (const n of list) {
      const { x, y } = pos.get(n.id);
      const cls = ["map-node"];
      if (n.landmark) cls.push("landmark");
      if (selected === n.id) cls.push("selected");
      const g = make("g", { class: cls.join(" "),
                            transform: `translate(${x - NW / 2},${y - NH / 2})` });
      if (born.has(n.id) || moved.has(n.id)) {
        g.appendChild(make("rect", { x: -3, y: -3, width: NW + 6, height: NH + 6, rx: 7,
          fill: "none", stroke: born.has(n.id) ? "#f8fafc" : "#67e8f9",
          "stroke-width": 1.6, "stroke-dasharray": born.has(n.id) ? "3 3" : "" }));
      }
      g.appendChild(make("rect", { width: NW, height: NH, rx: 5, stroke: statusColor(n.status) }));
      g.appendChild(make("text", { x: 8, y: 15, class: "nid" },
        `${KIND_GLYPH[n.kind] || "○"} ${n.id.slice(0, 26)}`));
      if (n.landmark) g.appendChild(make("text", { x: NW - 26, y: 15, class: "nmark" }, "★"));
      if (atTip() && disagrees(n)) g.appendChild(make("text", { x: NW - 13, y: 15, class: "nflag" }, "!"));
      if (atTip()) {
        const t = terr(n);
        g.appendChild(make("circle", { cx: NW - 34, cy: 11, r: 3.4, fill: t.color }));
      }
      g.appendChild(make("text", { x: 8, y: 30, class: "nstatus", fill: statusColor(n.status) },
        n.status || "?"));
      const owner = (n.owner || "").split(/[:(]/)[0].trim();
      g.appendChild(make("text", { x: 8 + 7 * Math.min(16, (n.status || "?").length) + 8, y: 30,
                                   class: "nowner" }, owner.slice(0, 22)));
      const chips = atTip() && n.battery
        ? `${n.battery.guards.length}g${n.battery.kills.length ? "/" + n.battery.kills.length + "k" : ""}` : "";
      if (chips) g.appendChild(make("text", { x: NW - 32, y: 30, class: "nowner" }, chips));
      g.addEventListener("mousemove", ev2 => {
        for (const p of edgeEls) {
          const inc = p.dataset.a === n.id || p.dataset.b === n.id;
          p.classList.toggle("hot", inc);
          p.classList.toggle("dim", !inc);
        }
        const move = moved.get(n.id);
        showTip(ev2, `<strong>${esc(n.id)}</strong> ${n.landmark ? "★" : ""}<br>${esc(n.title || "")}` +
          `<br>${esc(n.status)} · ${esc(n.kind)} · ${esc(owner)}` +
          (move ? `<br>this step: ${esc(move[1])} → ${esc(move[2])}` : "") +
          (born.has(n.id) ? "<br>born this step" : "") +
          (atTip() ? `<br>${esc(terr(n).text)}` : ""));
      });
      g.addEventListener("mouseleave", () => {
        edgeEls.forEach(p => p.classList.remove("hot", "dim"));
        tooltip.style.display = "none";
      });
      g.addEventListener("click", () => select(n.id));
      svg.appendChild(g);
    }
    document.getElementById("top-axis").textContent =
      `ROOTS · the goal objects${atTip() ? " (tip)" : " as of " + stamp(ev.ts)}`;
    document.getElementById("bottom-axis").textContent = "DEEP PREREQUISITES · longest-path depth below the roots";
  }

  // ---------------------------------------------------------------- lifelines
  function renderLifelines() {
    svg.replaceChildren();
    const rows = nodes.slice();
    const t0 = Math.min(...rows.map(n => n.birth)) - 1800;
    const t1 = now;
    const GUT = 200, RH = 15, TOP = 46;
    const width = Math.max(stage.clientWidth, 900);
    const height = TOP + rows.length * RH + 40;
    svg.setAttribute("width", width);
    svg.setAttribute("height", height);
    svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
    const X = ts => GUT + (ts - t0) / (t1 - t0) * (width - GUT - 14);

    for (let d = Math.ceil(t0 / 86400) * 86400; d < t1; d += 86400) {
      svg.appendChild(make("line", { x1: X(d), y1: TOP - 8, x2: X(d), y2: height - 26, class: "life-grid" }));
      svg.appendChild(make("text", { x: X(d) + 2, y: height - 14, class: "life-day" }, day(d)));
    }
    const perDay = {};
    for (const e of events) perDay[Math.floor(e.ts / 86400)] = (perDay[Math.floor(e.ts / 86400)] || 0) + 1;
    const maxDay = Math.max(1, ...Object.values(perDay));
    for (const [dk, c] of Object.entries(perDay)) {
      const x = X(Number(dk) * 86400);
      const h = 4 + 16 * c / maxDay;
      svg.appendChild(make("rect", { x, y: TOP - 10 - h, width: Math.max(2, X(86400) - X(0) - 2),
                                     height: h, class: "life-commit-bar" }));
    }
    svg.appendChild(make("text", { x: GUT, y: 12, class: "life-day" },
      `map commits per day (${events.length} total) — click a bar to seek`));
    for (const [dk] of Object.entries(perDay)) {
      const x = X(Number(dk) * 86400);
      const hit = make("rect", { x, y: 0, width: Math.max(4, X(86400) - X(0)), height: TOP - 8,
                                 fill: "transparent", style: "cursor:pointer" });
      hit.addEventListener("click", () => {
        const target = Number(dk) * 86400 + 86399;
        let idx = 0;
        for (let i = 0; i < events.length; i++) if (events[i].ts <= target) idx = i;
        setStep(idx, false);
      });
      svg.appendChild(hit);
    }

    for (const ep of data.epochs) {
      svg.appendChild(make("line", { x1: X(ep.ts), y1: TOP - 24, x2: X(ep.ts), y2: height - 26, class: "life-epoch" }));
      svg.appendChild(make("text", { x: X(ep.ts) + 4, y: TOP - 14, class: "life-epoch-label" },
        `${ep.label} — ${ep.died} archived / ${ep.born} born`));
    }

    rows.forEach((n, i) => {
      const y = TOP + i * RH;
      const label = make("text", { x: GUT - 8, y: y + 9, "text-anchor": "end",
                                   class: `life-row-label${n.live ? "" : " dead"}` },
        `${n.landmark ? "★" : ""}${n.id.slice(0, 30)}`);
      label.addEventListener("click", () => select(n.id));
      svg.appendChild(label);
      const end = n.death ?? t1;
      for (let s = 0; s < n.segments.length; s++) {
        const [ts, status] = n.segments[s];
        const segEnd = s + 1 < n.segments.length ? n.segments[s + 1][0] : end;
        const r = make("rect", { x: X(ts), y: y + 2, width: Math.max(2, X(segEnd) - X(ts)),
                                 height: 9, rx: 2, fill: statusColor(status),
                                 opacity: n.live ? .95 : .38, class: "life-seg" });
        r.addEventListener("mousemove", ev => showTip(ev,
          `<strong>${esc(n.id)}</strong><br>${esc(status)} from ${stamp(ts)}` +
          `${segEnd < t1 ? " to " + stamp(segEnd) : " — now"}` +
          (n.death ? `<br>archived ${stamp(n.death)}` : "")));
        r.addEventListener("mouseleave", () => tooltip.style.display = "none");
        r.addEventListener("click", () => select(n.id));
        svg.appendChild(r);
      }
      for (const ts of n.ownerChanges)
        svg.appendChild(make("line", { x1: X(ts), y1: y, x2: X(ts), y2: y + 13, class: "life-tick" }));
      if (n.death) svg.appendChild(make("text", { x: X(n.death) + 2, y: y + 10,
        class: "life-day" }, "†"));
    });

    // the playback cursor
    const cx = X(atTip() ? t1 : events[current].ts);
    svg.appendChild(make("line", { x1: cx, y1: TOP - 24, x2: cx, y2: height - 26,
                                   stroke: "#f8fafc", "stroke-width": 1.2, opacity: .9 }));
    document.getElementById("top-axis").textContent = "STATUS LIFELINES · every node id ever authored, birth-ordered";
    document.getElementById("bottom-axis").textContent = "white ticks = owner changes · † = archived at re-root · amber = re-root · white line = playback cursor";
  }

  // ---------------------------------------------------------------- panels
  function pill(status) {
    return `<span class="pill" style="background:${statusColor(status)}">${esc(status || "?")}</span>`;
  }

  function renderSummary() {
    const kinds = {};
    for (const n of live) kinds[n.kind] = (kinds[n.kind] || 0) + 1;
    const landmarks = live.filter(n => n.landmark).length;
    const guards = data.battery.reduce((a, b) => a + (b.guards.length ? 1 : 0), 0);
    const kills = data.battery.reduce((a, b) => a + (b.kills.length ? 1 : 0), 0);
    document.getElementById("summary").innerHTML = `<h2>Plan · ${esc(meta.expedition || "?")}</h2>
      <div class="kpi-grid">
        <div class="kpi"><b>${live.length}</b><span>live nodes · ${meta.archivedCount} archived</span></div>
        <div class="kpi"><b>${meta.commitCount}</b><span>map commits</span></div>
        <div class="kpi"><b>${landmarks}/${meta.landmarkCap}</b><span>landmarks</span></div>
        <div class="kpi"><b>${data.battery.length}</b><span>battery · ${guards} guard / ${kills} kill</span></div>
        <div class="kpi"><b>${Object.entries(kinds).map(([k, v]) => `${v}${k[0]}`).join(" ")}</b><span>by kind (c/n/r)</span></div>
        <div class="kpi"><b>${data.epochs.length}</b><span>re-root(s)</span></div>
      </div>
      <div class="legend-note">roots: ${(meta.roots || []).map(esc).join(", ")} · authored update ${esc(meta.updated)} · mined @ ${esc(meta.head)}</div>`;
  }

  function renderLadder() {
    const counts = atTip()
      ? live.reduce((a, n) => (a[n.status] = (a[n.status] || 0) + 1, a), {})
      : events[current].counts;
    const order = Object.keys(counts).sort((a, b) => counts[b] - counts[a]);
    const max = Math.max(1, ...Object.values(counts));
    document.getElementById("ladder").innerHTML =
      `<h2>Maturity · ${atTip() ? "tip (asserted)" : "as of " + stamp(events[current].ts)}</h2>` +
      order.map(s => `<div class="role-row"><span class="role-label">${esc(s)}</span>
        <span class="role-track"><i class="role-fill" style="width:${100 * counts[s] / max}%;background:${statusColor(s)}"></i></span>
        <span class="role-value">${counts[s]}</span></div>`).join("");
  }

  function renderTerritory() {
    const anchored = live.filter(n => n.territory);
    const found = anchored.filter(n => n.territory.exists);
    const clean = found.filter(n => n.territory.coneSorries === 0);
    const bad = live.filter(disagrees);
    document.getElementById("territory").innerHTML = `<h2>Plan ⇄ territory (source scan, tip)</h2>
      <div class="kpi-grid">
        <div class="kpi"><b>${anchored.length}/${live.length}</b><span>lean-anchored</span></div>
        <div class="kpi"><b>${found.length}</b><span>anchors found in source</span></div>
        <div class="kpi"><b>${clean.length}</b><span>cones source-clean</span></div>
      </div>
      ${bad.length ? `<div class="subhead">Disagreements (asserted vs scanned)</div>
        <ul class="mini-list">${bad.map(n => `<li title="${esc(terr(n).text)}">
          <code>${esc(n.id)}</code> ${pill(n.status)} ${n.territory.exists === false ? "anchor missing" : `${n.territory.coneSorries} sorried in cone`}</li>`).join("")}</ul>`
        : `<div class="legend-note">no banked-status node has sorries in its scanned cone</div>`}
      <div class="legend-note">independent check — the survey/anchor-pin layer this substitutes for is unwired in the live harness</div>`;
  }

  function renderAlarms() {
    const items = [];
    const openAged = live.filter(isOpen)
      .map(n => ({ n, h: (now - n.segments[n.segments.length - 1][0]) / 3600 }))
      .sort((a, b) => b.h - a.h).slice(0, 3);
    for (const { n, h } of openAged)
      if (h > 24) items.push(`<li><code>${esc(n.id)}</code> in ${pill(n.status)} for ${h.toFixed(0)}h wall</li>`);
    for (const n of nodes.filter(n => n.ownerChanges.length >= 3))
      items.push(`<li><code>${esc(n.id)}</code> owner churn ×${n.ownerChanges.length}</li>`);
    for (const n of live.filter(n => n.landmark && EXITED.has(n.status)))
      items.push(`<li><code>${esc(n.id)}</code> landmark on exit status</li>`);
    for (const n of live.filter(n => n.titleChanges >= 3))
      items.push(`<li><code>${esc(n.id)}</code> title churn ×${n.titleChanges}</li>`);
    document.getElementById("alarms").innerHTML = `<h2>Flags (viewer-side, wall clock, tip)</h2>` +
      (items.length ? `<ul class="mini-list">${items.join("")}</ul>`
                    : `<div class="legend-note">nothing firing</div>`);
  }

  function renderDetails() {
    const n = selected && byId.get(selected);
    if (!n) { detailsEl.innerHTML = "<em>Select a node.</em>"; return; }
    const t = terr(n);
    const consumers = live.filter(m => m.edges.some(e => e.to === n.id));
    const link = id => `<a href="#" class="xlink" data-node="${esc(id)}"><code>${esc(id)}</code></a>`;
    const transitions = [];
    for (let s = 1; s < n.segments.length; s++)
      transitions.push(`<li>${stamp(n.segments[s][0])} ${esc(n.segments[s - 1][1])} → ${esc(n.segments[s][1])}</li>`);
    detailsEl.innerHTML = `<h2>${n.landmark ? "★ " : ""}${esc(n.id)}${n.live ? "" : " (archived)"}</h2>
      <p>${esc(n.title || "")}</p>
      <dl class="dl-compact">
        <dt>status</dt><dd>${pill(n.status)} since ${stamp(n.segments[n.segments.length - 1][0])}</dd>
        <dt>kind / tier</dt><dd>${esc(n.kind)} / ${esc(n.tier || "—")}</dd>
        <dt>owner</dt><dd>${esc(n.owner || "—")}</dd>
        <dt>born</dt><dd>${stamp(n.birth)}${n.death ? ` · archived ${stamp(n.death)}` : ""} · ${n.titleChanges} title edits</dd>
        <dt>territory</dt><dd style="color:${t.color}">${esc(t.text)}${
          n.territory && n.territory.exists ? ` <a class="xlink" href="declarations.html#q=${encodeURIComponent(n.territory.decl)}">open in graph</a>` : ""}</dd>
      </dl>
      ${n.prop ? `<div class="prop-box">${esc(n.prop)}</div>` : ""}
      ${n.notes ? `<p class="legend-note">${esc(n.notes)}</p>` : ""}
      ${n.edges.length ? `<div class="subhead">Edges out</div><ul class="mini-list">${
        n.edges.map(e => `<li>${esc(e.type)} → ${link(e.to)}</li>`).join("")}</ul>` : ""}
      ${consumers.length ? `<div class="subhead">Needed by</div><ul class="mini-list">${
        consumers.map(m => `<li>${link(m.id)} ${pill(m.status)}</li>`).join("")}</ul>` : ""}
      ${transitions.length ? `<div class="subhead">Status history</div><ul class="mini-list trans-list">${transitions.join("")}</ul>` : ""}
      ${n.battery ? `<div class="subhead">Battery</div><ul class="mini-list">${
        [...n.battery.guards.map(b => `<li>guard · ${esc(b)}</li>`),
         ...n.battery.kills.map(b => `<li>kill · ${esc(b)}</li>`)].join("")}</ul>` : ""}
      ${n.evidence.length ? `<div class="subhead">Evidence</div><ul class="mini-list">${
        n.evidence.map(e => `<li>${esc(e)}</li>`).join("")}</ul>` : ""}`;
    detailsEl.querySelectorAll("a[data-node]").forEach(a =>
      a.addEventListener("click", ev => { ev.preventDefault(); select(a.dataset.node); }));
  }

  function renderLegend() {
    const shown = [...new Set([...live, ...nodes].map(n => n.status))];
    document.getElementById("legend").innerHTML =
      `<strong>Status (asserted)</strong><br>` +
      shown.map(s => `<span><i style="background:${statusColor(s)};color:${statusColor(s)}"></i>${esc(s)}</span>`).join("") +
      `<br><strong>Territory dot (tip only)</strong><br>
       <span><i style="background:#4ade80;color:#4ade80"></i>anchor found, cone source-clean</span>
       <span><i style="background:#fbbf24;color:#fbbf24"></i>sorries in cone</span>
       <span><i style="background:#fb7185;color:#fb7185"></i>anchor missing</span>
       <span><i style="background:#475569;color:#475569"></i>no anchor</span>
       <br><strong>Edges</strong><br>
       <span>— needs (upward)</span> <span>┄ discharges</span> <span>· · conjectured-toward</span>
       <br><strong>Playback</strong> white dashed ring = born this map commit · cyan ring = status changed
       <br><strong>Kind</strong> ● claim ◆ notion ➤ route · ★ landmark · ! banked-but-sorried`;
  }

  // ---------------------------------------------------------------- playback
  function renderStep() {
    const ev = events[current];
    document.getElementById("step-time").textContent =
      `${stamp(ev.ts)} UTC · map commit ${current + 1}/${events.length}${atTip() ? " · TIP" : ""}`;
    document.getElementById("step-meta").textContent =
      `${ev.sha} · ${ev.total} nodes · +${ev.births.length} born / −${ev.deaths.length} archived / ${ev.transitions.length} transition(s)`;
    const subj = document.getElementById("step-subject");
    subj.textContent = ev.subject;
    subj.title = ev.subject +
      (ev.transitions.length ? "\n" + ev.transitions.map(t => `${t[0]}: ${t[1]} → ${t[2]}`).join("\n") : "");
  }

  function setStep(index, keepPlaying = true) {
    current = Math.max(0, Math.min(events.length - 1, index));
    timelineEl.value = current;
    renderStep();
    renderLadder();
    render();
    if (!keepPlaying) stop();
  }

  function stop() {
    playing = false;
    playEl.textContent = "▶";
    if (timer) { clearTimeout(timer); timer = null; }
  }

  function playTick() {
    if (!playing) return;
    if (current >= events.length - 1) { stop(); return; }
    setStep(current + 1);
    timer = setTimeout(playTick, 650);
  }

  function togglePlay() {
    if (playing) { stop(); return; }
    if (current >= events.length - 1) setStep(0);
    playing = true;
    playEl.textContent = "❚❚";
    timer = setTimeout(playTick, 650);
  }

  function showTip(ev, html) {
    const rect = stage.getBoundingClientRect();
    tooltip.innerHTML = html;
    tooltip.style.display = "block";
    tooltip.style.left = `${Math.min(rect.width - 380, ev.clientX - rect.left + 14)}px`;
    tooltip.style.top = `${Math.min(rect.height - 110, ev.clientY - rect.top + 12)}px`;
  }

  function select(id) {
    selected = id;
    renderDetails();
    render();
  }

  function render() {
    if (modeEl.value === "structure") renderStructure();
    else renderLifelines();
  }

  document.getElementById("subtitle").textContent =
    `${meta.mapPath} @ ${meta.head} — ${meta.commitCount} first-parent map commits; ` +
    `statuses are authored assertions, mined from git and checked against the source scan.`;
  timelineEl.max = events.length - 1;
  timelineEl.addEventListener("input", () => setStep(Number(timelineEl.value), false));
  playEl.addEventListener("click", togglePlay);
  document.getElementById("back").addEventListener("click", () => setStep(current - 1, false));
  document.getElementById("forward").addEventListener("click", () => setStep(current + 1, false));
  window.addEventListener("keydown", ev => {
    if (ev.target.tagName === "SELECT" || ev.target.tagName === "INPUT") return;
    if (ev.code === "Space") { ev.preventDefault(); togglePlay(); }
    else if (ev.code === "ArrowLeft") setStep(current - 1, false);
    else if (ev.code === "ArrowRight") setStep(current + 1, false);
  });
  modeEl.addEventListener("change", render);
  edgeModeEl.addEventListener("change", render);
  window.addEventListener("resize", render);
  stage.style.overflow = "auto";

  renderSummary();
  renderTerritory();
  renderAlarms();
  renderLegend();
  renderDetails();
  setStep(events.length - 1, false);
})();
