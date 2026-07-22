(() => {
  "use strict";

  const history = window.HISTORY_DATA;
  const meta = history.meta;
  const areas = meta.areas;
  const kinds = meta.kinds;
  const roles = meta.roles;
  const lane = meta.laneMeta || {};
  const fallbackPalette = ["#38bdf8", "#22d3ee", "#4ade80", "#a78bfa", "#fbbf24", "#fb7185", "#94a3b8"];
  const areaOrder = lane.areaOrder || areas.map((_, i) => i);
  const roleOrder = lane.roleOrder || roles.map((_, i) => i);
  const areaColors = lane.areaColors || areas.map((_, i) => fallbackPalette[i % fallbackPalette.length]);
  const roleColors = lane.roleColors || roles.map((_, i) => fallbackPalette[i % fallbackPalette.length]);
  const kindColors = ["#60a5fa", "#34d399", "#c084fc", "#f472b6", "#ef4444", "#94a3b8"];
  const roleShort = lane.roleShort || roles;
  const areaShort = lane.areaShort || areas;
  const goalLabel = meta.goalLabel || "goal cone";
  const headerP = document.querySelector("header p");
  if (headerP && meta.branch) {
    headerP.textContent = `Hourly playback of ${meta.branch}'s source-resolved declaration DAG, by first-parent integration time.`;
  }
  const scopeGoalOption = document.querySelector('#scope option[value="goal"]');
  if (scopeGoalOption) scopeGoalOption.textContent = goalLabel;

  const $ = id => document.getElementById(id);
  const stage = $("stage");
  const canvas = $("canvas");
  const ctx = canvas.getContext("2d");
  const tooltip = $("tooltip");
  const timelineEl = $("timeline");
  const playEl = $("play");
  const backEl = $("back");
  const forwardEl = $("forward");
  const speedEl = $("speed");
  const blurEl = $("blur");
  const scopeEl = $("scope");
  const lanesEl = $("lanes");
  const groupingEl = $("grouping");
  const thresholdEl = $("threshold");
  const bucketTimeEl = $("bucket-time");
  const commitMetaEl = $("commit-meta");
  const commitSubjectEl = $("commit-subject");
  const kpisEl = $("kpis");
  const deltaEl = $("delta");
  const activityEl = $("activity");
  const semanticsEl = $("semantics");
  const hubsEl = $("hubs");
  const detailsEl = $("details");
  const legendEl = $("legend");
  const topAxisEl = $("top-axis");
  const scopeBadgeEl = $("scope-badge");
  const spark = $("spark");
  const sparkCtx = spark.getContext("2d");

  let width = 1;
  let height = 1;
  let dpr = 1;
  let currentFrame = history.timeline.length - 1;
  let model = null;
  let selected = null;
  let hovered = null;
  let playing = false;
  let timer = null;
  let modelCache = new Map();
  let globalMaxCount = 1;
  let globalMaxWeight = 1;
  let globalLaneMass = [];
  const globalMaxHeight = Math.max(0, ...history.states.map(state => state.maxHeight));
  const number = new Intl.NumberFormat("en-GB", { maximumFractionDigits: 0 });

  function esc(value) {
    return String(value).replace(/[&<>"']/g, char => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[char]));
  }

  function fmt(value) { return number.format(value || 0); }
  function pct(part, whole) { return whole ? `${(100 * part / whole).toFixed(part / whole < .1 ? 1 : 0)}%` : "0%"; }
  function signed(value) { return value > 0 ? `+${fmt(value)}` : value < 0 ? `−${fmt(-value)}` : "0"; }
  function signClass(value) { return value > 0 ? "positive" : value < 0 ? "negative" : ""; }
  function basename(name) { return name ? name.split(".").pop() : "—"; }
  function duration(seconds) {
    const absolute = Math.abs(seconds);
    if (absolute < 60) return `${absolute}s`;
    const minutes = Math.floor(absolute / 60);
    const remainder = absolute % 60;
    return `${minutes}m${remainder ? ` ${remainder}s` : ""}`;
  }
  function rgba(hex, alpha) {
    const value = parseInt(hex.slice(1), 16);
    return `rgba(${value >> 16},${(value >> 8) & 255},${value & 255},${alpha})`;
  }

  function viewConfig() {
    const byRole = lanesEl.value === "role";
    return {
      laneField: byRole ? 3 : 1,
      crossField: byRole ? 1 : 3,
      laneNames: byRole ? roles : areas,
      crossNames: byRole ? areas : roles,
      laneShort: byRole ? roleShort : areaShort,
      laneColors: byRole ? roleColors : areaColors,
      crossColors: byRole ? areaColors : roleColors,
      laneOrder: byRole ? roleOrder : areaOrder,
      crossOrder: byRole ? areaOrder : roleOrder,
      stateCounts: byRole ? "roleCounts" : "areaCounts",
      stateGoalCounts: byRole ? "goalRoleCounts" : "goalAreaCounts",
      byRole,
    };
  }

  function aggregateState(stateIndex) {
    const cacheKey = [stateIndex, blurEl.value, scopeEl.value, lanesEl.value, groupingEl.value].join("|");
    if (modelCache.has(cacheKey)) return modelCache.get(cacheKey);
    const state = history.states[stateIndex];
    const blur = Number(blurEl.value);
    const goalOnly = scopeEl.value === "goal";
    const strands = groupingEl.value === "strands";
    const cfg = viewConfig();
    const groups = new Map();
    const atomicToKey = Array(state.groups.length).fill(null);

    for (let i = 0; i < state.groups.length; i++) {
      const atomic = state.groups[i];
      const count = atomic[goalOnly ? 6 : 4];
      if (!count) continue;
      const band = Math.floor(atomic[0] / blur);
      const lane = atomic[cfg.laneField];
      const cross = strands ? atomic[cfg.crossField] : -1;
      const key = `${band}|${lane}|${cross}`;
      if (!groups.has(key)) {
        groups.set(key, {
          key, band, lane, cross, count: 0, fullCount: 0, goalCount: 0,
          sorry: 0, internal: 0, incoming: 0, outgoing: 0,
          kinds: Array(kinds.length).fill(0), areas: Array(areas.length).fill(0), roles: Array(roles.length).fill(0),
        });
      }
      const group = groups.get(key);
      group.count += count;
      group.fullCount += atomic[4];
      group.goalCount += atomic[6];
      group.sorry += atomic[goalOnly ? 9 : 8];
      group.internal += atomic[goalOnly ? 7 : 5];
      group.kinds[atomic[2]] += count;
      group.areas[atomic[1]] += count;
      group.roles[atomic[3]] += count;
      atomicToKey[i] = key;
    }

    const edgeWeights = new Map();
    for (const edge of state.edges) {
      const weight = edge[goalOnly ? 3 : 2];
      if (!weight) continue;
      const sourceKey = atomicToKey[edge[0]];
      const targetKey = atomicToKey[edge[1]];
      if (sourceKey == null || targetKey == null) continue;
      if (sourceKey === targetKey) {
        groups.get(sourceKey).internal += weight;
        continue;
      }
      const key = `${sourceKey}\u0000${targetKey}`;
      const current = edgeWeights.get(key) || { weight: 0, goalWeight: 0 };
      current.weight += weight;
      current.goalWeight += edge[3];
      edgeWeights.set(key, current);
    }

    const groupList = [...groups.values()];
    const byKey = new Map(groupList.map((group, index) => [group.key, index]));
    const edges = [];
    for (const [key, weights] of edgeWeights) {
      const [sourceKey, targetKey] = key.split("\u0000");
      const source = byKey.get(sourceKey);
      const target = byKey.get(targetKey);
      groupList[source].outgoing += weights.weight;
      groupList[target].incoming += weights.weight;
      edges.push({ source, target, weight: weights.weight, goalWeight: weights.goalWeight });
    }
    const laneCounts = Array(cfg.laneNames.length).fill(0);
    for (const group of groupList) laneCounts[group.lane] += group.count;
    const result = { stateIndex, state, groups: groupList, edges, laneCounts, blur, goalOnly, strands, cfg };
    modelCache.set(cacheKey, result);
    return result;
  }

  function calibrate() {
    modelCache = new Map();
    globalMaxCount = 1;
    globalMaxWeight = 1;
    const cfg = viewConfig();
    globalLaneMass = Array(cfg.laneNames.length).fill(0);
    const countField = scopeEl.value === "goal" ? cfg.stateGoalCounts : cfg.stateCounts;
    for (let i = 0; i < history.states.length; i++) {
      const state = history.states[i];
      const candidate = aggregateState(i);
      for (const group of candidate.groups) globalMaxCount = Math.max(globalMaxCount, group.count);
      for (const edge of candidate.edges) globalMaxWeight = Math.max(globalMaxWeight, edge.weight);
      state[countField].forEach((count, lane) => { globalLaneMass[lane] = Math.max(globalLaneMass[lane], count); });
    }
  }

  function makeLanes(cfg, left, right) {
    const available = Math.max(1, width - left - right);
    const minimum = Math.min(54, available / cfg.laneOrder.length * .38);
    const remainder = Math.max(0, available - minimum * cfg.laneOrder.length);
    const weights = cfg.laneOrder.map(lane => Math.pow(Math.max(1, globalLaneMass[lane]), .36));
    const totalWeight = weights.reduce((sum, value) => sum + value, 0) || 1;
    const lanes = [];
    let cursor = left;
    cfg.laneOrder.forEach((lane, orderIndex) => {
      const laneWidth = minimum + remainder * weights[orderIndex] / totalWeight;
      lanes.push({ id: lane, x0: cursor, x1: cursor + laneWidth, width: laneWidth, center: cursor + laneWidth / 2 });
      cursor += laneWidth;
    });
    lanes[lanes.length - 1].x1 = width - right;
    lanes[lanes.length - 1].width = lanes[lanes.length - 1].x1 - lanes[lanes.length - 1].x0;
    lanes[lanes.length - 1].center = (lanes[lanes.length - 1].x0 + lanes[lanes.length - 1].x1) / 2;
    return lanes;
  }

  function layout() {
    if (!model) return;
    const top = 80;
    const bottom = 48;
    const left = 48;
    const right = 18;
    const maxBand = Math.floor(globalMaxHeight / model.blur);
    const lanes = makeLanes(model.cfg, left, right);
    const byLane = new Map(lanes.map(lane => [lane.id, lane]));
    for (const group of model.groups) {
      const lane = byLane.get(group.lane);
      if (model.strands) {
        const slot = model.cfg.crossOrder.indexOf(group.cross);
        const padding = Math.min(10, lane.width * .07);
        const usable = Math.max(1, lane.width - 2 * padding);
        group.x = lane.x0 + padding + (slot + .5) * usable / model.cfg.crossOrder.length;
      } else {
        group.x = lane.center;
      }
      group.y = top + (maxBand ? group.band / maxBand : 0) * Math.max(1, height - top - bottom);
      const radiusLimit = model.blur === 1 ? 10 : model.strands ? 15 : 23;
      group.r = 2.5 + Math.sqrt(group.count / globalMaxCount) * radiusLimit;
    }
    model.maxBand = maxBand;
    model.lanes = lanes;
    model.top = top;
    model.bottom = bottom;
    model.left = left;
    model.right = right;
  }

  function resize() {
    const rect = stage.getBoundingClientRect();
    width = rect.width;
    height = rect.height;
    dpr = window.devicePixelRatio || 1;
    canvas.width = Math.max(1, Math.round(width * dpr));
    canvas.height = Math.max(1, Math.round(height * dpr));
    canvas.style.width = `${width}px`;
    canvas.style.height = `${height}px`;
    layout();
    draw();
    resizeSpark();
  }

  function drawPie(group) {
    let angle = -Math.PI / 2;
    for (let kind = 0; kind < kinds.length; kind++) {
      const next = angle + Math.PI * 2 * group.kinds[kind] / group.count;
      if (next > angle) {
        ctx.beginPath();
        ctx.moveTo(group.x, group.y);
        ctx.arc(group.x, group.y, group.r, angle, next);
        ctx.closePath();
        ctx.fillStyle = kindColors[kind];
        ctx.fill();
      }
      angle = next;
    }
  }

  function ribbonPath(source, target) {
    const delta = Math.abs(source.y - target.y);
    const bend = Math.min(delta * .48, 90);
    ctx.beginPath();
    ctx.moveTo(source.x, source.y);
    ctx.bezierCurveTo(source.x, source.y - bend, target.x, target.y + bend, target.x, target.y);
  }

  function drawArrow(edge, source, target) {
    if (edge.weight < Math.max(Number(thresholdEl.value), globalMaxWeight * .035)) return;
    const angle = Math.atan2(target.y - source.y, target.x - source.x);
    const size = 3 + Math.min(5, Math.sqrt(edge.weight) / 3);
    const x = target.x - Math.cos(angle) * (target.r + 2);
    const y = target.y - Math.sin(angle) * (target.r + 2);
    ctx.beginPath();
    ctx.moveTo(x, y);
    ctx.lineTo(x - Math.cos(angle - .5) * size, y - Math.sin(angle - .5) * size);
    ctx.lineTo(x - Math.cos(angle + .5) * size, y - Math.sin(angle + .5) * size);
    ctx.closePath();
    ctx.fillStyle = "rgba(226,232,240,.55)";
    ctx.fill();
  }

  function draw() {
    if (!model) return;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, width, height);
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";

    for (const lane of model.lanes) {
      const color = model.cfg.laneColors[lane.id];
      ctx.fillStyle = rgba(color, .035);
      ctx.fillRect(lane.x0 + 1, 42, lane.width - 2, Math.max(0, height - 70));
      ctx.strokeStyle = rgba(color, .13);
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(lane.x0, 42);
      ctx.lineTo(lane.x0, height - 28);
      ctx.stroke();
      ctx.fillStyle = color;
      ctx.font = "600 9px ui-sans-serif,system-ui";
      ctx.fillText(model.cfg.laneShort[lane.id], lane.center, 19, Math.max(30, lane.width - 7));
      ctx.fillStyle = "rgba(203,213,225,.58)";
      ctx.font = "8px ui-monospace,SFMono-Regular,Menlo,monospace";
      ctx.fillText(`${fmt(model.laneCounts[lane.id])} decl`, lane.center, 32, Math.max(30, lane.width - 7));
    }
    const lastLane = model.lanes[model.lanes.length - 1];
    ctx.strokeStyle = "rgba(148,163,184,.12)";
    ctx.beginPath();
    ctx.moveTo(lastLane.x1, 42);
    ctx.lineTo(lastLane.x1, height - 28);
    ctx.stroke();

    ctx.textAlign = "left";
    for (let band = 0; band <= model.maxBand; band++) {
      const y = model.top + (model.maxBand ? band / model.maxBand : 0) * Math.max(1, height - model.top - model.bottom);
      ctx.strokeStyle = band % 5 === 0 ? "rgba(148,163,184,.17)" : "rgba(148,163,184,.055)";
      ctx.beginPath();
      ctx.moveTo(model.left, y);
      ctx.lineTo(width - model.right, y);
      ctx.stroke();
      if (band % 2 === 0 || model.maxBand < 12) {
        const a = band * model.blur;
        const b = a + model.blur - 1;
        ctx.fillStyle = "rgba(148,163,184,.62)";
        ctx.font = "8px ui-sans-serif,system-ui";
        ctx.fillText(a === b ? `${a}` : `${a}–${b}`, 7, y + 3);
      }
    }

    if (!model.groups.length) {
      ctx.fillStyle = "#94a3b8";
      ctx.font = "16px ui-sans-serif,system-ui";
      ctx.textAlign = "center";
      ctx.fillText(model.goalOnly ? `No ${goalLabel} in this snapshot` : "No explicit Lean declarations in this snapshot", width / 2, height / 2);
      return;
    }

    const threshold = Number(thresholdEl.value);
    const ribbons = model.edges.filter(edge => edge.weight >= threshold).sort((a, b) => a.weight - b.weight);
    ctx.globalCompositeOperation = "screen";
    for (const edge of ribbons) {
      const source = model.groups[edge.source];
      const target = model.groups[edge.target];
      ribbonPath(source, target);
      ctx.strokeStyle = model.cfg.laneColors[source.lane];
      ctx.globalAlpha = .045 + .30 * Math.sqrt(edge.weight / globalMaxWeight);
      ctx.lineWidth = .3 + 6.5 * Math.sqrt(edge.weight / globalMaxWeight);
      ctx.stroke();
      if (!model.goalOnly && edge.goalWeight > 0) {
        ribbonPath(source, target);
        ctx.strokeStyle = "#67e8f9";
        ctx.globalAlpha = .10 + .25 * Math.sqrt(edge.goalWeight / globalMaxWeight);
        ctx.lineWidth = .25 + 2.5 * Math.sqrt(edge.goalWeight / globalMaxWeight);
        ctx.stroke();
      }
      ctx.globalAlpha = 1;
      drawArrow(edge, source, target);
    }
    ctx.globalCompositeOperation = "source-over";
    ctx.globalAlpha = 1;

    for (let i = 0; i < model.groups.length; i++) {
      const group = model.groups[i];
      const laneColor = model.cfg.laneColors[group.lane];
      const crossColor = group.cross >= 0 ? model.cfg.crossColors[group.cross] : laneColor;
      ctx.shadowColor = crossColor;
      ctx.shadowBlur = 9;
      drawPie(group);
      ctx.shadowBlur = 0;
      ctx.beginPath();
      ctx.arc(group.x, group.y, group.r + 1.2, 0, Math.PI * 2);
      ctx.strokeStyle = selected === i ? "#fff" : hovered === i ? "#e2e8f0" : laneColor;
      ctx.lineWidth = selected === i ? 2.4 : 1;
      ctx.globalAlpha = selected === i || hovered === i ? 1 : .78;
      ctx.stroke();
      if (!model.goalOnly && group.goalCount > 0) {
        ctx.beginPath();
        ctx.arc(group.x, group.y, group.r + 2.8, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * group.goalCount / group.count);
        ctx.strokeStyle = "#67e8f9";
        ctx.lineWidth = 1.35;
        ctx.globalAlpha = .85;
        ctx.stroke();
      }
      ctx.globalAlpha = 1;
    }
  }

  function groupAt(x, y) {
    if (!model) return null;
    let result = null;
    let best = Infinity;
    for (let i = 0; i < model.groups.length; i++) {
      const group = model.groups[i];
      const distance = Math.hypot(x - group.x, y - group.y);
      if (distance <= group.r + 5 && distance < best) { result = i; best = distance; }
    }
    return result;
  }

  function composition(group) {
    return kinds.map((name, index) => [name, group.kinds[index]])
      .filter(([, count]) => count)
      .map(([name, count]) => `${esc(name)}: ${fmt(count)}`)
      .join(" · ");
  }

  function groupTitle(group) {
    const lane = model.cfg.laneNames[group.lane];
    const cross = group.cross >= 0 ? ` · ${model.cfg.crossNames[group.cross]}` : "";
    return `${lane}${cross}`;
  }

  function renderDetails() {
    if (selected == null || !model.groups[selected]) {
      detailsEl.innerHTML = "<em>Select a population node.</em>";
      return;
    }
    const group = model.groups[selected];
    const start = group.band * model.blur;
    const end = start + model.blur - 1;
    const goalRow = model.goalOnly ? "" : `<dt>in goal cone</dt><dd>${fmt(group.goalCount)} · ${pct(group.goalCount, group.count)}</dd>`;
    detailsEl.innerHTML = `<h2>${esc(groupTitle(group))}</h2><dl>
      <dt>dependency layers</dt><dd>${start === end ? start : `${start}–${end}`}</dd>
      <dt>declarations</dt><dd>${fmt(group.count)}</dd>${goalRow}
      <dt>incoming / outgoing</dt><dd>${fmt(group.incoming)} / ${fmt(group.outgoing)}</dd>
      <dt>internal edges</dt><dd>${fmt(group.internal)}</dd>
      <dt>sorry tokens</dt><dd>${fmt(group.sorry)}</dd>
    </dl><p>${composition(group)}</p>`;
  }

  function renderKpis(state, shownRibbons) {
    const scopedDeclarations = model.goalOnly ? state.goalDeclarationCount : state.declarationCount;
    const scopedEdges = model.goalOnly ? state.goalEdgeCount : state.edgeCount;
    const scopedSorry = model.goalOnly ? state.goalSorryCount : state.sorryCount;
    kpisEl.innerHTML = `<h2>Snapshot · ${model.goalOnly ? goalLabel : "full codebase"}</h2><div class="kpi-grid">
      <div class="kpi"><b>${fmt(scopedDeclarations)}</b><span>declarations · ${fmt(state.moduleCount)} modules</span></div>
      <div class="kpi"><b>${fmt(state.goalDeclarationCount)}</b><span>goal cone · ${pct(state.goalDeclarationCount, state.declarationCount)}</span></div>
      <div class="kpi"><b>${fmt(scopedEdges)}</b><span>resolved refs · ${fmt(shownRibbons)} ribbons</span></div>
      <div class="kpi"><b>${state.maxHeight}</b><span>max depth · median ${state.medianHeight}</span></div>
      <div class="kpi"><b>${fmt(state.rootCount)}</b><span>full-DAG roots · ${pct(state.rootCount, state.declarationCount)}</span></div>
      <div class="kpi"><b>${fmt(scopedSorry)}</b><span>explicit sorry tokens</span></div>
    </div>`;
  }

  function renderDelta(frame) {
    const change = frame.change;
    const items = [
      ["modules", `+${fmt(change.moduleAdded)} / −${fmt(change.moduleRemoved)}`, change.moduleAdded - change.moduleRemoved],
      ["declarations", `+${fmt(change.declarationAdded)} / −${fmt(change.declarationRemoved)}`, change.declarationAdded - change.declarationRemoved],
      ["edges", signed(change.edgeDelta), change.edgeDelta],
      ["top roots", signed(change.rootDelta), change.rootDelta],
      ["max depth", signed(change.heightDelta), change.heightDelta],
      ["sorry", signed(change.sorryDelta), -change.sorryDelta],
      ["goal cone", signed(change.goalDelta), change.goalDelta],
      ["bucket commits", fmt(frame.activity.commitCount), frame.activity.commitCount],
    ];
    deltaEl.innerHTML = `<h2>Change since prior code state</h2><div class="delta-strip">${items.map(([label, value, sign]) =>
      `<div class="delta-item">${esc(label)}<b class="${signClass(sign)}">${value}</b></div>`).join("")}</div>`;
  }

  function renderActivity(frame, state) {
    const activity = frame.activity;
    const chips = activity.tags.length ? activity.tags.map(tag => `<span class="chip">${esc(tag)}</span>`).join("") : `<span class="chip">QUIET BUCKET</span>`;
    const commits = activity.recentCommits.slice(-3).reverse();
    const files = activity.topFiles.slice(0, 3);
    const skew = state.timestamp - state.authorTimestamp;
    const bucketLabel = meta.bucketHours === 1 ? "Hourly" : `${meta.bucketHours}-hour`;
    activityEl.innerHTML = `<h2>${bucketLabel} expedition activity</h2>
      <div class="activity-summary"><span><b>${fmt(activity.commitCount)}</b> commits</span><span><b>${fmt(activity.leanCommitCount)}</b> Lean</span><span><b>${fmt(activity.authorCount)}</b> authors</span><span><b>+${fmt(activity.insertions)} / −${fmt(activity.deletions)}</b> lines</span><span><b>${fmt(activity.filesChanged)}</b> Lean files</span></div>
      <div class="chips">${chips}</div>
      <div class="subhead">Recent commits</div>
      <ul class="mini-list">${commits.length ? commits.map(([hash, subject]) => `<li title="${esc(subject)}"><code>${esc(hash)}</code> ${esc(subject)}</li>`).join("") : "<li>no commits in this bucket</li>"}</ul>
      <div class="subhead">Highest Lean churn</div>
      <ul class="mini-list">${files.length ? files.map(([path, added, deleted]) => `<li title="${esc(path)}"><span class="file-churn">+${fmt(added)} −${fmt(deleted)}</span>${esc(path)}</li>`).join("") : "<li>no Lean file changes</li>"}</ul>
      <div class="legend-note">Integration clock · ${state.parentCount > 1 ? `${state.parentCount}-parent merge` : "linear commit"}${skew ? ` · committed ${duration(skew)} after authorship` : " · author/commit timestamps agree"}</div>`;
  }

  function renderSemantics(state) {
    const counts = model.goalOnly ? state.goalRoleCounts : state.roleCounts;
    const max = Math.max(1, ...counts);
    semanticsEl.innerHTML = `<h2>Heuristic proof-role population</h2>${roleOrder.map(role => {
      const width = 100 * counts[role] / max;
      const goalWidth = model.goalOnly ? 0 : 100 * state.goalRoleCounts[role] / max;
      return `<div class="role-row"><span class="role-label" title="${esc(roles[role])}">${esc(roleShort[role])}</span><span class="role-track"><i class="role-fill" style="width:${width}%;background:${roleColors[role]}"></i>${goalWidth ? `<i class="role-goal" style="width:${goalWidth}%"></i>` : ""}</span><span class="role-value">${fmt(counts[role])}</span></div>`;
    }).join("")}<div class="legend-note">Cyan inset = portion feeding the current headline.</div>`;
  }

  function renderHubs(state) {
    const hubs = state.topHubs.slice(0, 6);
    hubsEl.innerHTML = `<h2>Dependency hubs · direct consumers</h2><div class="subhead">Target</div><div title="${esc(state.goalTarget || "No headline yet")}">${esc(basename(state.goalTarget || "No headline yet"))}</div><ul class="mini-list hub-list">${hubs.map(([name, moduleName, consumers, inGoal]) =>
      `<li title="${esc(name)} · ${esc(moduleName)}" class="${inGoal ? "in-goal" : ""}"><span class="hub-count">${fmt(consumers)}</span>${inGoal ? "◆ " : ""}${esc(basename(name))}</li>`).join("")}</ul><div class="legend-note">◆ lies in the current goal cone; counts are full-DAG consumers.</div>`;
  }

  function renderLegend() {
    const cfg = model.cfg;
    const audit = meta.timingAudit;
    legendEl.innerHTML = `<strong>Node fill · declaration kind</strong><br>${kinds.map((name, index) => `<span><i style="background:${kindColors[index]};color:${kindColors[index]}"></i>${esc(name)}</span>`).join("")}
      <br><strong>Horizontal lane · ${cfg.byRole ? "proof role" : "code area"}</strong><br>${cfg.laneOrder.map(index => `<span><i style="background:${cfg.laneColors[index]};color:${cfg.laneColors[index]}"></i>${esc(cfg.laneShort[index])}</span>`).join("")}
      <br><span class="legend-note">Lane widths reflect peak historical population. ${model.strands ? `Position within a lane = ${cfg.byRole ? "code area" : "proof role"}; glow follows that cross-facet.` : "Each layer band is collapsed to one population per lane."} Cyan arcs/ribbon cores mark the goal cone.<br>Clock audit: ${fmt(audit.firstParentCommitCount)} first-parent commits, ${fmt(audit.mergeCommitCount)} merges, ${fmt(audit.authorCommitterMismatchCount)} author/commit differences (max ${duration(audit.maxAbsAuthorCommitterDeltaSeconds)}), ${fmt(audit.committerTimestampBackstepCount)} backsteps.</span>`;
  }

  function setFrame(index, keepPlaying = true) {
    currentFrame = Math.max(0, Math.min(history.timeline.length - 1, index));
    timelineEl.value = currentFrame;
    const frame = history.timeline[currentFrame];
    const state = history.states[frame.state];
    model = aggregateState(frame.state);
    selected = null;
    hovered = null;
    layout();
    const when = new Date(frame.time * 1000).toLocaleString(undefined, { timeZone: "UTC", dateStyle: "medium", timeStyle: "short" });
    bucketTimeEl.textContent = `${when} UTC · bucket ${currentFrame + 1}/${history.timeline.length}`;
    commitMetaEl.textContent = `${state.commit.slice(0, 10)} · integrated ${new Date(state.timestamp * 1000).toISOString().slice(0, 16).replace("T", " ")} UTC`;
    commitMetaEl.title = `Author: ${state.authorIso} · Commit/integration: ${state.iso}`;
    commitSubjectEl.textContent = state.subject;
    commitSubjectEl.title = state.subject;
    const shownRibbons = model.edges.filter(edge => edge.weight >= Number(thresholdEl.value)).length;
    renderKpis(state, shownRibbons);
    renderDelta(frame);
    renderActivity(frame, state);
    renderSemantics(state);
    renderHubs(state);
    renderDetails();
    renderLegend();
    topAxisEl.textContent = model.goalOnly ? "HIGH LEVEL · CURRENT HEADLINE CONE" : "HIGH LEVEL · TERMINAL RESULTS / UNUSED ROOTS";
    scopeBadgeEl.textContent = state.goalTarget ? `goal: ${state.goalTarget}` : "goal: no headline yet";
    drawSpark();
    draw();
    if (!keepPlaying) stop();
  }

  function resizeSpark() {
    const rect = spark.getBoundingClientRect();
    const ratio = window.devicePixelRatio || 1;
    spark.width = Math.max(1, Math.round(rect.width * ratio));
    spark.height = Math.max(1, Math.round(rect.height * ratio));
    drawSpark();
  }

  function drawSpark() {
    const rect = spark.getBoundingClientRect();
    const w = rect.width;
    const h = rect.height;
    const ratio = window.devicePixelRatio || 1;
    sparkCtx.setTransform(ratio, 0, 0, ratio, 0, 0);
    sparkCtx.clearRect(0, 0, w, h);
    const frames = history.timeline;
    const declarations = frames.map(frame => history.states[frame.state].declarationCount);
    const goals = frames.map(frame => history.states[frame.state].goalDeclarationCount);
    const sorry = frames.map(frame => history.states[frame.state].sorryCount);
    const commits = frames.map(frame => frame.activity.commitCount);
    const maxDeclarations = Math.max(1, ...declarations);
    const maxSorry = Math.max(1, ...sorry);
    const maxCommits = Math.max(1, ...commits);
    const x = index => 6 + index / (frames.length - 1 || 1) * (w - 12);
    const yDecl = value => h - 14 - value / maxDeclarations * (h - 24);
    const ySorry = value => h - 14 - value / maxSorry * (h - 24);

    sparkCtx.fillStyle = "rgba(100,116,139,.30)";
    commits.forEach((value, index) => {
      const barWidth = Math.max(1, (w - 12) / frames.length * .8);
      const barHeight = value / maxCommits * 10;
      sparkCtx.fillRect(x(index) - barWidth / 2, h - 2 - barHeight, barWidth, barHeight);
    });
    frames.forEach((frame, index) => {
      if (!frame.activity.tags.length) return;
      sparkCtx.fillStyle = "rgba(251,191,36,.65)";
      sparkCtx.fillRect(x(index), 3, 1, 5);
    });

    function line(values, y, color, lineWidth) {
      sparkCtx.beginPath();
      values.forEach((value, index) => index ? sparkCtx.lineTo(x(index), y(value)) : sparkCtx.moveTo(x(index), y(value)));
      sparkCtx.strokeStyle = color;
      sparkCtx.lineWidth = lineWidth;
      sparkCtx.stroke();
    }
    line(declarations, yDecl, "#4ade80", 1.5);
    line(goals, yDecl, "#22d3ee", 1.25);
    line(sorry, ySorry, "rgba(251,113,133,.88)", 1);
    const currentX = x(currentFrame);
    sparkCtx.strokeStyle = "#f8fafc";
    sparkCtx.lineWidth = 1;
    sparkCtx.beginPath();
    sparkCtx.moveTo(currentX, 2);
    sparkCtx.lineTo(currentX, h - 2);
    sparkCtx.stroke();
  }

  function stop() {
    playing = false;
    playEl.textContent = "▶";
    if (timer) { clearTimeout(timer); timer = null; }
  }

  function playStep() {
    if (!playing) return;
    if (currentFrame >= history.timeline.length - 1) { stop(); return; }
    setFrame(currentFrame + 1);
    timer = setTimeout(playStep, Number(speedEl.value));
  }

  function togglePlay() {
    if (playing) { stop(); return; }
    if (currentFrame >= history.timeline.length - 1) setFrame(0);
    playing = true;
    playEl.textContent = "❚❚";
    timer = setTimeout(playStep, Number(speedEl.value));
  }

  timelineEl.max = history.timeline.length - 1;
  timelineEl.addEventListener("input", () => setFrame(Number(timelineEl.value), false));
  playEl.addEventListener("click", togglePlay);
  backEl.addEventListener("click", () => setFrame(currentFrame - 1, false));
  forwardEl.addEventListener("click", () => setFrame(currentFrame + 1, false));
  for (const element of [scopeEl, lanesEl, groupingEl, blurEl]) {
    element.addEventListener("change", () => { calibrate(); setFrame(currentFrame); });
  }
  thresholdEl.addEventListener("change", () => setFrame(currentFrame));

  canvas.addEventListener("mousemove", event => {
    const rect = canvas.getBoundingClientRect();
    const x = event.clientX - rect.left;
    const y = event.clientY - rect.top;
    const id = groupAt(x, y);
    hovered = id;
    draw();
    if (id == null) { tooltip.style.display = "none"; return; }
    const group = model.groups[id];
    const start = group.band * model.blur;
    const end = start + model.blur - 1;
    tooltip.style.display = "block";
    tooltip.style.left = `${Math.max(5, Math.min(width - 370, x + 12))}px`;
    tooltip.style.top = `${Math.max(5, Math.min(height - 110, y + 12))}px`;
    tooltip.innerHTML = `<strong>${esc(groupTitle(group))}</strong><br>layers ${start === end ? start : `${start}–${end}`} · ${fmt(group.count)} declarations${model.goalOnly ? "" : `<br>${fmt(group.goalCount)} in goal cone`}<br>${composition(group)}`;
  });
  canvas.addEventListener("mouseleave", () => { hovered = null; tooltip.style.display = "none"; draw(); });
  canvas.addEventListener("click", event => {
    const rect = canvas.getBoundingClientRect();
    selected = groupAt(event.clientX - rect.left, event.clientY - rect.top);
    renderDetails();
    draw();
  });
  spark.addEventListener("click", event => {
    const rect = spark.getBoundingClientRect();
    const fraction = Math.max(0, Math.min(1, (event.clientX - rect.left - 6) / Math.max(1, rect.width - 12)));
    setFrame(Math.round(fraction * (history.timeline.length - 1)), false);
  });
  window.addEventListener("keydown", event => {
    if (event.target.tagName === "SELECT" || event.target.tagName === "INPUT") return;
    if (event.code === "Space") { event.preventDefault(); togglePlay(); }
    else if (event.code === "ArrowLeft") setFrame(currentFrame - 1, false);
    else if (event.code === "ArrowRight") setFrame(currentFrame + 1, false);
  });
  window.addEventListener("resize", resize);

  calibrate();
  setFrame(currentFrame);
  resize();
})();
