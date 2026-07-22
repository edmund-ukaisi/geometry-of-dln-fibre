"""Tip-state module and declaration graphs with a precomputed layered layout.

Both graphs share the height convention of graph.py (0 = top consumers) and a
simple Sugiyama-style layout: nodes on rows by height, ordered within a row by
a few barycenter sweeps, x centred around 0.
"""
from __future__ import annotations

import datetime as dt
from collections import defaultdict

from .graph import StateGraph
from .leanparse import KINDS, module_name_from_path


def _components(n, neighbors):
    comp = [-1] * n
    sizes = []
    for seed in range(n):
        if comp[seed] != -1:
            continue
        cid = len(sizes)
        queue, comp[seed] = [seed], cid
        head = 0
        while head < len(queue):
            v = queue[head]
            head += 1
            for w in neighbors[v]:
                if comp[w] == -1:
                    comp[w] = cid
                    queue.append(w)
        sizes.append(len(queue))
    return comp, sizes


def _layout(heights, deps, consumers, comp, sizes, x_gap, y_gap, sweeps=4):
    """Row = height (0 on top). Order within a row: big components first, then
    barycenter sweeps over both edge directions. Returns (xs, ys, world_w, world_h)."""
    n = len(heights)
    max_h = max(heights, default=0)
    rows = defaultdict(list)
    order_key = [(-sizes[comp[i]], comp[i], i) for i in range(n)]
    for i in sorted(range(n), key=lambda i: order_key[i]):
        rows[heights[i]].append(i)
    slot = [0] * n
    for row in rows.values():
        for s, i in enumerate(row):
            slot[i] = s
    for _ in range(sweeps):
        for row_ids in (range(max_h + 1), range(max_h, -1, -1)):
            for h in row_ids:
                row = rows[h]
                if len(row) < 2:
                    continue
                def bary(i):
                    ns = [slot[w] for w in deps[i]] + [slot[w] for w in consumers[i]]
                    return (sum(ns) / len(ns)) if ns else slot[i]
                row.sort(key=lambda i: (comp[i] if sizes[comp[i]] > 2 else -1, bary(i)))
                for s, i in enumerate(row):
                    slot[i] = s
    xs, ys = [0.0] * n, [0] * n
    widest = max((len(r) for r in rows.values()), default=1)
    for h, row in rows.items():
        offset = (len(row) - 1) / 2
        for i in row:
            xs[i] = round((slot[i] - offset) * x_gap, 1)
            ys[i] = h * y_gap
    return xs, ys, widest * x_gap, max_h * y_gap + y_gap


def _cone(seeds, deps, n):
    mark = bytearray(n)
    queue = [s for s in seeds]
    for s in seeds:
        mark[s] = 1
    head = 0
    while head < len(queue):
        v = queue[head]
        head += 1
        for d in deps[v]:
            if not mark[d]:
                mark[d] = 1
                queue.append(d)
    return mark


def _pastel(hex_color: str, mix: float = 0.72) -> str:
    v = int(hex_color.lstrip("#"), 16)
    channel = lambda c: round(c + (255 - c) * mix)
    r, g, b = v >> 16, (v >> 8) & 255, v & 255
    return f"#{channel(r):02x}{channel(g):02x}{channel(b):02x}"


def _base_meta(repo, branch, head, profile):
    return {
        "generatedAt": dt.datetime.now(dt.timezone.utc).isoformat(),
        "sourceRoot": repo.root,
        "sourceHead": head[:10],
        "branch": branch,
        "canonicalRoot": repo.root,
        "canonicalHead": head[:10],
        "activeOnlyModules": [],
        "noBuild": True,
        "areas": profile.areas,
        "areaColors": profile.area_colors,
        "goalLabel": profile.goal_label,
        "categoryColors": {
            profile.area_short[i].lower().replace(" ", "-"): _pastel(color)
            for i, color in enumerate(profile.area_colors)
        },
    }


def build_module_graph(repo, branch, head, profile, blobs, tip):
    files = repo.lean_tree(head, profile.lean_root)
    modules, parsed_of = [], {}
    for path, blob_sha in files:
        module = module_name_from_path(path, profile.lean_root)
        modules.append((module, path))
        parsed_of[module] = blobs.parsed(blob_sha)
    index = {m: i for i, (m, _p) in enumerate(modules)}
    n = len(modules)
    deps = [[] for _ in range(n)]        # module → imported project modules
    consumers = [[] for _ in range(n)]
    external = [0] * n
    edges = set()
    for i, (module, _path) in enumerate(modules):
        for imp in parsed_of[module].imports:
            j = index.get(imp)
            if j is None:
                external[i] += 1
            elif j != i:
                edges.add((j, i))        # dep → consumer
    for j, i in edges:
        deps[i].append(j)
        consumers[j].append(i)

    heights = _module_heights(n, consumers)
    both = [deps[i] + consumers[i] for i in range(n)]
    comp, sizes = _components(n, both)
    xs, ys, world_w, world_h = _layout(heights, deps, consumers, comp, sizes,
                                       x_gap=150, y_gap=66)

    goal_module = None
    goal_target = None
    tip_graph, module_of_decl = tip
    if tip_graph.goal_index is not None:
        goal_target = tip_graph.goal_target
        goal_module = module_of_decl[tip_graph.goal_index]
    sorry_of = {m: parsed_of[m].sorry_count for m, _p in modules}
    goal_cone = _cone([index[goal_module]], deps, n) if goal_module in index else bytearray(n)
    frontier_seeds = [i for i, (m, _p) in enumerate(modules) if sorry_of[m]]
    frontier_cone = _cone(frontier_seeds, deps, n)

    nodes = []
    for i, (module, path) in enumerate(modules):
        parsed = parsed_of[module]
        label = "/".join(module.split(".")[1:]) or module
        nodes.append({
            "name": module, "label": label,
            "path": f"{repo.root}/{path}", "relativePath": path,
            "category": _category(module, parsed, profile),
            "sorryCount": parsed.sorry_count,
            "lineCount": parsed.line_count,
            "externalImportCount": external[i],
            "compiled": None, "active": False, "synthetic": False,
            "x": xs[i], "y": ys[i], "id": i,
            "height": heights[i], "component": comp[i],
            "componentSize": sizes[comp[i]],
            "consumerCount": len(consumers[i]),
            "dependencyCount": len(deps[i]),
            "root": not consumers[i],
            "goalCone": bool(goal_cone[i]),
            "frontierCone": bool(frontier_cone[i]),
            "goal": module == goal_module,
            "frontier": bool(sorry_of[module]) ,
        })
    meta = _base_meta(repo, branch, head, profile)
    meta.update({
        "componentCount": len(sizes), "rootCount": sum(1 for nd in nodes if nd["root"]),
        "maxHeight": max(heights, default=0),
        "worldWidth": world_w, "worldHeight": world_h,
        "nodeCount": n, "edgeCount": len(edges),
        "compiledCount": 0, "sourceOnlyCount": n,
        "goalTarget": goal_target,
    })
    return {"kind": "module", "meta": meta, "nodes": nodes,
            "edges": sorted([list(e) for e in edges])}


def _module_heights(n, consumers):
    # longest path from consumer-free roots; module import graph is acyclic
    pending = [0] * n
    deps_of = [[] for _ in range(n)]
    for dep in range(n):
        for cons in consumers[dep]:
            deps_of[cons].append(dep)
    out_deg = [len(consumers[i]) for i in range(n)]
    height = [0] * n
    queue = [i for i in range(n) if out_deg[i] == 0]
    head = 0
    while head < len(queue):
        c = queue[head]
        head += 1
        for d in deps_of[c]:
            if height[d] < height[c] + 1:
                height[d] = height[c] + 1
            out_deg[d] -= 1
            if out_deg[d] == 0:
                queue.append(d)
    return height


def _category(module, parsed, profile):
    if not parsed.decls and parsed.imports:
        return "aggregator"
    area = profile.area_index(module)
    return profile.area_short[area].lower().replace(" ", "-")


def tip_state(repo, head, profile, blobs):
    files = repo.lean_tree(head, profile.lean_root)
    decls, module_of = [], []
    for path, blob_sha in files:
        parsed = blobs.parsed(blob_sha)
        module = module_name_from_path(path, profile.lean_root)
        for decl in parsed.decls:
            decls.append(decl)
            module_of.append(module)
    return StateGraph(decls, module_of, profile), module_of


def build_declaration_graph(repo, branch, head, profile, blobs, tip):
    graph, module_of = tip
    n = graph.n
    deps, consumers = graph.dependencies, graph.consumers
    both = [deps[i] + consumers[i] for i in range(n)]
    comp, sizes = _components(n, both)
    xs, ys, world_w, world_h = _layout(graph.height, deps, consumers, comp, sizes,
                                       x_gap=16, y_gap=52, sweeps=3)
    frontier_seeds = [i for i in range(n) if graph.decls[i].sorry_count]
    frontier_cone = _cone(frontier_seeds, deps, n)

    module_paths = {module_name_from_path(p, profile.lean_root): p
                    for p, _b in repo.lean_tree(head, profile.lean_root)}
    nodes = []
    for i in range(n):
        decl = graph.decls[i]
        nodes.append({
            "name": decl.name, "label": decl.name.rsplit(".", 1)[-1],
            "module": module_of[i],
            "kind": KINDS[graph.kind[i]],
            "area": graph.area[i],
            "role": profile.role_short[graph.role[i]],
            "line": decl.line,
            "exact": False,
            "hasSorry": decl.sorry_count > 0,
            "synthetic": False,
            "source": f"{repo.root}/{module_paths.get(module_of[i], '')}",
            "active": False,
            "x": xs[i], "y": ys[i], "id": i,
            "height": graph.height[i], "component": comp[i],
            "componentSize": sizes[comp[i]],
            "consumerCount": len(consumers[i]),
            "dependencyCount": len(deps[i]),
            "root": not consumers[i],
            "goalCone": bool(graph.in_goal_cone[i]),
            "frontierCone": bool(frontier_cone[i]),
            "goal": i == graph.goal_index,
            "frontier": decl.sorry_count > 0,
        })
    edges = sorted(
        [dep, cons] for dep in range(n) for cons in consumers[dep]
    )
    meta = _base_meta(repo, branch, head, profile)
    meta.update({
        "componentCount": len(sizes),
        "rootCount": graph.root_count,
        "maxHeight": graph.max_height,
        "worldWidth": world_w, "worldHeight": world_h,
        "nodeCount": n, "edgeCount": len(edges),
        "exactCount": 0, "sourceDerivedCount": n,
        "goalTarget": graph.goal_target,
    })
    return {"kind": "declaration", "meta": meta, "nodes": nodes, "edges": edges}
