"""Expedition-map (plan-layer) mining.

Reads `expeditions/<slug>/map/claims.yaml` snapshots along the first-parent
lineage (same clock as the code history), diffs them into per-node lifecycles
(births, status transitions, owner changes, deaths), detects re-root epochs
(mass id replacement), joins tip nodes to the declaration territory via their
`lean:` anchors, and reads battery attachments. Pure git reads; the authored
YAML is the single source — nothing here writes.
"""
from __future__ import annotations

import bisect
import datetime as dt
from collections import Counter

import yaml

NODE_FIELDS = ("kind", "title", "status", "owner", "tier", "lean", "notes", "kill")


def find_map_path(repo, tip):
    """Newest expeditions/*/map/claims.yaml in the tip tree (date-prefixed slugs)."""
    out = repo.run("ls-tree", "-r", "--name-only", tip, "--", "expeditions")
    candidates = [p for p in out.splitlines() if p.endswith("/map/claims.yaml")]
    return max(candidates) if candidates else None


def _parse_snapshot(text):
    try:
        data = yaml.safe_load(text)
    except yaml.YAMLError:
        return None
    if not isinstance(data, dict):
        return None
    nodes = {}
    for n in data.get("nodes") or []:
        if not isinstance(n, dict) or not n.get("id"):
            continue
        rec = {f: n.get(f) for f in NODE_FIELDS}
        rec["landmark"] = bool(n.get("landmark"))
        rec["prop"] = (n.get("prop") or "").strip()[:1200]
        rec["evidence"] = [str(e) for e in (n.get("evidence") or [])][:8]
        rec["edges"] = [
            {"type": e.get("type"), "to": e.get("to")}
            for e in (n.get("edges") or []) if isinstance(e, dict) and e.get("to")
        ]
        nodes[str(n["id"])] = rec
    meta = data.get("meta") or {}
    return {"meta": meta, "nodes": nodes}


def _battery_header(text):
    kills, guards, config, provenance = [], [], "", ""
    for line in text.splitlines():
        s = line.strip()
        if s and not s.startswith("#"):
            break
        body = s.lstrip("#").strip()
        key, _, val = body.partition(":")
        key, val = key.strip().lower(), val.strip()
        if key in ("kills", "guards"):
            (kills if key == "kills" else guards).extend(
                x.strip() for x in val.split(",") if x.strip())
        elif key == "config":
            config = val
        elif key == "provenance":
            provenance = val
    return kills, guards, config, provenance


def mine(repo, base, tip, map_path, tip_graph):
    """Full plan-layer history + tip territory join. Returns None if no map."""
    if not map_path:
        return None
    shas = repo.run("log", "--first-parent", "--reverse",
                    "--format=%H\x1f%ct\x1f%s", f"{base}..{tip}",
                    "--", map_path).splitlines()
    if not shas:
        return None

    nodes = {}        # id → lifecycle record
    events = []
    epochs = []
    prev = {}
    for row in shas:
        sha, ts, subject = row.split("\x1f", 2)
        ts = int(ts)
        try:
            text = repo.run("show", f"{sha}:{map_path}")
        except Exception:
            continue
        snap = _parse_snapshot(text)
        if snap is None:
            continue
        cur = snap["nodes"]
        births = [i for i in cur if i not in prev]
        deaths = [i for i in prev if i not in cur]
        transitions, owner_changes = [], []
        for nid, rec in cur.items():
            life = nodes.get(nid)
            if life is None or life["death"] is not None:
                # birth (or rebirth after an epoch archived it)
                life = nodes.setdefault(nid, {
                    "id": nid, "birth": ts, "death": None,
                    "segments": [], "ownerChanges": [], "titleChanges": 0,
                })
                if life["death"] is not None:      # rebirth: reopen
                    life["death"] = None
                life["segments"].append([ts, rec["status"]])
            else:
                p = prev.get(nid, {})
                if rec["status"] != p.get("status"):
                    transitions.append([nid, p.get("status"), rec["status"]])
                    life["segments"].append([ts, rec["status"]])
                if (rec["owner"] or "") != (p.get("owner") or ""):
                    owner_changes.append(nid)
                    life["ownerChanges"].append(ts)
                if rec["title"] != p.get("title"):
                    life["titleChanges"] += 1
            life["last"] = rec                     # latest authored fields
        for nid in deaths:
            nodes[nid]["death"] = ts
        if prev and len(deaths) >= max(3, len(prev) // 2):
            epochs.append({"ts": ts, "sha": sha[:10], "died": len(deaths),
                           "born": len(births), "label": "re-root"})
        events.append({
            "ts": ts, "sha": sha[:10], "subject": subject[:120],
            "transitions": transitions, "births": births, "deaths": deaths,
            "ownerChanges": owner_changes,
            "counts": dict(Counter(r["status"] for r in cur.values())),
            "total": len(cur),
        })
        prev = cur

    live_ids = set(prev)
    meta_snapshot = snap["meta"] if snap else {}

    # -- territory join (tip nodes with a lean anchor vs the source scan) ----
    name_index = tip_graph.name_to_index
    by_suffix = {}
    for name in name_index:
        by_suffix.setdefault(name.rsplit(".", 1)[-1], []).append(name)
    for nid in live_ids:
        rec = nodes[nid]["last"]
        anchor = rec.get("lean")
        nodes[nid]["territory"] = None
        if not anchor:
            continue
        di = name_index.get(anchor)
        if di is None:
            tail = anchor.rsplit(".", 1)[-1]
            matches = [c for c in by_suffix.get(tail, ())
                       if c == anchor or c.endswith("." + anchor) or anchor.endswith("." + c)]
            di = name_index[matches[0]] if len(matches) == 1 else None
        if di is None:
            nodes[nid]["territory"] = {"decl": anchor, "exists": False}
            continue
        cone_sorries, seen, queue = 0, {di}, [di]
        while queue:
            v = queue.pop()
            if tip_graph.decls[v].sorry_count:
                cone_sorries += 1
            for d in tip_graph.dependencies[v]:
                if d not in seen:
                    seen.add(d)
                    queue.append(d)
        nodes[nid]["territory"] = {
            "decl": tip_graph.decls[di].name, "exists": True, "declId": di,
            "sorry": tip_graph.decls[di].sorry_count,
            "coneSorries": cone_sorries, "coneSize": len(seen),
        }

    # -- battery attachments at tip ------------------------------------------
    battery = []
    battery_dir = map_path.rsplit("/", 1)[0] + "/battery"
    out = repo.run("ls-tree", "-r", "--name-only", tip, "--", battery_dir)
    for path in out.splitlines():
        name = path.rsplit("/", 1)[-1]
        if not name.endswith(".py") or name.startswith("_"):
            continue
        kills, guards, config, provenance = _battery_header(
            repo.run("show", f"{tip}:{path}"))
        battery.append({"name": name, "kills": kills, "guards": guards,
                        "config": config, "provenance": provenance})
    attach = {}
    for b in battery:
        for nid in b["kills"]:
            attach.setdefault(nid, {"kills": [], "guards": []})["kills"].append(b["name"])
        for nid in b["guards"]:
            attach.setdefault(nid, {"kills": [], "guards": []})["guards"].append(b["name"])

    node_list = []
    for nid, life in nodes.items():
        rec = life["last"]
        node_list.append({
            "id": nid, "live": nid in live_ids,
            "birth": life["birth"], "death": life["death"],
            "segments": life["segments"], "ownerChanges": life["ownerChanges"],
            "titleChanges": life["titleChanges"],
            "territory": life.get("territory"),
            "battery": attach.get(nid),
            **{f: rec.get(f) for f in NODE_FIELDS},
            "landmark": rec.get("landmark", False),
            "prop": rec.get("prop", ""), "evidence": rec.get("evidence", []),
            "edges": rec.get("edges", []),
        })
    node_list.sort(key=lambda n: (n["birth"], n["id"]))

    return {
        "meta": {
            "generatedAt": dt.datetime.now(dt.timezone.utc).isoformat(),
            "mapPath": map_path,
            "expedition": meta_snapshot.get("expedition"),
            "roots": meta_snapshot.get("roots") or [],
            "updated": str(meta_snapshot.get("updated") or ""),
            "commitCount": len(events),
            "liveCount": len(live_ids),
            "archivedCount": len(node_list) - len(live_ids),
            "landmarkCap": 9,
        },
        "nodes": node_list,
        "events": events,
        "epochs": epochs,
        "battery": battery,
    }


class PlanClock:
    """Per-state plan summaries for the history playback: counts at a state's
    timestamp + transitions/births/deaths that happened since the prior state."""

    def __init__(self, plan):
        self.events = plan["events"] if plan else []
        self.ts = [e["ts"] for e in self.events]

    def summary_between(self, prev_ts, ts):
        if not self.events:
            return None
        hi = bisect.bisect_right(self.ts, ts)
        if hi == 0:
            return None                      # before the map existed
        latest = self.events[hi - 1]
        lo = bisect.bisect_right(self.ts, prev_ts) if prev_ts is not None else 0
        transitions, births, deaths = [], 0, 0
        for e in self.events[lo:hi]:
            transitions.extend(e["transitions"])
            births += len(e["births"])
            deaths += len(e["deaths"])
        return {"n": latest["total"], "c": latest["counts"],
                "t": transitions[:12], "b": births, "d": deaths}
