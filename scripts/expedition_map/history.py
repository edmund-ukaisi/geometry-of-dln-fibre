"""Git-derived metadata history + the activity clock (spec § survey).

The plan-layer's own git history is a second territory to keep the map honest
against wall-clock drift. Two disciplines from the spec govern it:

* **First-parent only.** We walk the expedition branch with ``--first-parent``,
  so a teammate merge collapses to a single mainline commit: its side-branch
  commits create neither phantom status transitions nor extra activity buckets.
* **The activity clock.** Ages/staleness are measured in *active commit-hours*
  (distinct hour-buckets that carry ≥1 first-parent commit of the branch), not
  wall time — a hole is not stale because the VM slept.

Metadata is derived by re-parsing the ``claims.yaml`` snapshot at each
first-parent commit that touched it (``git show <sha>:<path>``) and diffing
consecutive snapshots. This is more robust than reconstructing per-node status
from ``-p`` unified diffs, and gives exactly the first-parent semantics the spec
asks for. Snapshots are cached by sha (``survey/history-cache.json``), so a
refresh only re-reads commits it has not seen.
"""

from __future__ import annotations

import bisect
import datetime
import subprocess
from pathlib import Path

import yaml

from . import model

HOUR = 3600

# Alarm thresholds (defaults; all activity-time except staleness). Surfaced as
# alarms, never columns.
DEFAULT_ALARMS = {
    "oldest_open_hole_activity_hours": 72,     # 3 activity-days
    "promotion_lag_activity_days": 2,          # adjudicated -> skeleton-linked
    "owner_churn_count": 2,                     # > this many changes ...
    "owner_churn_window_activity_hours": 24,    # ... within this activity window
}


# ---------------------------------------------------------------------------
# git helpers
# ---------------------------------------------------------------------------

def _git(repo, *args, timeout=60):
    r = subprocess.run(["git", "-C", str(repo), *args],
                       capture_output=True, text=True, timeout=timeout)
    return r.returncode, r.stdout, r.stderr


def repo_root(path):
    code, out, _ = _git(path, "rev-parse", "--show-toplevel")
    return out.strip() if code == 0 else None


def _iso_to_epoch(iso):
    return int(datetime.datetime.fromisoformat(iso).timestamp())


def first_parent_commits(repo, branch, relpath=None):
    """(sha, iso, author) oldest-first along ``--first-parent`` of ``branch``.

    With ``relpath`` restricts to commits that changed that path (``--follow``);
    without it, every first-parent commit of the branch (for the clock).
    """
    args = ["log", "--first-parent", "--format=%H\x1f%cI\x1f%an", branch]
    if relpath:
        args += ["--follow", "--", relpath]
    code, out, _ = _git(repo, *args)
    if code != 0:
        return []
    rows = []
    for line in out.splitlines():
        if line.count("\x1f") == 2:
            sha, iso, author = line.split("\x1f")
            rows.append((sha, iso, author))
    rows.reverse()  # oldest-first
    return rows


def _snapshot(repo, sha, relpath):
    """Parse the ``claims.yaml`` at ``sha`` into {id: {status, owner}} (or None)."""
    code, out, _ = _git(repo, "show", f"{sha}:{relpath}")
    if code != 0:
        return None
    try:
        data = yaml.safe_load(out)
    except yaml.YAMLError:
        return None
    if not isinstance(data, dict):
        return None
    state = {}
    for n in data.get("nodes") or []:
        if isinstance(n, dict) and n.get("id"):
            state[n["id"]] = {
                "status": n.get("status"),
                "owner": (n.get("owner") or ""),
            }
    return state


# ---------------------------------------------------------------------------
# activity clock
# ---------------------------------------------------------------------------

def build_activity_clock(commit_isos):
    """Sorted distinct active hour-buckets (unix-hour ints) from commit dates."""
    buckets = sorted({_iso_to_epoch(iso) // HOUR for iso in commit_isos})
    return buckets


def activity_between(buckets, start_iso, end_iso):
    """Count active hour-buckets in (hour(start), hour(end)]."""
    if not buckets or not start_iso or not end_iso:
        return 0
    s = _iso_to_epoch(start_iso) // HOUR
    e = _iso_to_epoch(end_iso) // HOUR
    lo = bisect.bisect_right(buckets, s)
    hi = bisect.bisect_right(buckets, e)
    return max(0, hi - lo)


# ---------------------------------------------------------------------------
# per-node history
# ---------------------------------------------------------------------------

def _derive(m, file_commits, snapshots, clock, tip_iso):
    """Diff consecutive first-parent snapshots into per-node metadata."""
    nodes = {}
    prev = {}
    for sha, iso, author in file_commits:
        state = snapshots.get(sha)
        if state is None:
            continue
        for nid, cur in state.items():
            rec = nodes.setdefault(nid, {
                "first_seen": iso, "transitions": [], "owner_changes": [],
                "current_status": cur["status"], "current_status_since": iso,
                "current_owner": cur["owner"],
            })
            if nid not in prev:
                rec["first_seen"] = rec.get("first_seen", iso)
            else:
                if cur["status"] != prev[nid]["status"]:
                    rec["transitions"].append({
                        "from": prev[nid]["status"], "to": cur["status"],
                        "sha": sha, "ts": iso})
                    rec["current_status_since"] = iso
                if cur["owner"] != prev[nid]["owner"]:
                    rec["owner_changes"].append({
                        "from": prev[nid]["owner"], "to": cur["owner"],
                        "sha": sha, "ts": iso})
            rec["current_status"] = cur["status"]
            rec["current_owner"] = cur["owner"]
        prev = state

    now_wall = datetime.datetime.now(datetime.timezone.utc)
    out = {}
    for nid in m["by_id"]:                       # only current nodes surface
        rec = nodes.get(nid)
        if not rec:
            continue
        out[nid] = _finish(rec, clock, tip_iso, now_wall)
    return out


def _finish(rec, clock, tip_iso, now_wall):
    first_seen = rec["first_seen"]
    since = rec["current_status_since"]
    wall_age = (now_wall - datetime.datetime.fromisoformat(first_seen)).days
    tis_wall = (now_wall - datetime.datetime.fromisoformat(since)).days

    # promotion lag: adjudicated -> skeleton-linked (activity + wall)
    t_adj = _first_entry(rec, "adjudicated")
    t_sk = _first_entry(rec, "skeleton-linked")
    lag = None
    if t_adj:
        if t_sk and t_sk >= t_adj:
            lag = {"activity_hours": activity_between(clock, t_adj, t_sk),
                   "wall_days": (datetime.datetime.fromisoformat(t_sk)
                                 - datetime.datetime.fromisoformat(t_adj)).days,
                   "ongoing": False}
        elif not t_sk and rec["current_status"] == "adjudicated":
            lag = {"activity_hours": activity_between(clock, t_adj, tip_iso),
                   "wall_days": (datetime.datetime.fromisoformat(tip_iso)
                                 - datetime.datetime.fromisoformat(t_adj)).days,
                   "ongoing": True}

    return {
        "first_seen": first_seen,
        "current_status": rec["current_status"],
        "current_owner": rec["current_owner"],
        "current_status_since": since,
        "transitions": rec["transitions"],
        "owner_changes": rec["owner_changes"],
        "owner_churn": len(rec["owner_changes"]),
        "wall_age_days": wall_age,
        "activity_age_hours": activity_between(clock, first_seen, tip_iso),
        "time_in_status_wall_days": tis_wall,
        "time_in_status_activity_hours": activity_between(clock, since, tip_iso),
        "promotion_lag": lag,
    }


def _first_entry(rec, status):
    for t in rec["transitions"]:
        if t["to"] == status:
            return t["ts"]
    # or first_seen if it was introduced already in that status
    if rec["transitions"] and rec["transitions"][0]["from"] == status:
        return rec["first_seen"]
    if not rec["transitions"] and rec["current_status"] == status:
        return rec["first_seen"]
    return None


# ---------------------------------------------------------------------------
# alarms
# ---------------------------------------------------------------------------

def _owner_churn_window(changes, clock, window_hours):
    """Max owner-changes falling within any trailing ``window_hours`` activity."""
    ts = [c["ts"] for c in changes]
    best = 0
    for i in range(len(ts)):
        cnt = sum(1 for j in range(i, len(ts))
                  if activity_between(clock, ts[i], ts[j]) <= window_hours)
        best = max(best, cnt)
    return best


def compute_alarms(m, nodes_hist, clock, tip_iso, stale, thresholds):
    """Return a list of firing alarms (only firing ones)."""
    th = dict(DEFAULT_ALARMS)
    th.update(thresholds or {})
    alarms = []

    # 1. oldest open hole (activity age)
    open_ages = [(nid, h["activity_age_hours"]) for nid, h in nodes_hist.items()
                 if nid in m["by_id"] and model.is_open(m["by_id"][nid])]
    if open_ages:
        nid, age = max(open_ages, key=lambda x: x[1])
        if age > th["oldest_open_hole_activity_hours"]:
            alarms.append({
                "kind": "oldest-open-hole",
                "node": nid,
                "message": f"open {age}h activity (> {th['oldest_open_hole_activity_hours']}h): {nid}"})

    # 2. promotion lag
    for nid, h in nodes_hist.items():
        lag = h.get("promotion_lag")
        if not lag:
            continue
        days = lag["activity_hours"] / 24.0
        if days > th["promotion_lag_activity_days"]:
            tag = "stuck" if lag["ongoing"] else "lag"
            alarms.append({
                "kind": "promotion-lag",
                "node": nid,
                "message": f"promotion {tag} {days:.1f} activity-days "
                           f"(> {th['promotion_lag_activity_days']}): {nid}"})

    # 3. owner churn
    for nid, h in nodes_hist.items():
        n = _owner_churn_window(h["owner_changes"], clock,
                                th["owner_churn_window_activity_hours"])
        if n > th["owner_churn_count"]:
            alarms.append({
                "kind": "owner-churn",
                "node": nid,
                "message": f"{n} owner changes in {th['owner_churn_window_activity_hours']}h "
                           f"activity (> {th['owner_churn_count']}): {nid}"})

    # 4. staleness
    if stale:
        alarms.append({"kind": "staleness", "node": None,
                       "message": "survey stale vs git HEAD — run `expedition survey`"})
    return alarms


# ---------------------------------------------------------------------------
# top-level build (with per-sha snapshot cache)
# ---------------------------------------------------------------------------

def build_history(m, branch="HEAD", cache=None, thresholds=None, stale=False):
    """Compute the git-metadata history + activity clock + alarms for map ``m``.

    Returns a dict with ``_available`` false (and a reason) when there is no git
    repo / no history, so callers degrade gracefully.
    """
    map_dir = Path(m["map_dir"])
    root = repo_root(map_dir)
    if not root:
        return {"_available": False, "reason": "not a git repository",
                "nodes": {}, "alarms": [], "activity_clock": {}}
    relpath = str((map_dir / "claims.yaml").resolve().relative_to(Path(root).resolve()))

    file_commits = first_parent_commits(root, branch, relpath)
    all_commits = first_parent_commits(root, branch)   # whole branch, for clock
    if not file_commits or not all_commits:
        return {"_available": False, "reason": "no first-parent history for claims.yaml",
                "nodes": {}, "alarms": [], "activity_clock": {}}

    clock = build_activity_clock([iso for _, iso, _ in all_commits])
    tip_iso = all_commits[-1][1]

    cache = cache or {}
    snap_cache = dict(cache.get("snapshots", {}))
    snapshots = {}
    for sha, _iso, _a in file_commits:
        if sha in snap_cache:
            snapshots[sha] = snap_cache[sha]
        else:
            s = _snapshot(root, sha, relpath)
            if s is not None:
                snapshots[sha] = s
                snap_cache[sha] = s

    nodes_hist = _derive(m, file_commits, snapshots, clock, tip_iso)
    alarms = compute_alarms(m, nodes_hist, clock, tip_iso, stale, thresholds)

    return {
        "_available": True,
        "branch": branch,
        "last_sha": all_commits[-1][0],
        "tip_iso": tip_iso,
        "activity_clock": {
            "buckets": clock,
            "total_hours": len(clock),
            "tip_iso": tip_iso,
        },
        "nodes": nodes_hist,
        "alarms": alarms,
        "_cache": {"snapshots": snap_cache, "last_sha": all_commits[-1][0]},
    }
