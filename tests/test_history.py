"""Git-metadata history + activity clock, on a synthetic repo.

The merge-commit case proves first-parent discipline: a side branch's edits must
create neither phantom status transitions nor extra activity-clock buckets.
"""

import os
import subprocess

import pytest

from expedition_map import model, history, ops
from conftest import dump_claims


def _run(repo, *args, env=None):
    e = os.environ.copy()
    e.setdefault("GIT_CONFIG_GLOBAL", "/dev/null")
    if env:
        e.update(env)
    return subprocess.run(["git", "-C", str(repo), *args],
                          capture_output=True, text=True, env=e, check=True)


class Repo:
    def __init__(self, root):
        self.root = root
        self.map = root / "map"
        self.map.mkdir(parents=True)
        self._tick = 0
        _run(root, "init", "-q")
        _run(root, "checkout", "-q", "-b", "main")  # deterministic branch name
        _run(root, "config", "user.email", "t@t")
        _run(root, "config", "user.name", "t")
        _run(root, "config", "commit.gpgsign", "false")

    def commit(self, nodes, roots, date, msg):
        (self.map / "claims.yaml").write_text(dump_claims(nodes, roots))
        # A monotonic scratch file keeps every commit non-empty even when the
        # map state is unchanged (e.g. an ageing but static open hole).
        self._tick += 1
        (self.root / "tick.txt").write_text(str(self._tick))
        _run(self.root, "add", "-A")
        env = {"GIT_AUTHOR_DATE": date, "GIT_COMMITTER_DATE": date}
        _run(self.root, "commit", "-q", "-m", msg, env=env)
        return _run(self.root, "rev-parse", "HEAD").stdout.strip()

    def checkout(self, *args):
        _run(self.root, "checkout", "-q", *args)

    def merge_ours(self, branch, date, msg):
        env = {"GIT_AUTHOR_DATE": date, "GIT_COMMITTER_DATE": date}
        _run(self.root, "merge", "-q", "-s", "ours", "--no-ff", branch, "-m", msg,
             env=env)
        return _run(self.root, "rev-parse", "HEAD").stdout.strip()


def _node(nid="a", status="stated", owner="me"):
    return {"id": nid, "kind": "claim", "status": status, "lean": "A", "owner": owner}


def test_not_a_git_repo(tmp_path):
    (tmp_path / "map").mkdir()
    (tmp_path / "map" / "claims.yaml").write_text(
        dump_claims([_node()], ["a"]))
    m = model.load_map(tmp_path / "map")
    h = history.build_history(m)
    assert h["_available"] is False


def test_transitions_and_first_parent_discipline(tmp_path):
    r = Repo(tmp_path)
    r.commit([_node(status="stated")], ["a"], "2026-06-01T10:00:00", "c1")
    r.commit([_node(status="adjudicated")], ["a"], "2026-06-02T10:00:00", "c2")
    r.checkout("-b", "side")
    side_sha = r.commit([_node(status="refuted", owner="teammate")], ["a"],
                        "2026-06-05T03:00:00", "s1")
    r.checkout("main")
    r.commit([_node(status="skeleton-linked")], ["a"], "2026-06-04T10:00:00", "c3")
    r.merge_ours("side", "2026-06-06T10:00:00", "merge side")

    m = model.load_map(r.map)
    h = history.build_history(m)
    assert h["_available"]
    # clock counts the 4 first-parent commits, NOT the side commit's hour.
    assert h["activity_clock"]["total_hours"] == 4
    a = h["nodes"]["a"]
    assert [(t["from"], t["to"]) for t in a["transitions"]] == [
        ("stated", "adjudicated"), ("adjudicated", "skeleton-linked")]
    assert a["current_status"] == "skeleton-linked"    # side's refuted invisible
    assert a["owner_changes"] == []                     # side's owner edit invisible
    assert all(t["sha"] != side_sha for t in a["transitions"])


def test_promotion_lag(tmp_path):
    r = Repo(tmp_path)
    r.commit([_node(status="adjudicated")], ["a"], "2026-06-01T10:00:00", "c1")
    r.commit([_node(status="skeleton-linked")], ["a"], "2026-06-04T10:00:00", "c2")
    m = model.load_map(r.map)
    h = history.build_history(m)
    lag = h["nodes"]["a"]["promotion_lag"]
    assert lag is not None and lag["ongoing"] is False
    assert lag["activity_hours"] >= 1
    assert lag["wall_days"] == 3


def test_oldest_open_hole_alarm(tmp_path):
    r = Repo(tmp_path)
    for i, d in enumerate(["2026-06-01T10:00:00", "2026-06-02T11:00:00",
                           "2026-06-03T12:00:00", "2026-06-04T13:00:00"]):
        r.commit([_node(status="stated")], ["a"], d, f"c{i}")
    m = model.load_map(r.map)
    # threshold below the node's activity age => fires.
    h = history.build_history(m, thresholds={"oldest_open_hole_activity_hours": 1})
    kinds = {a["kind"] for a in h["alarms"]}
    assert "oldest-open-hole" in kinds
    # a high threshold => no fire.
    h2 = history.build_history(m, thresholds={"oldest_open_hole_activity_hours": 999})
    assert "oldest-open-hole" not in {a["kind"] for a in h2["alarms"]}


def test_owner_churn_alarm(tmp_path):
    r = Repo(tmp_path)
    owners = ["me", "you", "them", "me2"]  # 3 changes within a tight window
    hours = ["2026-06-01T10:00:00", "2026-06-01T11:00:00",
             "2026-06-01T12:00:00", "2026-06-01T13:00:00"]
    for i, (o, d) in enumerate(zip(owners, hours)):
        r.commit([_node(status="stated", owner=o)], ["a"], d, f"c{i}")
    m = model.load_map(r.map)
    h = history.build_history(m, thresholds={
        "owner_churn_count": 2, "owner_churn_window_activity_hours": 24})
    assert "owner-churn" in {a["kind"] for a in h["alarms"]}
    assert h["nodes"]["a"]["owner_churn"] == 3


def test_incremental_snapshot_cache(tmp_path):
    r = Repo(tmp_path)
    r.commit([_node(status="stated")], ["a"], "2026-06-01T10:00:00", "c1")
    r.commit([_node(status="adjudicated")], ["a"], "2026-06-02T10:00:00", "c2")
    m = model.load_map(r.map)
    h1 = history.build_history(m)
    cache = h1["_cache"]
    assert cache["snapshots"]  # populated
    # second run with the cache reproduces the same transitions.
    h2 = history.build_history(m, cache=cache)
    assert [(t["from"], t["to"]) for t in h1["nodes"]["a"]["transitions"]] == \
           [(t["from"], t["to"]) for t in h2["nodes"]["a"]["transitions"]]


def test_calibration_time_in_status_join(tmp_path):
    r = Repo(tmp_path)
    r.commit([_node(status="stated")], ["a"], "2026-06-01T10:00:00", "c1")
    r.commit([_node(status="adjudicated")], ["a"], "2026-06-03T10:00:00", "c2")
    m = model.load_map(r.map)
    h = history.build_history(m)
    survey = {"history": {"nodes": h["nodes"]}}
    ops.calibration_add(r.map, "a", "1 activity-day", "?")
    out = ops.calibration_show(r.map, survey=survey)
    assert "time-in-status (predicted vs actual)" in out
    assert "a: predicted 1 activity-day" in out
    assert "actual in-status" in out
