#!/usr/bin/env python3
"""Joiner → substrate/threads.json + enriched events + pool_summary.md.

Joins performed (all mechanical):
  E1  event.update_n  → the doc commit that landed it (subject mentions UPDATE-N)
  E2  event.sha_refs  → resolved against real commit shas (prefix match)
  T1  thread slug     → commit span, counts, lean LoC (from commits.json)
  T2  thread slug     → combed role/pillar (from data/process.json, fuzzy key match)
  A1  self-account audit, cheap tier: fraction of ledger sha-refs that resolve;
      UPDATE-date vs landed-commit-date agreement.
Outputs joined events (events.json updated in place with landed_commit fields),
threads.json, pool_summary.md (first hard readouts + join-quality stats).
"""
from __future__ import annotations
import json
from collections import Counter, defaultdict
from pathlib import Path

D = Path(__file__).resolve().parent
commits = json.loads((D / "commits.json").read_text())["commits"]
events_doc = json.loads((D / "events.json").read_text())
events = events_doc["events"]
proc = json.loads((D.parent / "data" / "process.json").read_text())

by_short = {c["sha"]: c for c in commits}
full_index = sorted(c["sha_full"] for c in commits)


def resolve(pref: str):
    hits = [s for s in full_index if s.startswith(pref)] or \
           ([by_short[pref]["sha_full"]] if pref in by_short else [])
    return hits[0][:8] if len(hits) == 1 else None


# E1: update_n -> landing doc commit (earliest doc/docs commit citing it)
landing = {}
for c in sorted(commits, key=lambda c: c["author_iso"]):
    if c["kind"] in ("doc", "docs", "tick") or c["subject"].startswith("docs"):
        for n in c["update_refs"]:
            landing.setdefault(n, c)
n_e1 = 0
for ev in events:
    c = landing.get(ev["update_n"])
    if c:
        ev["landed_commit"] = c["sha"]; ev["landed_iso"] = c["author_iso"]; n_e1 += 1
    else:
        ev["landed_commit"] = None; ev["landed_iso"] = None

# E2: resolve sha refs
n_ref = n_res = 0
for ev in events:
    res = []
    for pref in ev["sha_refs"]:
        n_ref += 1
        r = resolve(pref)
        if r: res.append(r); n_res += 1
    ev["resolved_shas"] = res
(D / "events.json").write_text(json.dumps(events_doc, indent=1))

# T1/T2: threads
threads = defaultdict(lambda: {"n_commits": 0, "first_iso": None, "last_iso": None,
                               "adds_lean": 0, "dels_lean": 0, "updates": set(),
                               "kinds": Counter(), "role": None, "pillar": None})
for c in sorted(commits, key=lambda c: c["author_iso"]):
    slugs = set(c["thread_slugs"]) | ({c["scope"]} if c["scope"] and ("genm" in str(c["scope"]) or "/" in str(c["scope"])) else set())
    for s in slugs:
        t = threads[s]
        t["n_commits"] += 1
        t["first_iso"] = t["first_iso"] or c["author_iso"]
        t["last_iso"] = c["author_iso"]
        t["adds_lean"] += c["adds_lean"]; t["dels_lean"] += c["dels_lean"]
        t["kinds"][c["kind"]] += 1
for ev in events:
    for s in ev["thread_slugs"]:
        if s in threads:
            threads[s]["updates"].add(ev["update_n"])
for pt in proc["threads"]:
    key = pt["thread"]
    for s in threads:
        if key in s or s in key or s.replace("genm-", "") == key:
            threads[s]["role"] = pt.get("role"); threads[s]["pillar"] = pt.get("pillar_fed")
            break
tout = {s: {**t, "updates": sorted(t["updates"]), "kinds": dict(t["kinds"])}
        for s, t in sorted(threads.items())}
(D / "threads.json").write_text(json.dumps(tout, indent=1))

# A1 + summary readouts
date_agree = 0
for ev in events:
    if not ev.get("landed_iso"):
        ev["date_quality"] = "no-landing"
    elif ev["landed_iso"][:10] == ev["date"]:
        ev["date_quality"] = "ok"; date_agree += 1
    elif ev["landed_iso"][11:16] < "03:00":
        ev["date_quality"] = "midnight-straddle"
    else:
        ev["date_quality"] = "early-backfill"  # format-migration era: date=backfill, prefer landed_iso
catches = [ev for ev in events if {"corrected", "retracted", "refuted", "wall"} & set(ev["flags"])]
per_day_catch = Counter(ev["date"] for ev in catches)
per_day_land = Counter(ev["date"] for ev in events if "landed" in ev["flags"])
covered = sum(1 for t in tout.values() if t["role"])

rebased = sum(1 for c in commits
              if abs((__import__('datetime').datetime.fromisoformat(c["committer_iso"]) -
                      __import__('datetime').datetime.fromisoformat(c["author_iso"])).total_seconds()) > 3600)
S = ["# Pool summary (mechanical readouts + join quality)", "",
     f"- commits: {len(commits)}; ledger blocks: {len(events)} (unique {events_doc['_meta']['n_unique']})",
     f"- threads (slug-level): {len(tout)}; with combed role/pillar attached: {covered}",
     "",
     "## Join quality",
     f"- E1 update→landing-commit: {n_e1}/{len(events)} matched ({100*n_e1/len(events):.0f}%)",
     f"- E2 ledger sha-refs resolving to real commits: {n_res}/{n_ref} ({100*n_res/max(n_ref,1):.0f}%)",
     f"- A1 date-agreement (UPDATE header date == landing commit date): {date_agree}/{n_e1} ({100*date_agree/max(n_e1,1):.0f}%)",
     f"- rebase detector (author≠committer date >1h): {rebased}/{len(commits)} commits",
     "",
     "## Correction-event stream (corrected|retracted|refuted|wall), per day", ""]
S += [f"- {d}: {'▇' * min(n, 40)} {n}" for d, n in sorted(per_day_catch.items())]
S += ["", "## Landing events per day", ""]
S += [f"- {d}: {'▇' * min(n, 40)} {n}" for d, n in sorted(per_day_land.items())]
agents = Counter(a for ev in events for a in ev.get("agent_ids", []))
cls = Counter(r["cls"] for ev in events for r in ev.get("sha_refs_classified", []))
rec = sum(1 for ev in events if ev.get("anchor_ref") not in ("tip", None))
disagree = [ev for ev in events if ev.get("landed_iso") and ev["landed_iso"][:10] != ev["date"]]
S += ["", "## Ledger completeness & references",
      f"- blocks recovered from history (compacted away at tip): {rec}",
      f"- sha-ref classes: {dict(cls)}  (exists_unmerged = banked-on-work-branches volume)",
      f"- agent/tide ids referenced: {sum(agents.values())} mentions, {len(agents)} unique",
      f"- A1 date disagreements (ledger date ≠ landing-commit date): "
      + "; ".join(f"UPDATE-{ev['update_n']} ({ev['date']} vs {ev['landed_iso'][:10]})" for ev in disagree),
      ""]
S += ["", "## Top 15 threads by Lean LoC added", ""]
top = sorted(tout.items(), key=lambda kv: -kv[1]["adds_lean"])[:15]
S += [f"- `{s}`: +{t['adds_lean']:,} lean ({t['n_commits']} commits, "
      f"{t['first_iso'][:10]}→{t['last_iso'][:10]}, role={t['role']})" for s, t in top]
(D / "pool_summary.md").write_text("\n".join(S) + "\n")
print("\n".join(S[:14]))
print(f"[join] wrote threads.json ({len(tout)}), enriched events.json, pool_summary.md")
