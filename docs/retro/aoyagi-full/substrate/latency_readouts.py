#!/usr/bin/env python3
"""Correction-latency readouts (H⁻): pair correction events with their named
targets and measure catch latency + trend.

Mechanical pairing: a block whose text contains correct/retract/supersede/
refute-class keywords within a short window of an `UPDATE-N` reference is
paired with target N. Latency = landed_iso(catcher) − landed_iso(target).
Conservative: only explicit named-target pairs (no inference).
Also: tide-cycle durations (commissioned-mention → landed-mention per slug).
"""
from __future__ import annotations
import json, re, subprocess
from collections import Counter
from datetime import datetime
from pathlib import Path

D = Path(__file__).resolve().parent
events = json.loads((D / "events.json").read_text())["events"]
by_n = {e["update_n"]: e for e in events}
T = lambda s: datetime.fromisoformat(s)

PAIR_RE = re.compile(
    r"(?:correct|CORRECT|retract|RETRACT|supersed|SUPERSED|refut|REFUT|invalidat|revis|REVIS)"
    r"[^.\n]{0,120}?UPDATE-(\d+)|UPDATE-(\d+)[^.\n]{0,60}?"
    r"(?:is |was |now )?(?:CORRECTED|RETRACTED|SUPERSEDED|REFUTED|over-optimistic|WRONG|invalid)")


def body_of(ev):
    ref = ev.get("anchor_ref", "tip")
    ref = "origin/expedition/aoyagi-full" if ref in ("tip", None) else ref
    txt = subprocess.run(["git", "show", f"{ref}:expeditions/2026-06-20-aoyagi-full/synthesis.md"],
                         cwd=D.parents[4], text=True, stdout=subprocess.PIPE).stdout
    return "\n".join(txt.splitlines()[ev["line_start"] - 1:ev["line_end"]])


# cache blobs per ref to avoid re-reading
_blob = {}
def body(ev):
    ref = ev.get("anchor_ref") or "tip"
    if ref not in _blob:
        r = "origin/expedition/aoyagi-full" if ref == "tip" else ref
        _blob[ref] = subprocess.run(
            ["git", "show", f"{r}:expeditions/2026-06-20-aoyagi-full/synthesis.md"],
            cwd=D.parents[4], text=True, stdout=subprocess.PIPE).stdout.splitlines()
    return "\n".join(_blob[ref][ev["line_start"] - 1:ev["line_end"]])


pairs = []
for ev in events:
    if not ({"corrected", "retracted", "superseded", "refuted", "recalibration", "overclaim"}
            & set(ev["flags"])):
        continue
    txt = body(ev)
    for m in PAIR_RE.finditer(txt):
        tgt = int(m.group(1) or m.group(2))
        if tgt == ev["update_n"] or tgt not in by_n:
            continue
        te, ce = by_n[tgt], ev
        if not (te.get("landed_iso") and ce.get("landed_iso")):
            continue
        hrs = (T(ce["landed_iso"]) - T(te["landed_iso"])).total_seconds() / 3600
        if 0 <= hrs < 24 * 14:
            pairs.append({"catcher": ce["update_n"], "target": tgt, "hours": round(hrs, 1),
                          "date": ce["date"], "header": ce["header"][:120]})

# dedup (same catcher→target once)
seen, uniq = set(), []
for p in pairs:
    k = (p["catcher"], p["target"])
    if k not in seen:
        seen.add(k); uniq.append(p)

by_week = Counter()
wk_hours = {}
for p in uniq:
    wk = p["date"][:8] + ("early" if int(p["date"][8:]) <= 15 else "late")
    by_week[wk] += 1
    wk_hours.setdefault(wk, []).append(p["hours"])

med = lambda xs: sorted(xs)[len(xs) // 2] if xs else None
hours = sorted(p["hours"] for p in uniq)
S = ["# Correction-latency readouts (explicit named-target pairs only)", "",
     "**Caveats (honest):** (1) named-target subsample — corrections that cite their target",
     "as `UPDATE-N`; the quick self-correction style does this, long sagas often don't →",
     "median is biased LOW. Full pairing = the S-grade pass over drill-in anchors.",
     "(2) latency is block-to-block; error *introduction* may precede the target block.", "",
     f"- pairs found: {len(uniq)} (conservative: named targets only)",
     f"- latency hours: median {med(hours)}, p25 {hours[len(hours)//4] if hours else '-'}, "
     f"p75 {hours[3*len(hours)//4] if hours else '-'}, max {hours[-1] if hours else '-'}",
     "", "## Median catch-latency by half-month", ""]
S += [f"- {wk}: median {med(hs)}h over {by_week[wk]} pairs" for wk, hs in sorted(wk_hours.items())]
S += ["", "## Longest-lived corrected claims (top 10)", ""]
S += [f"- {p['hours']:>6.1f}h  UPDATE-{p['target']} → corrected by UPDATE-{p['catcher']} ({p['date']})"
      for p in sorted(uniq, key=lambda p: -p["hours"])[:10]]
(D / "latency_summary.md").write_text("\n".join(S) + "\n")
(D / "latency_pairs.json").write_text(json.dumps(uniq, indent=1))
print("\n".join(S))
