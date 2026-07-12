#!/usr/bin/env python3
"""Ledger parser → substrate/events.json  (H readouts, themes 5-6 event stream).

One record per ⚙ UPDATE block in synthesis.md (read from BRANCH, not the
working tree), with header metadata, keyword flags, references, and body
line-offsets so later semantic passes can drill into the exact text.

Join keys: update_n, sha_refs, thread_slugs, item_refs, landed_commit (filled
by join.py from commits.json).
"""
from __future__ import annotations
import json, re, subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
BRANCH = "origin/expedition/aoyagi-full"
LEDGER = "expeditions/2026-06-20-aoyagi-full/synthesis.md"
OUT = Path(__file__).resolve().parent / "events.json"

HEADER_RE = re.compile(r"^\*?\*?⚙ UPDATE-(\d+)\s*\((\d{4}-\d\d-\d\d)")
SHAREF_RE = re.compile(r"@?\b([0-9a-f]{8})\b")
SLUG_RE = re.compile(r"\b(genm-[a-z0-9-]+|fm3?/[a-z0-9-]+|fm-[a-z0-9-]+|crux2/[a-z0-9-]+|r1-[a-z0-9-]+|d1[a-z0-9]+|l2[a-z0-9]+)\b")
ITEM_RE = re.compile(r"(?:#|Item[ -])(\d{2,3})\b")

# keyword flags: (flag_name, regex, header_only)
FLAGS = [
    ("wall",          re.compile(r"\bWALL\b"), False),
    ("retracted",     re.compile(r"RETRACT", re.I), False),
    ("corrected",     re.compile(r"CORRECT(?:ED|S|ION)", re.I), False),
    ("refuted",       re.compile(r"REFUT", re.I), False),
    ("superseded",    re.compile(r"SUPERSED", re.I), False),
    ("recalibration", re.compile(r"RECALIBRAT", re.I), False),
    ("overclaim",     re.compile(r"over-?claim", re.I), False),
    ("lesson",        re.compile(r"\bLESSON\b", re.I), False),
    ("landed",        re.compile(r"\b(landed|LANDED|integrated|INTEGRATED)\b"), False),
    ("clean_three",   re.compile(r"clean-three|axiom-clean", re.I), False),
    ("commissioned",  re.compile(r"commission", re.I), False),
    ("stood_down",    re.compile(r"stood down|stand.down", re.I), False),
    ("hold",          re.compile(r"\bHOLD(?:ING)?\b|\bHELD\b"), False),
    ("verdict",       re.compile(r"\bVERDICT\b"), False),
    ("pass",          re.compile(r"\bPASS(?:ED)?\b"), False),
    ("decorrelated",  re.compile(r"decorrelat", re.I), False),
    ("codex",         re.compile(r"\bCodex\b"), False),
    ("operator",      re.compile(r"\boperator\b", re.I), False),
    ("design",        re.compile(r"\bdesign\b", re.I), False),
    ("pivot",         re.compile(r"\bPIVOT\b|re-point", re.I), False),
    ("star1",         re.compile(r"★"), True),
    ("star2",         re.compile(r"★★"), True),
    ("star3",         re.compile(r"★★★"), True),
    ("checkmark",     re.compile(r"✅"), True),
    ("warn",          re.compile(r"⚠"), True),
]


def main():
    text = subprocess.run(["git", "show", f"{BRANCH}:{LEDGER}"], cwd=REPO, check=True,
                          text=True, stdout=subprocess.PIPE).stdout
    lines = text.splitlines()
    # locate headers
    heads = [(i, m) for i, ln in enumerate(lines) if (m := HEADER_RE.match(ln))]
    events = []
    for k, (i, m) in enumerate(heads):
        end = heads[k + 1][0] if k + 1 < len(heads) else len(lines)
        header = lines[i]
        body = "\n".join(lines[i:end])
        ev = {
            "update_n": int(m.group(1)), "date": m.group(2),
            "line_start": i + 1, "line_end": end,  # 1-based, into synthesis.md@BRANCH
            "header": header[:400],
            "n_lines": end - i,
            "thread_slugs": sorted(set(SLUG_RE.findall(body)))[:12],
            "sha_refs": sorted(set(SHAREF_RE.findall(body)))[:12],
            "item_refs": sorted({int(n) for n in ITEM_RE.findall(body)})[:12],
            "flags": sorted(f for f, rx, honly in FLAGS if rx.search(header if honly else body)),
        }
        events.append(ev)
    # duplicates happen (live-block + archived-block for the same N): keep all, mark
    seen = {}
    for ev in events:
        seen.setdefault(ev["update_n"], []).append(ev)
        ev["dup"] = len(seen[ev["update_n"]]) > 1
    OUT.write_text(json.dumps({"_meta": {"branch": BRANCH, "ledger": LEDGER,
                                          "n": len(events),
                                          "n_unique": len(seen)}, "events": events}, indent=1))
    nflag = {}
    for ev in events:
        for f in ev["flags"]:
            nflag[f] = nflag.get(f, 0) + 1
    print(f"[parse_ledger] {len(events)} blocks ({len(seen)} unique N) → {OUT.name}")
    print("  flag counts:", dict(sorted(nflag.items(), key=lambda x: -x[1])))


if __name__ == "__main__":
    main()
