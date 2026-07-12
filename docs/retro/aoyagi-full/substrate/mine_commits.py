#!/usr/bin/env python3
"""Git miner → substrate/commits.json  (H readouts, themes 1-2).

One record per commit in FORK..BRANCH with parsed subject-convention fields and
per-file numstat. Read-only against origin refs; regenerable anytime.

Join keys emitted: sha (short+full), update_refs (UPDATE-N), thread_slug,
teammate_tag, sha_refs (@xxxxxxxx in subjects), files[].path, files[].pillar.
"""
from __future__ import annotations
import json, re, subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]  # the worktree root
BRANCH = "origin/expedition/aoyagi-full"
FORK = "413566b3"  # merge-base with dev
OUT = Path(__file__).resolve().parent / "commits.json"

PILLARS = [
    ("sj-descent", "lean/DLNFibre/DLN/RLCT/Validate/RouteMSJ"),
    ("routem-engine", "lean/DLNFibre/DLN/RLCT/Validate/RouteM"),
    ("deepest-d1", "lean/DLNFibre/DLN/RLCT/Validate/Deepest"),
    ("d1-legs", "lean/DLNFibre/DLN/RLCT/Validate/D1"),
    ("r1-wiring", "lean/DLNFibre/DLN/RLCT/Validate/R1"),
    ("headline", "lean/DLNFibre/DLN/RLCT/Validate/Headline"),
    ("skeleton", "lean/DLNFibre/DLN/RLCT/Skeleton"),
    ("foundations", "lean/DLNFibre/DLN/RLCT/Foundations"),
    ("rlct-other", "lean/DLNFibre/DLN/RLCT"),
    ("lean-core", "lean/DLNFibre/Core"),
    ("lean-other", "lean/"),
    ("ledger", "expeditions/2026-06-20-aoyagi-full/synthesis.md"),
    ("discuss", "expeditions/2026-06-20-aoyagi-full/discuss-at-close.md"),
    ("threads", "expeditions/2026-06-20-aoyagi-full/threads"),
    ("expedition-docs", "expeditions/"),
    ("other", ""),
]

KIND_RE = re.compile(r"^(feat|fix|docs?|wip|setup|tick|thread|merge|integrate|refactor|test|chore|perf)\b", re.I)
SCOPE_RE = re.compile(r"^[a-z]+\(([^)]+)\)", re.I)
TEAMMATE_RE = re.compile(r"\[teammate:\s*([\w-]+)\]")
UPDATE_RE = re.compile(r"UPDATE-(\d+)")
SHAREF_RE = re.compile(r"@([0-9a-f]{8,10})\b")
ITEM_RE = re.compile(r"(?:discuss(?:-at-close)?\s*)?#(\d{2,3})\b")
SLUG_RE = re.compile(r"\b(genm-[a-z0-9-]+|fm3?/[a-z0-9-]+|fm-[a-z0-9-]+|crux2/[a-z0-9-]+|r1-[a-z0-9-]+|l2[a-z0-9-]*|d1[a-z0-9-]+|worktree-rung0[a-z0-9-]*)\b")


def pillar_of(path: str) -> str:
    best, blen = "other", -1
    for label, pref in PILLARS:
        if path.startswith(pref) and len(pref) > blen:
            best, blen = label, len(pref)
    return best


def run(args):
    return subprocess.run(["git", *args], cwd=REPO, check=True, text=True,
                          stdout=subprocess.PIPE).stdout


def main():
    fmt = "%x01%H%x02%h%x02%aI%x02%cI%x02%P%x02%s"
    raw = run(["log", f"{FORK}..{BRANCH}", f"--format={fmt}", "--numstat"])
    commits, cur = [], None
    for line in raw.splitlines():
        if line.startswith("\x01"):
            full, short, ai, ci, parents, subj = line[1:].split("\x02")
            scope = SCOPE_RE.search(subj)
            kindm = KIND_RE.match(subj)
            cur = {
                "sha": short, "sha_full": full, "author_iso": ai, "committer_iso": ci,
                "is_merge": len(parents.split()) > 1, "subject": subj,
                "kind": (kindm.group(1).lower().rstrip("s") if kindm else
                         ("merge" if subj.lower().startswith("merge") else "other")),
                "scope": scope.group(1) if scope else None,
                "teammate_tag": (TEAMMATE_RE.search(subj) or [None] and None) if not TEAMMATE_RE.search(subj) else TEAMMATE_RE.search(subj).group(1),
                "thread_slugs": sorted(set(SLUG_RE.findall(subj))),
                "update_refs": sorted({int(n) for n in UPDATE_RE.findall(subj)}),
                "sha_refs": SHAREF_RE.findall(subj),
                "item_refs": sorted({int(n) for n in ITEM_RE.findall(subj)}),
                "files": [], "adds_lean": 0, "dels_lean": 0, "adds_docs": 0, "dels_docs": 0,
            }
            commits.append(cur)
        elif cur is not None and "\t" in line:
            a, d, path = line.split("\t", 2)
            a = 0 if a == "-" else int(a); d = 0 if d == "-" else int(d)
            pil = pillar_of(path)
            cur["files"].append({"path": path, "adds": a, "dels": d, "pillar": pil})
            if path.startswith("lean/"):
                cur["adds_lean"] += a; cur["dels_lean"] += d
            else:
                cur["adds_docs"] += a; cur["dels_docs"] += d
    OUT.write_text(json.dumps({"_meta": {"branch": BRANCH, "fork": FORK,
                                          "n": len(commits)}, "commits": commits}, indent=1))
    kinds = {}
    for c in commits: kinds[c["kind"]] = kinds.get(c["kind"], 0) + 1
    print(f"[mine_commits] {len(commits)} commits → {OUT.name}; kinds: {kinds}")


if __name__ == "__main__":
    main()
