#!/usr/bin/env python3
"""aoyagi-full LoC diagnostics — a completion report for a single, finished expedition.

Adapted and uplifted from `generate_aoyagi_principled_loc.py` (the geometry-of-dln-fibre
diagnostic tool). Provenance kept alongside as `generate_aoyagi_principled_loc.py.orig`.

Three shared metrics, per commit, over Git author time:
  1. Lean raw physical LoC       — every `.lean` line, comments included.
  2. Lean native code-token LoC  — real Lean 4.29/Mathlib tokens after comment/doc skipping
                                    (`LeanNativeTokenLineCount.lean`); the "proof-mass" metric.
  3. Non-Lean expedition text LoC — UTF-8 docs under the expedition path.

QS-specific uplift (exploits that this expedition is complete, single-branch, one-round):
  * per-pillar breakdown of Lean LoC (Base / Extended / Horrocks / Patching / Induction /
    Localization / headline) — stacked area over time + final bars ("the sea, layer by layer");
  * milestone-annotated cumulative timeline (scaffold → Layer 0 → R1 closed → endgame → headline);
  * churn panel: gross Lean lines added vs deleted per bucket (the write-then-discard / refutation
    cost that net LoC hides).

The Lean toolchain (`lake env lean`) is invoked from `--lean-dir` (default: the repo's set-up
`lean/`); all git ops are read-only against `--repo`. Outputs land next to this script.
"""

from __future__ import annotations

import csv
import json
import os
import subprocess
import tempfile
import argparse
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

FIG_DIR = Path(__file__).resolve().parent
COUNTER = FIG_DIR / "LeanNativeTokenLineCount.lean"
CACHE_PATH = FIG_DIR / "native-token-blob-cache.json"
TOKEN_BATCH_SIZE = 200
CACHE_VERSION = "native-token-v2-count-error-lines"

# Configured in main(); module globals so the copied helpers resolve them at call time.
REPO = Path("/home/ubuntu/workspace/geometry-of-dln-fibre")
LEAN_DIR = REPO / "lean"

BRANCH = "origin/expedition/aoyagi-full"
BASE: str | None = "413566b3"  # fork from dev (net-of-fork counts)
# Plot endpoint: the branch is MID-FLIGHT; endpoint = the fetched tip at generation time.
HEAD_REV = "339811e8985a3a4e82cacbd1c1194fa3c495aeda"
LEAN_PATH = "lean/DLNFibre/DLN/RLCT"
NONLEAN_PATH = "expeditions/2026-06-20-aoyagi-full"
MODULE = "Mathlib"

PILLARS: list[tuple[str, str]] = [
    ("(S,J) descent + ledger", "lean/DLNFibre/DLN/RLCT/Validate/RouteMSJ"),
    ("Route-M box/peel engine", "lean/DLNFibre/DLN/RLCT/Validate/RouteM"),
    ("Deepest point / D1", "lean/DLNFibre/DLN/RLCT/Validate/Deepest"),
    ("D1 legs / gauge", "lean/DLNFibre/DLN/RLCT/Validate/D1"),
    ("R1 resolution wiring", "lean/DLNFibre/DLN/RLCT/Validate/R1"),
    ("Headlines & assembly", "lean/DLNFibre/DLN/RLCT/Validate/Headline"),
    ("Skeleton (defs/rungs)", "lean/DLNFibre/DLN/RLCT/Skeleton"),
    ("Foundations", "lean/DLNFibre/DLN/RLCT/Foundations"),
    ("Other (Validate misc)", "lean/DLNFibre/DLN/RLCT"),
]

MILESTONES: list[tuple[str, str]] = [
    ("b92ce5a9", "launch"),
    ("220916ae", "carve triply-certified"),
    ("6fd03723", "L=2 headline DONE"),
    ("57ea5c36", "(□) recalibration"),
    ("1b02bc3d", "atom fork #97"),
    ("c6133011", "§5 lane (operator)"),
    ("b142a966", "DecoratedDescent re-point"),
    ("c25b0b73", "minAdm=cCodim ∀widths"),
]

# Curated milestones (sha-prefix, short label). Times resolved from git; missing ones skipped.
MILESTONES: list[tuple[str, str]] = [
    ("fa13713", "scaffold"),
    ("785874b", "recon: ladder sized"),
    ("93280a3", "Layer 0 (base) landed"),
    ("61b41f1", "R2 α′ core proven"),
    ("e75cae1", "R1 Horrocks CLOSED"),
    ("2e457d7", "R2+R3 endgame composes"),
    ("721b0db", "headline landed (axiom-clean)"),
]

BINARY_EXTS = {
    ".7z", ".bmp", ".bz2", ".class", ".dll", ".dylib", ".gif", ".gz", ".ico", ".jpeg",
    ".jpg", ".mp3", ".mp4", ".o", ".olean", ".pdf", ".pickle", ".png", ".pyc", ".so",
    ".tar", ".tiff", ".webp", ".xz", ".zip",
}


@dataclass
class BlobEntry:
    sha: str
    path: str


@dataclass
class CommitSnapshot:
    commit: str
    author_time: str
    commit_time: str
    subject: str
    lean_blobs: list[BlobEntry]
    nonlean_blobs: list[BlobEntry]


# ---------------------------------------------------------------------------
# git plumbing (read-only against REPO)
# ---------------------------------------------------------------------------

def run_git(args: list[str], *, text: bool = True) -> str | bytes:
    result = subprocess.run(
        ["git", *args], cwd=REPO, check=True, text=text,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    return result.stdout


def parse_iso(ts: str) -> datetime:
    return datetime.fromisoformat(ts.replace("Z", "+00:00"))


def physical_line_count(data: bytes) -> int:
    if not data:
        return 0
    return len(data.decode("utf-8", errors="replace").splitlines())


def is_probably_text(data: bytes) -> bool:
    if b"\x00" in data:
        return False
    try:
        data.decode("utf-8")
    except UnicodeDecodeError:
        return False
    return True


def nonlean_candidate(path: str) -> bool:
    suffix = Path(path).suffix.lower()
    if suffix == ".lean":
        return False
    return suffix not in BINARY_EXTS


def git_log_records() -> list[tuple[str, str, str, str]]:
    fmt = "%H%x1f%aI%x1f%cI%x1f%s%x1e"
    rev = f"{BASE}..{HEAD_REV}" if BASE else HEAD_REV
    raw = run_git(["log", "--reverse", f"--format={fmt}", rev, "--", LEAN_PATH, NONLEAN_PATH])
    records = []
    for chunk in raw.rstrip("\x1e").split("\x1e"):
        chunk = chunk.strip("\n")
        if not chunk or "\x1f" not in chunk:
            continue
        commit, author_time, commit_time, subject = chunk.split("\x1f", 3)
        records.append((commit, author_time, commit_time, subject))
    return records


def ls_tree_blobs(commit: str, path: str) -> list[BlobEntry]:
    raw = run_git(["ls-tree", "-r", "-z", commit, "--", path], text=False)
    entries: list[BlobEntry] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        meta, file_path = record.split(b"\t", 1)
        _mode, obj_type, sha = meta.split()[:3]
        if obj_type == b"blob":
            entries.append(BlobEntry(sha.decode(), file_path.decode()))
    return entries


def cat_blobs(shas: Iterable[str]) -> dict[str, bytes]:
    ordered = sorted(set(shas))
    if not ordered:
        return {}
    payload = "".join(f"{sha}\n" for sha in ordered).encode()
    result = subprocess.run(
        ["git", "cat-file", "--batch"], cwd=REPO, input=payload,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
    )
    out = result.stdout
    pos = 0
    blobs: dict[str, bytes] = {}
    while pos < len(out):
        header_end = out.index(b"\n", pos)
        header = out[pos:header_end].decode()
        pos = header_end + 1
        sha, obj_type, size_s = header.split()
        if obj_type != "blob":
            raise RuntimeError(f"Expected blob for {sha}, got {obj_type}")
        size = int(size_s)
        blobs[sha] = out[pos: pos + size]
        pos += size
        if pos < len(out) and out[pos: pos + 1] == b"\n":
            pos += 1
    return blobs


# ---------------------------------------------------------------------------
# native-token counter (Lean) + blob cache
# ---------------------------------------------------------------------------

def load_token_cache() -> dict[str, dict[str, int]]:
    if not CACHE_PATH.exists():
        return {}
    with CACHE_PATH.open("r", encoding="utf-8") as f:
        data = json.load(f)
    if data.get("_meta", {}).get("version") != CACHE_VERSION:
        return {}
    blobs = data.get("blobs", {})
    return {sha: {"native_token_loc": int(v["native_token_loc"]),
                  "token_errors": int(v["token_errors"])} for sha, v in blobs.items()}


def save_token_cache(cache: dict[str, dict[str, int]]) -> None:
    payload = {
        "_meta": {"version": CACHE_VERSION, "counter": str(COUNTER),
                  "description": "token-parser-error lines counted conservatively as code; count in token_errors."},
        "blobs": {sha: cache[sha] for sha in sorted(cache)},
    }
    with CACHE_PATH.open("w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
        f.write("\n")


def run_native_counter(missing: list[str], blobs: dict[str, bytes]) -> dict[str, dict[str, int]]:
    if not missing:
        return {}
    with tempfile.TemporaryDirectory(prefix="qs-native-token-") as tmp_s:
        tmp = Path(tmp_s)
        blob_dir = tmp / "blobs"
        blob_dir.mkdir()
        list_path = tmp / "blob-paths.txt"
        sha_by_path: dict[str, str] = {}
        with list_path.open("w", encoding="utf-8") as f:
            for sha in missing:
                p = blob_dir / f"{sha}.lean"
                p.write_bytes(blobs[sha])
                f.write(str(p) + "\n")
                sha_by_path[str(p)] = sha
        env = os.environ.copy()
        env.setdefault("MPLCONFIGDIR", str(Path("/tmp") / "matplotlib-cache"))
        cmd = ["lake", "env", "lean", "--run", str(COUNTER), "--module", MODULE,
               "--file-list", str(list_path)]
        result = subprocess.run(cmd, cwd=LEAN_DIR, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
        rows = result.stdout.splitlines()
        if not rows or rows[0] != "path\tnative_token_loc\ttoken_errors":
            raise RuntimeError(f"Unexpected Lean counter output:\n{result.stdout}\n{result.stderr}")
        counted: dict[str, dict[str, int]] = {}
        for row in rows[1:]:
            path, loc_s, errors_s = row.split("\t")
            counted[sha_by_path[path]] = {"native_token_loc": int(loc_s), "token_errors": int(errors_s)}
        if len(counted) != len(missing):
            raise RuntimeError(f"counter returned {len(counted)} rows for {len(missing)} blobs")
        return counted


def chunks(items: list[str], size: int) -> Iterable[list[str]]:
    for start in range(0, len(items), size):
        yield items[start: start + size]


def ensure_native_counts(lean_shas: set[str], blobs: dict[str, bytes]) -> dict[str, dict[str, int]]:
    cache = load_token_cache()
    missing = sorted(sha for sha in lean_shas if sha not in cache)
    print(f"[native-token] cache hit={len(lean_shas) - len(missing)} missing={len(missing)}")
    for i, batch in enumerate(chunks(missing, TOKEN_BATCH_SIZE), start=1):
        print(f"[native-token] batch {i} size={len(batch)}")
        cache.update(run_native_counter(batch, blobs))
        save_token_cache(cache)
    return cache


# ---------------------------------------------------------------------------
# pillar mapping + churn
# ---------------------------------------------------------------------------

def pillar_of(path: str) -> str:
    best_label, best_len = PILLARS[-1][0], -1
    for label, prefix in PILLARS:
        if path.startswith(prefix) and len(prefix) > best_len:
            best_label, best_len = label, len(prefix)
    return best_label


def churn_by_bucket(bucket_hours: int) -> dict[datetime, dict[str, int]]:
    """Gross Lean lines added / deleted per author-time bucket (via --numstat)."""
    rev = f"{BASE}..{HEAD_REV}" if BASE else HEAD_REV
    # NB: use a literal marker + newline split. `str.splitlines()` also breaks on the
    # \x1e/\x1f control chars, so those must not be used as record delimiters here.
    raw = run_git(["log", "--reverse", "--no-merges", "--numstat",
                   "--format=COMMITMARK%x09%H%x09%aI", rev, "--", LEAN_PATH])
    buckets: dict[datetime, dict[str, int]] = {}
    author_time = None
    for line in str(raw).split("\n"):
        if line.startswith("COMMITMARK\t"):
            _, _sha, author_time = line.split("\t")
            continue
        if not line.strip() or author_time is None:
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        added_s, deleted_s, path = parts
        if added_s == "-" or not path.endswith(".lean"):
            continue
        b = bucket_start(parse_iso(author_time), bucket_hours)
        slot = buckets.setdefault(b, {"added": 0, "deleted": 0})
        slot["added"] += int(added_s or 0)
        slot["deleted"] += int(deleted_s or 0)
    return buckets


def bucket_start(dt: datetime, hours: int) -> datetime:
    dt = dt.astimezone(timezone.utc)
    return dt.replace(hour=(dt.hour // hours) * hours, minute=0, second=0, microsecond=0)


# ---------------------------------------------------------------------------
# collection
# ---------------------------------------------------------------------------

def collect_snapshots() -> list[CommitSnapshot]:
    commits = git_log_records()
    snaps: list[CommitSnapshot] = []
    for i, (commit, at, ct, subject) in enumerate(commits, start=1):
        if i == 1 or i == len(commits) or i % 25 == 0:
            print(f"[collect] {i}/{len(commits)} {commit[:8]}")
        lean = [e for e in ls_tree_blobs(commit, LEAN_PATH) if e.path.endswith(".lean")]
        nonlean = [e for e in ls_tree_blobs(commit, NONLEAN_PATH) if nonlean_candidate(e.path)]
        snaps.append(CommitSnapshot(commit, at, ct, subject, lean, nonlean))
    return snaps


def comma(n: float | int) -> str:
    return f"{int(n):,}"


# ---------------------------------------------------------------------------
# figures
# ---------------------------------------------------------------------------

def resolve_milestones(snaps: list[CommitSnapshot]) -> list[tuple[datetime, str]]:
    by_prefix: list[tuple[datetime, str]] = []
    for sha_prefix, label in MILESTONES:
        try:
            at = run_git(["show", "-s", "--format=%aI", sha_prefix]).strip().splitlines()[0]
            by_prefix.append((parse_iso(at), label))
        except Exception:
            print(f"[milestone] skipped {sha_prefix} ({label}) — not found")
    return sorted(by_prefix)


def add_hours_from_base(ax, t0):
    """Secondary top x-axis showing hours elapsed from the base commit (t0)."""
    import matplotlib.dates as mdates
    x0 = mdates.date2num(t0)
    secax = ax.secondary_xaxis("top", functions=(lambda x: (x - x0) * 24.0,
                                                 lambda h: x0 + h / 24.0))
    secax.set_xlabel("hours from base (scaffold)", fontsize=9)
    return secax


def extend_right(ax, frac=0.06):
    """Pad the right of the x-axis so the final data point/bar — and the headline milestone
    label, which now sits at the endpoint — is not flush against (or clipped by) the spine."""
    lo, hi = ax.get_xlim()
    ax.set_xlim(lo, hi + (hi - lo) * frac)


def fig_three_metric(rows, milestones, generated, bucket_hours, churn):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.dates as mdates
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FuncFormatter

    C = {"raw": "#2563eb", "native": "#16a34a", "nonlean": "#64748b",
         "add": "#16a34a", "del": "#dc2626"}
    plotted = sorted(rows, key=lambda r: (parse_iso(r["author_time"]), r["commit"]))
    dates = [parse_iso(r["author_time"]) for r in plotted]
    raw = [r["lean_raw_loc"] for r in plotted]
    native = [r["lean_native_token_loc"] for r in plotted]
    nonlean = [r["nonlean_loc"] for r in plotted]
    end = plotted[-1]

    fig, axes = plt.subplots(2, 1, figsize=(14.5, 10.5), gridspec_kw={"height_ratios": [1.1, 1]})
    ax, ax_non = axes[0], axes[0].twinx()
    ax.plot(dates, raw, color=C["raw"], lw=2, marker="o", ms=2.6,
            label=f"Lean raw physical LoC: {comma(end['lean_raw_loc'])}")
    ax.plot(dates, native, color=C["native"], lw=2, marker="o", ms=2.6,
            label=f"Lean native code-token LoC: {comma(end['lean_native_token_loc'])}")
    ax_non.plot(dates, nonlean, color=C["nonlean"], lw=2, ls="--", marker="o", ms=2.6,
                label=f"Non-Lean expedition text LoC: {comma(end['nonlean_loc'])}")
    for mdt, label in milestones:
        ax.axvline(mdt, color="#b45309", lw=1.0, ls=":", alpha=0.75)
        ax.text(mdt, ax.get_ylim()[1] * 0.02, " " + label, rotation=90, va="bottom", ha="left",
                fontsize=7.6, color="#b45309")
    ax.set_title("aoyagi-full: cumulative LoC over author time (annotated)", fontsize=13,
                 fontweight="bold", pad=42)
    ax.set_ylabel("Lean LoC")
    ax_non.set_ylabel("Non-Lean LoC", color=C["nonlean"])
    ax_non.tick_params(axis="y", labelcolor=C["nonlean"])
    ax.grid(True, color="#d9d9d9", lw=0.8, alpha=0.65)
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: comma(v)))
    ax_non.yaxis.set_major_formatter(FuncFormatter(lambda v, _: comma(v)))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d\n%H:%M", tz=timezone.utc))
    h1, l1 = ax.get_legend_handles_labels()
    h2, l2 = ax_non.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, loc="upper left", framealpha=0.92)
    extend_right(ax)
    add_hours_from_base(ax, dates[0])

    # churn panel (gross Lean added / deleted per bucket)
    ax2 = axes[1]
    bdates = sorted(churn)
    added = [churn[d]["added"] for d in bdates]
    deleted = [-churn[d]["deleted"] for d in bdates]
    x = mdates.date2num(bdates)
    width = bucket_hours / 24 * 0.7
    ax2.bar(x, added, width=width, color=C["add"], alpha=0.85, label=f"Lean lines added: {comma(sum(added))}")
    ax2.bar(x, deleted, width=width, color=C["del"], alpha=0.85,
            label=f"Lean lines deleted: {comma(-sum(deleted))}")
    ax2.axhline(0, color="#333", lw=0.8)
    ax2.set_title(f"Lean churn per {bucket_hours}h bucket — gross added (up) vs deleted (down)",
                  fontsize=13, fontweight="bold", pad=42)
    ax2.set_ylabel("Lean lines")
    ax2.grid(True, axis="y", color="#d9d9d9", lw=0.8, alpha=0.65)
    ax2.yaxis.set_major_formatter(FuncFormatter(lambda v, _: comma(v)))
    ax2.xaxis_date()
    ax2.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d\n%H:%M", tz=timezone.utc))
    ax2.legend(loc="upper left", framealpha=0.92)
    extend_right(ax2)
    add_hours_from_base(ax2, dates[0])

    fig.suptitle("aoyagi-full formalisation — LoC over one expedition (raw · native-code · non-Lean) + churn",
                 fontsize=16, fontweight="bold", y=0.995)
    fig.text(0.012, 0.012,
             f"Generated {generated}Z. Branch `{BRANCH}`, root → headline-resolution `{HEAD_REV[:8]}`. Native LoC = Lean 4.29/Mathlib "
             f"token lines after comment/doc skipping (unknown-token lines count as code). "
             f"Bottom x-axis = author (wall-clock) time; top x-axis = hours from base (scaffold); "
             f"non-Lean on right y-axis. Churn from `git log --numstat` over `{LEAN_PATH}`.",
             fontsize=8.2, color="#334155")
    fig.tight_layout(rect=[0, 0.055, 1, 0.93])
    out = FIG_DIR / "aoyagi-3metric-churn-author-time.annotated.png"
    fig.savefig(out, dpi=160)
    plt.close(fig)
    print(f"[fig] {out}")


def fig_pillars(pillar_series, pillar_final, dates, milestones, generated):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.dates as mdates
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FuncFormatter

    labels = [lab for lab, _ in PILLARS]
    palette = ["#2563eb", "#7c3aed", "#16a34a", "#ea580c", "#dc2626", "#0891b2", "#ca8a04", "#0d9488", "#64748b"]
    fig, axes = plt.subplots(1, 2, figsize=(16.5, 7.6), gridspec_kw={"width_ratios": [2.05, 1]})

    ax = axes[0]
    stack = [[pillar_series[i][lab] for lab in labels] for i in range(len(dates))]
    ys = list(zip(*stack)) if stack else [[] for _ in labels]
    ax.stackplot(dates, *ys, labels=labels, colors=[palette[i % len(palette)] for i in range(len(labels))], alpha=0.9)
    for mdt, label in milestones:
        ax.axvline(mdt, color="#334155", lw=1.0, ls=":", alpha=0.7)
        ax.text(mdt, ax.get_ylim()[1] * 0.98, " " + label, rotation=90, va="top", ha="left",
                fontsize=7.4, color="#334155")
    ax.set_title("Native code-token LoC by ladder pillar (cumulative)", fontsize=13,
                 fontweight="bold", pad=42)
    ax.set_ylabel("Lean native code-token LoC")
    ax.grid(True, color="#e2e2e2", lw=0.7, alpha=0.6)
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: comma(v)))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d\n%H:%M", tz=timezone.utc))
    ax.legend(loc="upper left", fontsize=9, framealpha=0.92)
    extend_right(ax)
    add_hours_from_base(ax, dates[0])

    ax = axes[1]
    vals = [pillar_final[lab] for lab in labels]
    order = sorted(range(len(labels)), key=lambda i: vals[i], reverse=True)
    y = list(range(len(order)))
    ax.barh(y, [vals[i] for i in order], color=[palette[i % len(palette)] for i in order], alpha=0.9)
    ax.set_yticks(y, [labels[i] for i in order], fontsize=9)
    ax.invert_yaxis()
    for yi, i in enumerate(order):
        ax.text(vals[i], yi, f" {comma(vals[i])}", va="center", fontsize=9)
    ax.set_title("Final native LoC per pillar", fontsize=13, fontweight="bold")
    ax.grid(True, axis="x", color="#e2e2e2", lw=0.7, alpha=0.6)
    ax.xaxis.set_major_formatter(FuncFormatter(lambda v, _: comma(v)))

    fig.suptitle("aoyagi-full: where the proof mass lives — Lean native code-token LoC by pillar",
                 fontsize=16, fontweight="bold", y=0.99)
    fig.text(0.012, 0.015,
             f"Generated {generated}Z. Pillars are subtrees of `{LEAN_PATH}`; native LoC excludes comments/docs. "
             "'Headline + axiom gate' is the catch-all top level (Theorem/AxCheck/Basic/aggregator).",
             fontsize=8.4, color="#334155")
    fig.tight_layout(rect=[0, 0.045, 1, 0.92])
    out = FIG_DIR / "aoyagi-pillars-native-loc.annotated.png"
    fig.savefig(out, dpi=160)
    plt.close(fig)
    print(f"[fig] {out}")


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main() -> None:
    global REPO, LEAN_DIR, BRANCH, BASE, LEAN_PATH, NONLEAN_PATH, MODULE, HEAD_REV
    ap = argparse.ArgumentParser(description="aoyagi-full LoC diagnostics (mid-flight).")
    ap.add_argument("--repo", default=str(REPO))
    ap.add_argument("--lean-dir", default=None, help="Dir to run `lake env lean` from (default <repo>/lean).")
    ap.add_argument("--branch", default=BRANCH)
    ap.add_argument("--base", default=BASE)
    ap.add_argument("--lean-path", default=LEAN_PATH)
    ap.add_argument("--nonlean-path", default=NONLEAN_PATH)
    ap.add_argument("--module", default=MODULE)
    ap.add_argument("--bucket-hours", type=int, default=6)
    ap.add_argument("--head-rev", default=HEAD_REV,
                    help="Commit to plot up to (default: the headline-resolution commit, not the moving tip).")
    args = ap.parse_args()
    REPO = Path(args.repo)
    LEAN_DIR = Path(args.lean_dir) if args.lean_dir else REPO / "lean"
    BRANCH, BASE = args.branch, args.base
    LEAN_PATH, NONLEAN_PATH, MODULE = args.lean_path, args.nonlean_path, args.module
    HEAD_REV = args.head_rev

    generated = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S")
    print(f"[start] repo={REPO} branch={BRANCH} base={BASE} generated={generated}Z")

    snaps = collect_snapshots()
    if not snaps:
        raise RuntimeError("no commits touch the configured paths")

    lean_shas = {e.sha for s in snaps for e in s.lean_blobs}
    all_shas = lean_shas | {e.sha for s in snaps for e in s.nonlean_blobs}
    print(f"[blobs] lean unique={len(lean_shas)} all unique={len(all_shas)}")
    blobs = cat_blobs(all_shas)
    raw_lines = {sha: physical_line_count(d) for sha, d in blobs.items()}
    text_lines = {sha: physical_line_count(d) if is_probably_text(d) else 0 for sha, d in blobs.items()}
    native = ensure_native_counts(lean_shas, blobs)

    rows: list[dict] = []
    pillar_series: list[dict[str, int]] = []
    labels = [lab for lab, _ in PILLARS]
    prev = {"raw": 0, "native": 0, "nonlean": 0}
    for s in snaps:
        lean_raw = sum(raw_lines.get(e.sha, 0) for e in s.lean_blobs)
        lean_nat = sum(native.get(e.sha, {}).get("native_token_loc", 0) for e in s.lean_blobs)
        errs = sum(native.get(e.sha, {}).get("token_errors", 0) for e in s.lean_blobs)
        nonlean = sum(text_lines.get(e.sha, 0) for e in s.nonlean_blobs)
        pill = {lab: 0 for lab in labels}
        for e in s.lean_blobs:
            pill[pillar_of(e.path)] += native.get(e.sha, {}).get("native_token_loc", 0)
        pillar_series.append(pill)
        rows.append({
            "author_time": s.author_time, "commit_time": s.commit_time, "commit": s.commit[:8],
            "lean_raw_loc": lean_raw, "lean_native_token_loc": lean_nat,
            "lean_native_token_errors": errs, "nonlean_loc": nonlean,
            "lean_raw_delta": lean_raw - prev["raw"], "lean_native_token_delta": lean_nat - prev["native"],
            "nonlean_delta": nonlean - prev["nonlean"], "subject": s.subject,
            **{f"pillar::{lab}": pill[lab] for lab in labels},
        })
        prev = {"raw": lean_raw, "native": lean_nat, "nonlean": nonlean}

    # CSV
    with (FIG_DIR / "aoyagi-loc-by-commit.csv").open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    milestones = resolve_milestones(snaps)
    churn = churn_by_bucket(args.bucket_hours)
    dates = [parse_iso(r["author_time"]) for r in rows]
    pillar_final = pillar_series[-1]
    end = rows[-1]

    total_added = sum(v["added"] for v in churn.values())
    total_deleted = sum(v["deleted"] for v in churn.values())
    summary = {
        "generated": generated + "Z", "repo": str(REPO), "branch": BRANCH, "base": BASE,
        "head_rev": HEAD_REV, "endpoint": "mid-flight branch tip",
        "tip": run_git(["rev-parse", HEAD_REV]).strip(), "path_commits": len(rows),
        "lean_raw_loc": end["lean_raw_loc"], "lean_native_token_loc": end["lean_native_token_loc"],
        "lean_native_token_errors": end["lean_native_token_errors"],
        "native_to_raw_ratio": round(end["lean_native_token_loc"] / end["lean_raw_loc"], 4) if end["lean_raw_loc"] else 0,
        "nonlean_loc": end["nonlean_loc"],
        "lean_gross_added": total_added, "lean_gross_deleted": total_deleted,
        "lean_net": total_added - total_deleted,
        "lean_churn_ratio_deleted_over_added": round(total_deleted / total_added, 4) if total_added else 0,
        "pillars_final_native": {lab: pillar_final[lab] for lab in labels},
        "milestones": [{"time": dt.isoformat(), "label": lab} for dt, lab in milestones],
    }
    with (FIG_DIR / "aoyagi-loc-summary.json").open("w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, sort_keys=True)
        f.write("\n")
    print("[summary]", json.dumps(summary, indent=2))

    os.environ.setdefault("MPLCONFIGDIR", str(Path("/tmp") / "matplotlib-cache"))
    fig_three_metric(rows, milestones, generated, args.bucket_hours, churn)
    fig_pillars(pillar_series, pillar_final, dates, milestones, generated)
    print("[done]")


if __name__ == "__main__":
    main()
