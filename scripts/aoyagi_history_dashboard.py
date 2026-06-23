#!/usr/bin/env python3
"""Generate a static Git-history dashboard for the Aoyagi formalisation paths.

The dashboard is intentionally dependency-free: it reads Git history with
`git log --numstat`, writes JSON/CSV data, and emits a self-contained HTML file
with inline JavaScript/SVG plots.
"""

from __future__ import annotations

import argparse
import csv
import html
import json
import math
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


SEP = "\x1f"
COMMIT_MARKER = "___GHD_COMMIT___"


AOYAGI_LEAN_PREFIXES = (
    "lean/DLNFibre/DLN/Aoyagi/",
    "lean/DLNFibre/DLN/RLCT/",
)

AOYAGI_DOC_PREFIXES = (
    "expeditions/2026-06-18-aoyagi-rlct/",
    "expeditions/2026-06-20-aoyagi-full/",
    "threads/regslice-fm/",
    "paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/",
)

DOC_EXTENSIONS = {
    ".md",
    ".markdown",
    ".yaml",
    ".yml",
    ".txt",
    ".tex",
    ".py",
}

TAG_PATTERNS = {
    "A0": re.compile(r"\bA0\b", re.I),
    "A2": re.compile(r"\bA2\b", re.I),
    "A4": re.compile(r"\bA4\b", re.I),
    "A6": re.compile(r"\bA6\b", re.I),
    "Case2": re.compile(r"case\s*2|case2", re.I),
    "Deepest": re.compile(r"deepest|#44c|#82|gauge|regslice|reg-slice", re.I),
    "R1": re.compile(r"\bR1\b|resolution|atlas", re.I),
    "L2": re.compile(r"\bL2\b|product[_ -]?reduction", re.I),
    "D1": re.compile(r"\bD1\b|monotonicity|deepest-point", re.I),
    "Boundary": re.compile(r"boundary|hypothesis|supplied|certificate|interface", re.I),
    "Docs": re.compile(r"docs?|thread|synthesis|review|reproduction|claim|lesson", re.I),
}

DEBT_GREP_PATTERN = (
    r"sorry|sorryAx|^\s*axiom\s+|^\s*opaque\s+|Boundary|Hypothesis|"
    r"Certificate|Supplied|Extraction|IsResolutionAtlas"
)

DEBT_REGEXES = {
    "body_sorry": re.compile(r"^\s*sorry\b"),
    "sorry_mentions": re.compile(r"\bsorry\b"),
    "sorryAx_mentions": re.compile(r"\bsorryAx\b"),
    "axiom_decls": re.compile(r"^\s*axiom\s+"),
    "opaque_decls": re.compile(r"^\s*opaque\s+"),
    "interface_mentions": re.compile(
        r"Boundary|Hypothesis|Certificate|Supplied|Extraction|IsResolutionAtlas"
    ),
    "interface_decls": re.compile(
        r"^\s*(structure|class|def|theorem|lemma)\s+"
        r"[A-Za-z0-9_']*(Boundary|Hypothesis|Certificate|Supplied|Extraction|Atlas)"
    ),
}


@dataclass
class SeriesSpec:
    key: str
    label: str
    ref_candidates: list[str]
    anchor: str | None
    description: str


DEFAULT_SERIES = [
    SeriesSpec(
        key="repo-head",
        label="Repo HEAD",
        ref_candidates=["HEAD"],
        anchor=None,
        description=(
            "Full current-repository history ending at HEAD. This gives the "
            "background Lean growth of the checked-out repository."
        ),
    ),
    SeriesSpec(
        key="aoyagi-rlct",
        label="Aoyagi RLCT",
        ref_candidates=["origin/expedition/aoyagi-rlct", "expedition/aoyagi-rlct"],
        anchor="9e99e01364b6f3b44d10afd59cc1e6d004cec82c",
        description=(
            "The source-audit and finite-certificate Aoyagi RLCT branch, "
            "anchored at its Aoyagi expedition root."
        ),
    ),
    SeriesSpec(
        key="aoyagi-full-named",
        label="Aoyagi Full Named",
        ref_candidates=["origin/expedition/aoyagi-full", "expedition/aoyagi-full"],
        anchor="e6827ba0cb238dad43c518c7a078064480066a12",
        description=(
            "The named expedition/aoyagi-full branch, anchored at the full-path "
            "root shared with the active side-lineage."
        ),
    ),
    SeriesSpec(
        key="aoyagi-full-active",
        label="Aoyagi Full Active",
        ref_candidates=["fm/regslice-id", "origin/fm/regslice-id"],
        anchor="e6827ba0cb238dad43c518c7a078064480066a12",
        description=(
            "The active full-path side-lineage currently carrying the deepest "
            "gauge/reg-slice work, anchored at the same full-path root."
        ),
    ),
]


def run_git(args: list[str], repo: Path, check: bool = True) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=repo,
        text=True,
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(
            "git {args} failed with code {code}\nSTDERR:\n{stderr}".format(
                args=" ".join(args), code=proc.returncode, stderr=proc.stderr.strip()
            )
        )
    return proc.stdout


def resolve_ref(repo: Path, candidates: Iterable[str]) -> tuple[str, str] | None:
    for candidate in candidates:
        out = run_git(["rev-parse", "--verify", f"{candidate}^{{commit}}"], repo, check=False)
        if out.strip():
            return candidate, out.strip()
    return None


def short_sha(sha: str) -> str:
    return sha[:7]


def is_lean_path(path: str) -> bool:
    return path.startswith("lean/") and path.endswith(".lean")


def is_aoyagi_lean_path(path: str) -> bool:
    return path.endswith(".lean") and path.startswith(AOYAGI_LEAN_PREFIXES)


def is_aoyagi_doc_path(path: str) -> bool:
    if not path.startswith(AOYAGI_DOC_PREFIXES):
        return False
    return Path(path).suffix.lower() in DOC_EXTENSIONS or "." not in Path(path).name


def is_aoyagi_path(path: str) -> bool:
    return is_aoyagi_lean_path(path) or is_aoyagi_doc_path(path)


def normalize_numstat_path(path: str) -> str:
    """Keep Git numstat paths usable enough for filters.

    Git can render renames as `dir/{old => new}.lean`. For filtering, it is
    enough to preserve the string and check for known fragments; exact rename
    accounting is not the goal of this dashboard.
    """

    return path.strip()


def parse_int_stat(value: str) -> int:
    if value == "-":
        return 0
    try:
        return int(value)
    except ValueError:
        return 0


def commit_subject(repo: Path, commit: str) -> dict[str, str]:
    fmt = "%H%x1f%aI%x1f%s"
    out = run_git(["show", "-s", f"--format={fmt}", commit], repo).strip()
    parts = out.split(SEP, 2)
    if len(parts) != 3:
        return {"sha": commit, "date": "", "subject": ""}
    return {"sha": parts[0], "date": parts[1], "subject": parts[2]}


def commit_range_arg(ref: str, anchor: str | None) -> str:
    return f"{anchor}..{ref}" if anchor else ref


def iter_commits_with_numstat(repo: Path, ref: str, anchor: str | None) -> list[dict[str, Any]]:
    fmt = f"{COMMIT_MARKER}{SEP}%H{SEP}%aI{SEP}%s"
    out = run_git(
        [
            "log",
            "--reverse",
            "--numstat",
            f"--format=format:{fmt}",
            commit_range_arg(ref, anchor),
        ],
        repo,
    )

    commits: list[dict[str, Any]] = []
    current: dict[str, Any] | None = None
    for raw_line in out.splitlines():
        line = raw_line.rstrip("\n")
        if line.startswith(COMMIT_MARKER):
            if current is not None:
                commits.append(current)
            _, sha, date, subject = line.split(SEP, 3)
            current = {
                "sha": sha,
                "short": short_sha(sha),
                "date": date,
                "subject": subject,
                "files": [],
            }
            continue
        if current is None or not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) < 3:
            continue
        add = parse_int_stat(parts[0])
        delete = parse_int_stat(parts[1])
        path = normalize_numstat_path(parts[2])
        current["files"].append({"path": path, "add": add, "del": delete})

    if current is not None:
        commits.append(current)
    return commits


def list_files_at(repo: Path, commit: str, prefixes: tuple[str, ...] | None = None) -> list[str]:
    args = ["ls-tree", "-r", "--name-only", commit]
    out = run_git(args, repo, check=False)
    paths = [line.strip() for line in out.splitlines() if line.strip()]
    if prefixes is None:
        return paths
    return [path for path in paths if path.startswith(prefixes)]


def exact_line_count(repo: Path, commit: str, predicate) -> int:
    total = 0
    for path in list_files_at(repo, commit):
        if not predicate(path):
            continue
        blob = run_git(["show", f"{commit}:{path}"], repo, check=False)
        if blob:
            total += len(blob.splitlines())
    return total


def debt_snapshot(repo: Path, commit: str) -> dict[str, int]:
    metrics = {name: 0 for name in DEBT_REGEXES}
    args = [
        "grep",
        "-I",
        "-n",
        "-E",
        DEBT_GREP_PATTERN,
        commit,
        "--",
        *AOYAGI_LEAN_PREFIXES,
    ]
    out = run_git(args, repo, check=False)
    if not out:
        return metrics

    for line in out.splitlines():
        # git grep prints `<commit>:<path>:<line>:<content>`.
        parts = line.split(":", 3)
        if len(parts) == 4:
            content = parts[3]
        else:
            content = line
        for name, regex in DEBT_REGEXES.items():
            if regex.search(content):
                metrics[name] += 1
    return metrics


def classify_tags(subject: str) -> list[str]:
    tags = [tag for tag, regex in TAG_PATTERNS.items() if regex.search(subject)]
    return tags or ["Other"]


def empty_churn_bucket(bucket_count: int) -> list[int]:
    return [0 for _ in range(bucket_count)]


def build_series(repo: Path, spec: SeriesSpec, bucket_count: int, debt_every: int) -> dict[str, Any] | None:
    resolved = resolve_ref(repo, spec.ref_candidates)
    if resolved is None:
        return None

    ref_name, ref_sha = resolved
    anchor = spec.anchor
    anchor_info: dict[str, str] | None = None
    if anchor:
        anchor_resolved = resolve_ref(repo, [anchor])
        if anchor_resolved is None:
            anchor = None
        else:
            anchor = anchor_resolved[1]
            ok = subprocess.run(
                ["git", "merge-base", "--is-ancestor", anchor, ref_sha],
                cwd=repo,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=False,
            ).returncode == 0
            if not ok:
                merge_base = run_git(["merge-base", anchor, ref_sha], repo, check=False).strip()
                anchor = merge_base or None
            if anchor:
                anchor_info = commit_subject(repo, anchor)

    commits = iter_commits_with_numstat(repo, ref_sha, anchor)
    head_info = commit_subject(repo, ref_sha)

    baseline_commit = anchor if anchor else None
    lean_loc = exact_line_count(repo, baseline_commit, is_lean_path) if baseline_commit else 0
    aoyagi_lean_loc = (
        exact_line_count(repo, baseline_commit, is_aoyagi_lean_path) if baseline_commit else 0
    )
    aoyagi_doc_loc = (
        exact_line_count(repo, baseline_commit, is_aoyagi_doc_path) if baseline_commit else 0
    )
    last_debt = debt_snapshot(repo, baseline_commit) if baseline_commit else {name: 0 for name in DEBT_REGEXES}

    file_churn: dict[str, dict[str, Any]] = {}
    tag_counts = {tag: 0 for tag in [*TAG_PATTERNS.keys(), "Other"]}
    total = {
        "lean_add": 0,
        "lean_del": 0,
        "aoyagi_lean_add": 0,
        "aoyagi_lean_del": 0,
        "aoyagi_doc_add": 0,
        "aoyagi_doc_del": 0,
    }
    enriched: list[dict[str, Any]] = []
    n = max(1, len(commits))

    for index, commit in enumerate(commits):
        lean_add = lean_del = 0
        aoyagi_lean_add = aoyagi_lean_del = 0
        aoyagi_doc_add = aoyagi_doc_del = 0
        bucket = min(bucket_count - 1, math.floor(index * bucket_count / n))

        for f in commit["files"]:
            path = f["path"]
            add = f["add"]
            delete = f["del"]
            if is_lean_path(path):
                lean_add += add
                lean_del += delete
            if is_aoyagi_lean_path(path):
                aoyagi_lean_add += add
                aoyagi_lean_del += delete
            if is_aoyagi_doc_path(path):
                aoyagi_doc_add += add
                aoyagi_doc_del += delete
            if is_aoyagi_path(path):
                entry = file_churn.setdefault(
                    path,
                    {"path": path, "add": 0, "del": 0, "buckets": empty_churn_bucket(bucket_count)},
                )
                entry["add"] += add
                entry["del"] += delete
                entry["buckets"][bucket] += add + delete

        lean_loc = max(0, lean_loc + lean_add - lean_del)
        aoyagi_lean_loc = max(0, aoyagi_lean_loc + aoyagi_lean_add - aoyagi_lean_del)
        aoyagi_doc_loc = max(0, aoyagi_doc_loc + aoyagi_doc_add - aoyagi_doc_del)

        if debt_every <= 1 or index % debt_every == 0 or index == len(commits) - 1:
            last_debt = debt_snapshot(repo, commit["sha"])

        tags = classify_tags(commit["subject"])
        for tag in tags:
            tag_counts[tag] = tag_counts.get(tag, 0) + 1

        total["lean_add"] += lean_add
        total["lean_del"] += lean_del
        total["aoyagi_lean_add"] += aoyagi_lean_add
        total["aoyagi_lean_del"] += aoyagi_lean_del
        total["aoyagi_doc_add"] += aoyagi_doc_add
        total["aoyagi_doc_del"] += aoyagi_doc_del

        enriched.append(
            {
                "index": index + 1,
                "sha": commit["sha"],
                "short": commit["short"],
                "date": commit["date"],
                "subject": commit["subject"],
                "lean_add": lean_add,
                "lean_del": lean_del,
                "aoyagi_lean_add": aoyagi_lean_add,
                "aoyagi_lean_del": aoyagi_lean_del,
                "aoyagi_doc_add": aoyagi_doc_add,
                "aoyagi_doc_del": aoyagi_doc_del,
                "lean_loc": lean_loc,
                "aoyagi_lean_loc": aoyagi_lean_loc,
                "aoyagi_doc_loc": aoyagi_doc_loc,
                "debt": dict(last_debt),
                "tags": tags,
            }
        )

    top_files = sorted(
        file_churn.values(), key=lambda row: (row["add"] + row["del"], row["path"]), reverse=True
    )[:35]

    return {
        "key": spec.key,
        "label": spec.label,
        "description": spec.description,
        "ref": ref_name,
        "ref_sha": ref_sha,
        "anchor": anchor,
        "anchor_info": anchor_info,
        "head_info": head_info,
        "commit_count": len(enriched),
        "totals": total,
        "final": enriched[-1] if enriched else {
            "lean_loc": lean_loc,
            "aoyagi_lean_loc": aoyagi_lean_loc,
            "aoyagi_doc_loc": aoyagi_doc_loc,
            "debt": last_debt,
        },
        "commits": enriched,
        "top_files": top_files,
        "tag_counts": tag_counts,
    }


def write_csv(path: Path, data: dict[str, Any]) -> None:
    rows: list[dict[str, Any]] = []
    for series in data["series"]:
        for commit in series["commits"]:
            debt = commit.get("debt", {})
            rows.append(
                {
                    "series": series["key"],
                    "label": series["label"],
                    "index": commit["index"],
                    "sha": commit["sha"],
                    "date": commit["date"],
                    "subject": commit["subject"],
                    "lean_add": commit["lean_add"],
                    "lean_del": commit["lean_del"],
                    "aoyagi_lean_add": commit["aoyagi_lean_add"],
                    "aoyagi_lean_del": commit["aoyagi_lean_del"],
                    "aoyagi_doc_add": commit["aoyagi_doc_add"],
                    "aoyagi_doc_del": commit["aoyagi_doc_del"],
                    "lean_loc": commit["lean_loc"],
                    "aoyagi_lean_loc": commit["aoyagi_lean_loc"],
                    "aoyagi_doc_loc": commit["aoyagi_doc_loc"],
                    "body_sorry": debt.get("body_sorry", 0),
                    "sorry_mentions": debt.get("sorry_mentions", 0),
                    "sorryAx_mentions": debt.get("sorryAx_mentions", 0),
                    "axiom_decls": debt.get("axiom_decls", 0),
                    "opaque_decls": debt.get("opaque_decls", 0),
                    "interface_mentions": debt.get("interface_mentions", 0),
                    "interface_decls": debt.get("interface_decls", 0),
                    "tags": ",".join(commit.get("tags", [])),
                }
            )

    fieldnames = list(rows[0].keys()) if rows else []
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def html_document(data: dict[str, Any]) -> str:
    json_data = json.dumps(data, ensure_ascii=True)
    escaped_json = html.escape(json_data, quote=False)
    runtime_js = r"""
const DATA = JSON.parse(document.getElementById("dashboard-data").textContent);
const COLORS = ["#2f6fbb", "#238b45", "#c77918", "#7b4ab8", "#16817a", "#c43c39"];
const DEBT_LABELS = {
  body_sorry: "body-level sorry lines",
  axiom_decls: "axiom declarations",
  opaque_decls: "opaque declarations",
  sorryAx_mentions: "sorryAx mentions",
  interface_mentions: "interface mentions",
  interface_decls: "interface declarations"
};
const DEBT_COLORS = {
  body_sorry: "#c43c39",
  axiom_decls: "#7b1f1f",
  opaque_decls: "#c77918",
  sorryAx_mentions: "#7b4ab8",
  interface_mentions: "#2f6fbb",
  interface_decls: "#16817a"
};

function esc(s) {
  return String(s ?? "").replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;","\"":"&quot;","'":"&#39;"}[c]));
}

function fmt(n) {
  return Number(n || 0).toLocaleString("en-US");
}

function shortDate(iso) {
  return String(iso || "").slice(0, 10);
}

function metric(c, name) {
  if (name in c) return c[name] || 0;
  return (c.debt || {})[name] || 0;
}

function commitHover(c, valueLabel, value) {
  return [
    `<b>${esc(c.short)}</b>`,
    esc(shortDate(c.date)),
    esc(c.subject),
    `${esc(valueLabel)}: ${fmt(value)}`
  ].join("<br>");
}

function plotConfig() {
  return {
    responsive: true,
    displaylogo: false,
    modeBarButtonsToRemove: ["lasso2d", "select2d"]
  };
}

function baseLayout(title, yTitle, height = 420) {
  return {
    title: {text: title, x: 0, xanchor: "left", font: {size: 16}},
    height,
    margin: {l: 62, r: 32, t: 52, b: 54},
    paper_bgcolor: "#ffffff",
    plot_bgcolor: "#ffffff",
    hovermode: "x unified",
    legend: {orientation: "h", x: 0, y: -0.2},
    xaxis: {
      title: "Commit number from anchor",
      gridcolor: "#eef2f6",
      zerolinecolor: "#d7dde5"
    },
    yaxis: {
      title: yTitle,
      gridcolor: "#eef2f6",
      zerolinecolor: "#d7dde5",
      rangemode: "tozero"
    },
    font: {family: "system-ui, -apple-system, BlinkMacSystemFont, Segoe UI, sans-serif", color: "#17202a"}
  };
}

function ensurePlotly(targetId) {
  if (window.Plotly) return true;
  const el = document.getElementById(targetId);
  if (el) {
    el.innerHTML = `<div class="plot-fallback">Plotly did not load. The tables and raw JSON/CSV are still available; open this file with network access or vendor Plotly locally for interactive plots.</div>`;
  }
  return false;
}

function sectionShell(id, title, explanation, caveat, plotId) {
  document.getElementById(id).innerHTML = `
    <div class="section-head">
      <div>
        <h2>${esc(title)}</h2>
        <p>${esc(explanation)}</p>
      </div>
    </div>
    ${caveat ? `<p class="note">${caveat}</p>` : ""}
    ${plotId ? `<div id="${plotId}" class="plot"></div>` : ""}`;
}

function renderAnchors() {
  const rows = DATA.series.map((s, i) => `
    <tr>
      <td><span class="series-dot" style="background:${COLORS[i % COLORS.length]}"></span><strong>${esc(s.label)}</strong><br><span class="small">${esc(s.description)}</span></td>
      <td><code>${esc(s.ref)}</code><br><code>${esc((s.ref_sha || "").slice(0, 12))}</code></td>
      <td>${s.anchor ? `<code>${esc(s.anchor.slice(0, 12))}</code><br><span class="small">${esc(s.anchor_info?.subject || "")}</span>` : `<span class="small">Repository root history</span>`}</td>
      <td>${fmt(s.commit_count)}</td>
    </tr>`).join("");
  document.getElementById("anchors").innerHTML = `
    <div class="section-head">
      <div>
        <h2>Scope And Anchors</h2>
        <p>This table fixes the comparison frame. The full-path series are anchored at the full expedition root; the RLCT series is anchored at its own Aoyagi expedition root.</p>
      </div>
      <div class="data-links">
        <a href="history.json">history.json</a>
        <a href="history.csv">history.csv</a>
      </div>
    </div>
    <p class="note warn">The active full work is shown separately from the named full branch because the implementation movement is on the side-lineage, not only on <code>origin/expedition/aoyagi-full</code>.</p>
    <table><thead><tr><th>Series</th><th>Ref</th><th>Anchor</th><th>Commits Since Anchor</th></tr></thead><tbody>${rows}</tbody></table>`;
}

function renderOverview() {
  const cards = DATA.series.map((s, i) => {
    const f = s.final || {};
    const d = f.debt || {};
    const leanNet = (s.totals.aoyagi_lean_add || 0) - (s.totals.aoyagi_lean_del || 0);
    return `<div class="card kpi-card">
      <div class="kpi-top"><span class="series-dot" style="background:${COLORS[i % COLORS.length]}"></span><h3>${esc(s.label)}</h3></div>
      <div class="metric">${fmt(f.aoyagi_lean_loc || 0)}</div>
      <div class="small">Aoyagi Lean LoC at tip</div>
      <div class="kpi-grid">
        <div><b>${fmt(s.commit_count)}</b><span>commits</span></div>
        <div><b>${leanNet >= 0 ? "+" : ""}${fmt(leanNet)}</b><span>net Aoyagi Lean</span></div>
        <div><b>${fmt(d.body_sorry || 0)}</b><span>body sorry</span></div>
        <div><b>${fmt(d.interface_decls || 0)}</b><span>interface decls</span></div>
      </div>
      <div class="small">Head <code>${esc((s.ref_sha || "").slice(0, 10))}</code> · ${esc(shortDate(s.head_info?.date))}</div>
    </div>`;
  }).join("");
  document.getElementById("overview").innerHTML = `
    <h2>Overview</h2>
    <p>These cards summarize branch tips and keep Aoyagi-scoped Lean separate from the rest of the repository.</p>
    <div class="grid kpi-wrap">${cards}</div>`;
}

function seriesLineTrace(s, si, metricName, label) {
  const x = s.commits.map(c => c.index);
  const y = s.commits.map(c => metric(c, metricName));
  return {
    type: "scatter",
    mode: "lines+markers",
    name: s.label,
    x, y,
    marker: {size: 4, color: COLORS[si % COLORS.length]},
    line: {width: 2.4, color: COLORS[si % COLORS.length]},
    text: s.commits.map((c, idx) => commitHover(c, label, y[idx])),
    hovertemplate: "%{text}<extra></extra>"
  };
}

function renderLinePlot(sectionId, plotId, title, metricName, label, explanation, caveat) {
  sectionShell(sectionId, title, explanation, caveat, plotId);
  if (!ensurePlotly(plotId)) return;
  const traces = DATA.series.map((s, i) => seriesLineTrace(s, i, metricName, label));
  Plotly.newPlot(plotId, traces, baseLayout(title, label), plotConfig());
}

function renderDocsPlot() {
  renderLinePlot(
    "loc-docs",
    "plot-docs",
    "Aoyagi Documentation LoC Over Time",
    "aoyagi_doc_loc",
    "Aoyagi docs LoC",
    "This tracks Aoyagi expedition notes, source-audit notes, and reg-slice thread notes. It shows research/documentation movement separately from Lean movement.",
    "Documentation LoC is a research-log proxy. Large increases often correspond to audits, failed routes, or statement cards, not only exposition polish."
  );
}

function renderChurn() {
  document.getElementById("churn").innerHTML = `
    <h2>Stock-Style Aoyagi Lean Churn</h2>
    <p>Each mini-plot shows Lean insertions as green bars, deletions as red bars, and cumulative Aoyagi Lean LoC as a blue line. Hover points show commit SHA, date, subject, and values.</p>
    <p class="note">High churn is not bad by itself. In these branches, churn spikes often mark boundary redesigns, source audits, or deep coordinate refactors.</p>
    <div class="grid two-col">${DATA.series.map(s => `<div class="card"><h3>${esc(s.label)}</h3><div id="plot-churn-${esc(s.key)}" class="plot small-plot"></div></div>`).join("")}</div>`;
  DATA.series.forEach(s => {
    const id = `plot-churn-${s.key}`;
    if (!ensurePlotly(id)) return;
    const x = s.commits.map(c => c.index);
    const add = s.commits.map(c => c.aoyagi_lean_add || 0);
    const del = s.commits.map(c => -(c.aoyagi_lean_del || 0));
    const loc = s.commits.map(c => c.aoyagi_lean_loc || 0);
    const common = s.commits.map(c => `${esc(c.short)}<br>${esc(shortDate(c.date))}<br>${esc(c.subject)}`);
    const traces = [
      {
        type: "bar",
        name: "insertions",
        x, y: add,
        marker: {color: "#238b45"},
        text: common.map((h, i) => `${h}<br>insertions: ${fmt(add[i])}`),
        hovertemplate: "%{text}<extra></extra>"
      },
      {
        type: "bar",
        name: "deletions",
        x, y: del,
        marker: {color: "#c43c39"},
        text: common.map((h, i) => `${h}<br>deletions: ${fmt(Math.abs(del[i]))}`),
        hovertemplate: "%{text}<extra></extra>"
      },
      {
        type: "scatter",
        mode: "lines",
        name: "cumulative LoC",
        x, y: loc,
        yaxis: "y2",
        line: {color: "#2f6fbb", width: 2.5},
        text: common.map((h, i) => `${h}<br>Aoyagi Lean LoC: ${fmt(loc[i])}`),
        hovertemplate: "%{text}<extra></extra>"
      }
    ];
    const layout = baseLayout(`${s.label}: Aoyagi Lean churn`, "insertions / deletions", 330);
    layout.barmode = "relative";
    layout.legend = {orientation: "h", x: 0, y: -0.28};
    layout.yaxis2 = {
      title: "cumulative LoC",
      overlaying: "y",
      side: "right",
      showgrid: false,
      rangemode: "tozero"
    };
    Plotly.newPlot(id, traces, layout, plotConfig());
  });
}

function renderDebt() {
  document.getElementById("debt").innerHTML = `
    <h2>Proof-Obligation Surface</h2>
    <p>This is a proxy view, not a proof graph. It tracks textual signals that a headline theorem still relies on unproved or supplied mathematics.</p>
    <p class="note warn">The useful signal is composition. Moving work from <code>sorry</code> into a named <code>Boundary</code> can be real progress if the boundary is mathematically correct and explicit.</p>
    <div id="plot-debt" class="plot"></div>`;
  if (!ensurePlotly("plot-debt")) return;
  const metrics = ["body_sorry", "axiom_decls", "opaque_decls", "sorryAx_mentions", "interface_decls", "interface_mentions"];
  const traces = [];
  DATA.series.forEach((s, si) => {
    metrics.forEach(m => {
      const y = s.commits.map(c => (c.debt || {})[m] || 0);
      traces.push({
        type: "scatter",
        mode: "lines",
        name: `${s.label}: ${DEBT_LABELS[m]}`,
        legendgroup: s.key,
        visible: m === "interface_mentions" ? "legendonly" : true,
        x: s.commits.map(c => c.index),
        y,
        line: {width: 2, color: DEBT_COLORS[m], dash: si === 0 ? "solid" : si === 1 ? "dot" : si === 2 ? "dash" : "longdash"},
        text: s.commits.map((c, idx) => commitHover(c, DEBT_LABELS[m], y[idx])),
        hovertemplate: "%{text}<extra></extra>"
      });
    });
  });
  const layout = baseLayout("Proof-obligation proxy metrics", "count", 520);
  layout.hovermode = "closest";
  layout.legend = {orientation: "v", x: 1.02, y: 1, xanchor: "left"};
  layout.margin.r = 260;
  Plotly.newPlot("plot-debt", traces, layout, plotConfig());
}

function renderInterfaces() {
  const rows = DATA.series.map(s => {
    const d = (s.final || {}).debt || {};
    return `<tr>
      <td><strong>${esc(s.label)}</strong></td>
      <td>${fmt(d.interface_mentions || 0)}</td>
      <td>${fmt(d.interface_decls || 0)}</td>
      <td>${fmt(d.body_sorry || 0)}</td>
      <td>${fmt(d.axiom_decls || 0)}</td>
      <td>${fmt(d.opaque_decls || 0)}</td>
    </tr>`;
  }).join("");
  document.getElementById("interfaces").innerHTML = `
    <div class="section-head">
      <div>
        <h2>Current Conditional Surface</h2>
        <p>This table and bar chart separate conditional architecture from direct holes.</p>
      </div>
    </div>
    <table><thead><tr><th>Series</th><th>Interface Mentions</th><th>Interface Decls</th><th>Body Sorry</th><th>Axiom Decls</th><th>Opaque Decls</th></tr></thead><tbody>${rows}</tbody></table>
    <div id="plot-current-surface" class="plot compact-plot"></div>`;
  if (!ensurePlotly("plot-current-surface")) return;
  const labels = Object.values(DEBT_LABELS);
  const keys = Object.keys(DEBT_LABELS);
  const traces = DATA.series.map((s, i) => {
    const d = (s.final || {}).debt || {};
    return {
      type: "bar",
      name: s.label,
      x: labels,
      y: keys.map(k => d[k] || 0),
      marker: {color: COLORS[i % COLORS.length]},
      hovertemplate: `<b>${esc(s.label)}</b><br>%{x}: %{y:,}<extra></extra>`
    };
  });
  const layout = baseLayout("Tip-level proof-obligation proxy counts", "count", 360);
  layout.barmode = "group";
  layout.xaxis.tickangle = -20;
  Plotly.newPlot("plot-current-surface", traces, layout, plotConfig());
}

function renderHeatmap() {
  document.getElementById("heatmap").innerHTML = `
    <h2>Aoyagi File Churn Heatmap</h2>
    <p>Rows are the most-churned Aoyagi files. Columns are equal-sized commit buckets from anchor to tip. Hover a cell to see the churn count.</p>
    <p class="note">Heat is additions plus deletions. A hot file can mean proof progress, refactoring, or repeated redesign; inspect the file and commits before assigning mathematical meaning.</p>
    <div class="grid two-col">${DATA.series.filter(s => (s.top_files || []).length).map(s => `<div class="card"><h3>${esc(s.label)}</h3><div id="plot-heat-${esc(s.key)}" class="plot heat-plot"></div></div>`).join("")}</div>`;
  DATA.series.filter(s => (s.top_files || []).length).forEach(s => {
    const id = `plot-heat-${s.key}`;
    if (!ensurePlotly(id)) return;
    const files = (s.top_files || []).slice(0, 26);
    const bucketCount = files[0]?.buckets?.length || 1;
    const x = Array.from({length: bucketCount}, (_, i) => `bucket ${i + 1}`);
    const y = files.map(f => f.path.length > 70 ? "..." + f.path.slice(-67) : f.path);
    const z = files.map(f => f.buckets || []);
    const customdata = files.map(f => Array.from({length: bucketCount}, () => f.path));
    const trace = {
      type: "heatmap",
      x, y, z,
      customdata,
      colorscale: [[0, "#f4f6f8"], [0.35, "#bfd7ee"], [0.7, "#5f99cf"], [1, "#184f90"]],
      colorbar: {title: "churn"},
      hovertemplate: "<b>%{customdata}</b><br>%{x}<br>churn: %{z:,}<extra></extra>"
    };
    const layout = baseLayout(`${s.label}: file churn`, "file", 620);
    layout.margin.l = 280;
    layout.xaxis.title = "commit bucket";
    layout.yaxis.autorange = "reversed";
    Plotly.newPlot(id, [trace], layout, plotConfig());
  });
}

function renderTags() {
  document.getElementById("tags").innerHTML = `
    <h2>Commit Message Lanes</h2>
    <p>This groups commit subjects by recurring Aoyagi work lanes: Case 2, A0/A2/A4/A6, R1/L2/D1, deepest gauge work, and interface/boundary work.</p>
    <p class="note">This is only as good as commit-message discipline. It is useful for navigation, not for proof status.</p>
    <div id="plot-tags" class="plot"></div>`;
  if (!ensurePlotly("plot-tags")) return;
  const tags = Array.from(new Set(DATA.series.flatMap(s => Object.keys(s.tag_counts || {})))).filter(tag =>
    DATA.series.some(s => (s.tag_counts || {})[tag] > 0)
  );
  const traces = DATA.series.map((s, i) => ({
    type: "bar",
    name: s.label,
    x: tags,
    y: tags.map(tag => (s.tag_counts || {})[tag] || 0),
    marker: {color: COLORS[i % COLORS.length]},
    hovertemplate: `<b>${esc(s.label)}</b><br>%{x}: %{y:,} commits<extra></extra>`
  }));
  const layout = baseLayout("Commit-message lane counts", "commits", 430);
  layout.barmode = "group";
  Plotly.newPlot("plot-tags", traces, layout, plotConfig());
}

function renderRecent() {
  const blocks = DATA.series.map(s => {
    const rows = s.commits.slice(-8).reverse().map(c => `
      <tr><td><code>${esc(c.short)}</code></td><td>${esc(shortDate(c.date))}</td><td>${esc(c.subject)}</td></tr>`).join("");
    return `<div class="card"><h3>${esc(s.label)}</h3><table><tbody>${rows}</tbody></table></div>`;
  }).join("");
  document.getElementById("recent").innerHTML = `
    <h2>Recent Commits</h2>
    <p>The final panel gives a quick route from a plotted movement back to the commits that caused it.</p>
    <div class="grid two-col">${blocks}</div>`;
}

function renderAll() {
  renderAnchors();
  renderOverview();
  renderLinePlot(
    "loc-all",
    "plot-loc-all",
    "Repository Lean LoC Over Time",
    "lean_loc",
    "Repository Lean LoC",
    "This line chart tracks cumulative Lean lines for each series using numstat deltas from the chosen anchor.",
    "For branch-local series, the starting point includes the anchor snapshot; the plotted movement is the branch history after that anchor."
  );
  renderLinePlot(
    "loc-aoyagi",
    "plot-loc-aoyagi",
    "Aoyagi Lean LoC Over Time",
    "aoyagi_lean_loc",
    "Aoyagi Lean LoC",
    "This filters Lean files to the Aoyagi namespaces only: DLNFibre.DLN.Aoyagi and DLNFibre.DLN.RLCT.",
    "This is the main LoC plot for this investigation because the repo contains other formalisation work."
  );
  renderDocsPlot();
  renderChurn();
  renderDebt();
  renderInterfaces();
  renderHeatmap();
  renderTags();
  renderRecent();
}

renderAll();
"""
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Aoyagi Git History Dashboard</title>
<script src="https://cdn.plot.ly/plotly-2.35.2.min.js"></script>
<style>
:root {{
  --bg: #f4f6f8;
  --panel: #ffffff;
  --ink: #17202a;
  --muted: #617080;
  --line: #d7dde5;
  --green: #238b45;
  --red: #c43c39;
  --blue: #2768b7;
  --orange: #c77918;
  --purple: #7b4ab8;
  --teal: #16817a;
}}
* {{ box-sizing: border-box; }}
body {{
  margin: 0;
  background: var(--bg);
  color: var(--ink);
  font: 14px/1.45 system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
}}
header {{
  padding: 30px 32px 20px;
  border-bottom: 1px solid var(--line);
  background: linear-gradient(180deg, #ffffff 0%, #f8fafc 100%);
}}
h1 {{ margin: 0 0 8px; font-size: 28px; letter-spacing: 0; }}
h2 {{ margin: 0 0 8px; font-size: 20px; letter-spacing: 0; }}
h3 {{ margin: 0 0 6px; font-size: 15px; letter-spacing: 0; }}
p {{ margin: 6px 0 10px; color: var(--muted); max-width: 980px; }}
main {{ padding: 20px 24px 44px; }}
section {{
  background: var(--panel);
  border: 1px solid var(--line);
  border-radius: 8px;
  padding: 18px;
  margin: 0 0 18px;
  box-shadow: 0 1px 2px rgba(20, 28, 36, 0.04);
}}
.section-head {{ display: flex; align-items: flex-start; justify-content: space-between; gap: 16px; }}
.grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(260px, 1fr)); gap: 12px; }}
.two-col {{ grid-template-columns: repeat(auto-fit, minmax(440px, 1fr)); }}
.card {{
  border: 1px solid var(--line);
  border-radius: 8px;
  padding: 12px;
  background: #fbfcfe;
}}
.kpi-card {{ min-height: 178px; }}
.kpi-top {{ display: flex; align-items: center; gap: 8px; }}
.kpi-top h3 {{ margin: 0; }}
.kpi-grid {{ display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 8px; margin: 12px 0; }}
.kpi-grid div {{ border-top: 1px solid var(--line); padding-top: 7px; }}
.kpi-grid b {{ display: block; font-size: 15px; }}
.kpi-grid span {{ color: var(--muted); font-size: 11px; }}
.metric {{ font-size: 24px; font-weight: 700; margin-top: 4px; }}
.small {{ font-size: 12px; color: var(--muted); }}
.plot {{ width: 100%; min-height: 420px; margin-top: 10px; }}
.small-plot {{ min-height: 330px; }}
.compact-plot {{ min-height: 360px; }}
.heat-plot {{ min-height: 620px; }}
.plot-fallback {{ border: 1px dashed var(--line); border-radius: 8px; padding: 16px; color: var(--muted); background: #fbfcfe; }}
table {{ border-collapse: collapse; width: 100%; margin-top: 10px; }}
th, td {{ border-bottom: 1px solid var(--line); padding: 7px 8px; text-align: left; vertical-align: top; }}
th {{ font-size: 12px; color: #415163; background: #f1f4f7; }}
code {{ font: 12px/1.4 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }}
.series-dot {{ display: inline-block; width: 10px; height: 10px; border-radius: 50%; margin-right: 5px; vertical-align: 0; }}
.data-links {{ display: flex; gap: 8px; align-items: center; flex-wrap: wrap; }}
.data-links a {{ display: inline-block; border: 1px solid var(--line); border-radius: 999px; padding: 5px 10px; color: var(--ink); text-decoration: none; background: #ffffff; font-size: 12px; }}
.data-links a:hover {{ border-color: var(--blue); color: var(--blue); }}
.note {{ border-left: 3px solid var(--blue); padding-left: 10px; color: var(--muted); }}
.warn {{ border-left-color: var(--orange); }}
@media (max-width: 720px) {{
  header {{ padding: 22px 18px 16px; }}
  main {{ padding: 14px; }}
  .section-head {{ display: block; }}
  .two-col {{ grid-template-columns: 1fr; }}
}}
</style>
</head>
<body>
<header>
  <h1>Aoyagi Git History Dashboard</h1>
  <p>Generated from local Git history. The interactive plots compare repository-wide Lean growth with the Aoyagi RLCT and full-path branches using branch-specific anchors.</p>
  <p class="small">Plotly powers hover labels, zooming, pan, image export, and legend toggles. If the CDN is unavailable, the raw JSON/CSV artifacts remain usable.</p>
  <p class="small">Generated at {html.escape(data["generated_at"])} from repository <code>{html.escape(data["repo"])}</code>.</p>
</header>
<main>
  <section id="anchors"></section>
  <section id="overview"></section>
  <section id="loc-all"></section>
  <section id="loc-aoyagi"></section>
  <section id="loc-docs"></section>
  <section id="churn"></section>
  <section id="debt"></section>
  <section id="interfaces"></section>
  <section id="heatmap"></section>
  <section id="tags"></section>
  <section id="recent"></section>
</main>
<script id="dashboard-data" type="application/json">{escaped_json}</script>
<script>{runtime_js}</script>
</body>
</html>
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path.cwd(),
        help="Repository root or any directory inside it.",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("artifacts/git-history"),
        help="Output directory for index.html, history.json, and history.csv.",
    )
    parser.add_argument(
        "--debt-every",
        type=int,
        default=1,
        help="Compute proof-obligation snapshots every N commits; final commit is always computed.",
    )
    parser.add_argument(
        "--buckets",
        type=int,
        default=40,
        help="Number of commit buckets for the file-churn heatmap.",
    )
    args = parser.parse_args()

    repo = Path(run_git(["rev-parse", "--show-toplevel"], args.repo).strip())
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    generated_at = run_git(["show", "-s", "--format=%cI", "HEAD"], repo).strip()
    series: list[dict[str, Any]] = []
    skipped: list[str] = []
    for spec in DEFAULT_SERIES:
        built = build_series(repo, spec, bucket_count=max(4, args.buckets), debt_every=max(1, args.debt_every))
        if built is None:
            skipped.append(spec.key)
        else:
            series.append(built)

    data = {
        "repo": str(repo),
        "generated_at": generated_at,
        "series": series,
        "skipped": skipped,
        "notes": [
            "Proof-obligation metrics are textual proxies, not semantic proof graphs.",
            "Aoyagi Lean scope is restricted to lean/DLNFibre/DLN/Aoyagi and lean/DLNFibre/DLN/RLCT.",
            "Aoyagi docs scope is restricted to the two Aoyagi expeditions, regslice thread notes, and the Aoyagi paper-source directory.",
        ],
    }

    json_path = out_dir / "history.json"
    csv_path = out_dir / "history.csv"
    html_path = out_dir / "index.html"
    json_path.write_text(json.dumps(data, indent=2, ensure_ascii=True), encoding="utf-8")
    write_csv(csv_path, data)
    html_path.write_text(html_document(data), encoding="utf-8")

    print(f"Wrote {html_path}")
    print(f"Wrote {json_path}")
    print(f"Wrote {csv_path}")
    if skipped:
        print("Skipped missing series: " + ", ".join(skipped))


if __name__ == "__main__":
    main()
