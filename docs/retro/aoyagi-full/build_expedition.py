#!/usr/bin/env python3
"""Build the expedition-chronicle figures from the combed log data (data/*.json).

Outputs (next to this script):
  aoyagi-timeline.png        — the annotated swimlane timeline (the hero figure)
  aoyagi-thread-dag.png      — the dialectic graph (graphviz dot)
  aoyagi-summary-charts.png  — claims-by-status, decorrelation catches-by-channel, concepts-by-pillar
Data provenance: docs/diagnostic-figures/data/{process,claims,decorrelation,routes_concepts,lessons}.json,
extracted by five decorrelated log-combing agents over the expedition record + git.
"""
from __future__ import annotations
import json, re, subprocess
from datetime import datetime, timezone, timedelta
from pathlib import Path

FIG = Path(__file__).resolve().parent
DATA = FIG / "data"
load = lambda n: json.load(open(DATA / n))
proc, claims, dec, rc, les = (load(f) for f in
    ["process.json", "claims.json", "decorrelation.json", "routes_concepts.json", "lessons.json"])

def T(s: str) -> datetime:
    return datetime.fromisoformat(s.replace("Z", "+00:00"))

T0 = T("2026-06-20T14:36:08+00:00")
MILESTONES = [
    ("2026-06-28T10:56:47+00:00", "carve triply-certified"),
    ("2026-07-08T16:26:22+00:00", "L=2 headline DONE"),
    ("2026-07-10T15:18:41+00:00", "(□) recalibration"),
    ("2026-07-10T19:16:04+00:00", "atom fork #97"),
    ("2026-07-11T10:13:11+00:00", "§5 lane (operator)"),
    ("2026-07-11T19:16:38+00:00", "DecoratedDescent re-point"),
    ("2026-07-12T08:39:35+00:00", "minAdm=cCodim ∀widths"),
]
PILLAR_ORDER = ["Recon", "Value", "L2", "D1", "R1-Upper", "SJ-Descent", "Headline"]
PCOL = {"Recon": "#94a3b8", "Value": "#ca8a04", "L2": "#2563eb", "D1": "#16a34a",
        "R1-Upper": "#7c3aed", "SJ-Descent": "#dc2626", "Headline": "#ea580c", "ops": "#334155"}


def hours(dt):  # hours from base
    return (dt - T0).total_seconds() / 3600.0


def add_hours_axis(ax):
    import matplotlib.dates as mdates
    x0 = mdates.date2num(T0)
    sec = ax.secondary_xaxis("top", functions=(lambda x: (x - x0) * 24.0,
                                               lambda h: x0 + h / 24.0))
    sec.set_xlabel("hours from base (scaffold)", fontsize=9)
    return sec


# ---- thread lane assignment -------------------------------------------------
def lanes():
    ts = [t for t in proc["threads"] if T(t["first_iso"]) >= T0]  # drop pre-launch (other-branch) threads
    def key(t):
        p = t["pillar_fed"]
        pi = PILLAR_ORDER.index(p) if p in PILLAR_ORDER else len(PILLAR_ORDER)
        return (pi, T(t["first_iso"]))
    ts.sort(key=key)
    y = {t["thread"]: i for i, t in enumerate(ts)}
    return ts, y

THREADS, THREAD_Y = lanes()
IDS = list(THREAD_Y)

def match_lane(threadstr):
    if not threadstr:
        return None
    s = str(threadstr)
    for tok in re.findall(r"\d{2}[a-z0-9-]*|[a-z][a-z0-9-]{3,}", s):
        if tok in THREAD_Y:
            return THREAD_Y[tok]
        for k in IDS:
            if k == tok or k.startswith(tok + "-") or k.startswith(tok):
                return THREAD_Y[k]
    return None


# ---- FIGURE 1: timeline -----------------------------------------------------
def fig_timeline():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.dates as mdates
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    from matplotlib.patches import Patch

    n = len(THREADS)
    fig, (ax, axa) = plt.subplots(2, 1, figsize=(20, 22),
                                  gridspec_kw={"height_ratios": [6.2, 1.0], "hspace": 0.16},
                                  sharex=True)

    # Codex-outage shaded span
    co = dec["codex_outage"]
    try:
        ax.axvspan(T(co["broke_iso"]), T(co["restored_iso"]), color="#f59e0b", alpha=0.07, zorder=0)
        ax.text(T(co["broke_iso"]), n - 0.2, "  Codex CLI down (decorrelation via independent seats)",
                fontsize=8, color="#b45309", va="top")
    except Exception:
        pass

    # thread lanes (bars) + labels
    for t in THREADS:
        y = THREAD_Y[t["thread"]]
        a, b = T(t["first_iso"]), T(t["last_iso"])
        w = max((b - a).total_seconds() / 86400.0, 0.006)  # min visible width (days)
        c = PCOL.get(t["pillar_fed"], "#64748b")
        ax.barh(y, w, left=mdates.date2num(a), height=0.62, color=c, alpha=0.80,
                edgecolor="white", linewidth=0.5, zorder=2)
    def _sid(t):
        p = t.split("-")
        return (p[0] + (p[1][:2] if len(p) > 1 and not p[1].isdigit() else "")) if p[0].isdigit() else t[:6]
    ax.set_yticks(range(n))
    ax.set_yticklabels([f"{_sid(t['thread'])}  {t['title'][:26]}" for t in THREADS], fontsize=7.4)
    ax.set_ylim(-0.6, n + 1.4)
    ax.invert_yaxis()

    # milestones (vertical lines across both panels)
    for iso, lab in MILESTONES:
        for a_ in (ax, axa):
            a_.axvline(T(iso), color="#b45309", ls=":", lw=1.0, alpha=0.7, zorder=1)
        ax.text(T(iso), -0.5, " " + lab, rotation=90, va="bottom", ha="left",
                fontsize=7.6, color="#b45309", zorder=5)

    # event markers
    def scatter(dt, y, marker, color, size, z=6, ec="white"):
        ax.scatter(mdates.date2num(dt), y, marker=marker, s=size, color=color,
                   edgecolors=ec, linewidths=0.5, zorder=z)

    STAT = {"refuted": ("X", "#dc2626"), "retracted": ("X", "#991b1b"),
            "corrected": ("o", "#ea580c"), "confirmed": ("^", "#16a34a")}
    for c in claims["claims_lifecycle"]:
        y = match_lane(c.get("thread"))
        if y is None:
            y = n + 0.9  # unattributed row (bottom)
        m, col = STAT.get(c["status"], ("s", "#64748b"))
        try:
            scatter(T(c["approx_iso_time"]), y, m, col, 62)
        except Exception:
            pass

    CHANCOL = {"codex": "#7c3aed", "pen-and-paper": "#2563eb", "reviewer": "#0891b2"}
    for k in dec["catches"]:
        y = match_lane(k.get("thread"))
        if y is None:
            y = n + 0.9
        try:
            scatter(T(k["iso_time"]), y + 0.0, "D", CHANCOL.get(k["channel"], "#2563eb"), 42, z=7)
        except Exception:
            pass

    # coordination failures on the ops row (y = -1.8)
    for e in proc["coordination_events"]:
        try:
            scatter(T(e["iso_time"]), n + 0.3, "v", "#334155", 55, z=6)
        except Exception:
            pass
    ax.text(mdates.date2num(T0), n + 0.3, "ops/coord  ", fontsize=7.2, color="#334155",
            va="center", ha="right")
    ax.text(mdates.date2num(T0), n + 0.9, "unattributed  ", fontsize=7.0, color="#64748b",
            va="center", ha="right")

    ax.grid(True, axis="x", color="#e5e7eb", lw=0.7, alpha=0.7)
    add_hours_axis(ax)

    # legend
    leg = [
        Line2D([0], [0], marker="X", color="w", markerfacecolor="#dc2626", markersize=10, label="refuted / retracted claim"),
        Line2D([0], [0], marker="o", color="w", markerfacecolor="#ea580c", markersize=9, label="corrected claim"),
        Line2D([0], [0], marker="^", color="w", markerfacecolor="#16a34a", markersize=9, label="confirmed claim"),
        Line2D([0], [0], marker="D", color="w", markerfacecolor="#2563eb", markersize=8, label="decorrelation catch (pen-and-paper)"),
        Line2D([0], [0], marker="D", color="w", markerfacecolor="#7c3aed", markersize=8, label="decorrelation catch (Codex)"),
        Line2D([0], [0], marker="D", color="w", markerfacecolor="#0891b2", markersize=8, label="decorrelation catch (reviewer)"),
        Line2D([0], [0], marker="v", color="w", markerfacecolor="#334155", markersize=9, label="coordination failure"),
    ] + [Patch(facecolor=PCOL[p], alpha=0.8, label=f"thread pillar: {p}") for p in PILLAR_ORDER]
    ax.legend(handles=leg, loc="upper right", fontsize=7.6, framealpha=0.95, ncol=2)

    # activity strip: commits/hour stacked by kind
    KCOL = {"feat": "#16a34a", "fix": "#ea580c", "refactor": "#2563eb", "docs": "#94a3b8", "other": "#d6bcfa"}
    def kind_of(a):
        s = a.get("subject", "").lower()
        if s.startswith(("fix", "revert")) or "refuted" in s or "retract" in s:
            return "fix"
        if s.startswith("refactor"):
            return "refactor"
        if any(s.startswith(w) for w in ("feat", "land", "wire", "bank")):
            return "feat"
        if any(w in s for w in ("docs", "synthesis", "lessons", "expedition(", "readme", "roadmap", "record", "flush")):
            return "docs"
        return "other"
    acts = proc["activity"]
    end = max(T(a["iso_time"]) for a in acts)
    nb = int(hours(end)) + 2
    buckets = {k: [0] * nb for k in KCOL}
    for a in acts:
        b = int(hours(T(a["iso_time"])))
        if 0 <= b < nb:
            buckets[kind_of(a)][b] += 1
    xs = [mdates.date2num(T0 + timedelta(hours=i + 0.5)) for i in range(nb)]
    bottom = [0] * nb
    wid = 1 / 24 * 0.9
    for k in ["feat", "fix", "refactor", "docs", "other"]:
        axa.bar(xs, buckets[k], width=wid, bottom=bottom, color=KCOL[k], label=k, alpha=0.9)
        bottom = [bottom[i] + buckets[k][i] for i in range(nb)]
    axa.set_ylabel("commits / h", fontsize=9)
    axa.set_title("commit activity per hour (by kind)", fontsize=10, loc="left")
    axa.grid(True, axis="y", color="#e5e7eb", lw=0.7, alpha=0.7)
    axa.legend(loc="upper right", fontsize=7.5, ncol=5, framealpha=0.9)
    axa.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d\n%H:%M", tz=timezone.utc))

    fig.suptitle("aoyagi-full formalisation expedition — mid-flight day 22: launch → DecoratedDescent endgame",
                 fontsize=16, fontweight="bold", y=0.995)
    fig.text(0.012, 0.008, "Thread bars from git (first/last commit touching each thread dir). Event times "
             "best-effort, anchored to the recording commit. Data: docs/diagnostic-figures/data/*.json "
             "(5 decorrelated log-combers). Bottom x-axis = wall-clock; top = hours from base.",
             fontsize=8, color="#334155")
    fig.subplots_adjust(left=0.16, right=0.995, top=0.925, bottom=0.055, hspace=0.16)
    out = FIG / "aoyagi-timeline.png"
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print("[fig]", out)


# ---- FIGURE 2: dialectic DAG (graphviz) -------------------------------------
def fig_dag():
    REL = {"refutes": ("#dc2626", "2.0", "bold"), "corrects": ("#ea580c", "1.6", "bold"),
           "supersedes": ("#7c3aed", "1.6", "bold"), "feeds": ("#cbd5e1", "0.8", "solid"), "audits": ("#0891b2", "1.4", "dashed")}
    title_by = {t["thread"]: t for t in proc["threads"]}
    dot = ['digraph G {', 'rankdir=LR; bgcolor="white"; splines=true; nodesep=0.25; ranksep=0.7;',
           'node [shape=box style="rounded,filled" fontname="Helvetica" fontsize=10 penwidth=0];']
    seen = set()
    for e in proc["edges"]:
        seen.add(e["from"]); seen.add(e["to"])
    for tid in seen:
        t = title_by.get(tid, {"title": tid, "pillar_fed": "Recon"})
        col = PCOL.get(t.get("pillar_fed", "Recon"), "#64748b")
        lab = f"{tid}\\n{t.get('title','')[:22]}"
        dot.append(f'"{tid}" [label="{lab}" fillcolor="{col}" fontcolor="white"];')
    for e in proc["edges"]:
        col, pw, style = REL[e["relation"]]
        dot.append(f'"{e["from"]}" -> "{e["to"]}" [color="{col}" penwidth={pw} '
                   f'style={style} arrowsize=0.7];')
    # legend cluster
    dot.append('subgraph cluster_leg { label="edge type"; fontsize=10; color="#e5e7eb"; style="rounded";')
    for i, (r, (c, pw, st)) in enumerate(REL.items()):
        dot.append(f'l{i}a [label="" shape=point width=0.01 color=white]; '
                   f'l{i}b [label="{r}" shape=plaintext fontsize=9]; '
                   f'l{i}a -> l{i}b [color="{c}" penwidth={pw} style={st}];')
    dot.append("}")
    dot.append("}")
    src = FIG / "aoyagi-thread-dag.dot"
    src.write_text("\n".join(dot))
    out = FIG / "aoyagi-thread-dag.png"
    subprocess.run(["dot", "-Tpng", "-Gdpi=150", str(src), "-o", str(out)], check=True)
    print("[fig]", out)


# ---- FIGURE 3: summary charts ----------------------------------------------
def fig_summary():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from collections import Counter

    fig, axs = plt.subplots(1, 3, figsize=(17, 5.2))

    # claims by status
    cs = Counter(c["status"] for c in claims["claims_lifecycle"])
    order = ["refuted", "retracted", "corrected", "confirmed"]
    col = {"refuted": "#dc2626", "retracted": "#991b1b", "corrected": "#ea580c", "confirmed": "#16a34a"}
    vals = [cs.get(k, 0) for k in order]
    axs[0].bar(order, vals, color=[col[k] for k in order])
    for i, v in enumerate(vals):
        axs[0].text(i, v, str(v), ha="center", va="bottom", fontsize=11, fontweight="bold")
    axs[0].set_title(f"Claims lifecycle (n={sum(vals)})", fontweight="bold")
    axs[0].tick_params(axis="x", rotation=20)

    # catches by channel
    ch = Counter(k["channel"] for k in dec["catches"])
    ccol = {"codex": "#7c3aed", "pen-and-paper": "#2563eb", "reviewer": "#0891b2"}
    ks = list(ch)
    axs[1].bar(ks, [ch[k] for k in ks], color=[ccol.get(k, "#64748b") for k in ks])
    for i, k in enumerate(ks):
        axs[1].text(i, ch[k], str(ch[k]), ha="center", va="bottom", fontsize=11, fontweight="bold")
    axs[1].set_title(f"Decorrelation catches by channel (n={sum(ch.values())})", fontweight="bold")
    axs[1].tick_params(axis="x", rotation=15)

    # concepts by pillar
    cp = Counter(c["pillar"] for c in rc["concepts"])
    ks2 = sorted(cp, key=lambda k: -cp[k])
    axs[2].bar(ks2, [cp[k] for k in ks2], color="#334155")
    for i, k in enumerate(ks2):
        axs[2].text(i, cp[k], str(cp[k]), ha="center", va="bottom", fontsize=10, fontweight="bold")
    axs[2].set_title(f"Concepts/lemmas built by pillar (n={sum(cp.values())})", fontweight="bold")
    axs[2].tick_params(axis="x", rotation=25)

    for a in axs:
        a.grid(True, axis="y", color="#e5e7eb", lw=0.7, alpha=0.7)
    fig.suptitle("aoyagi-full expedition — at a glance (mid-flight)", fontsize=15, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.94])
    out = FIG / "aoyagi-summary-charts.png"
    fig.savefig(out, dpi=150)
    plt.close(fig)
    print("[fig]", out)


if __name__ == "__main__":
    fig_timeline()
    fig_dag()
    fig_summary()
    print("[done]")
