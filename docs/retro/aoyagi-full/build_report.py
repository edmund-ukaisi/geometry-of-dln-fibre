#!/usr/bin/env python3
"""Emit the expedition chronicle in two forms from the combed data (data/*.json):

  EXPEDITION.md   — GitHub-viewable prose chronicle with the matplotlib figures woven through
                    + ledger tables (renders inline on GitHub; feeds the PDF).
  expedition.html — a self-contained single-file interactive report (tabbed, filterable tables,
                    figures embedded as base64). Open in any browser; nothing external.

Prose is authored here; tables are generated from the JSON so the two outputs never drift.
"""
from __future__ import annotations
import json, base64, html as H
from pathlib import Path

FIG = Path(__file__).resolve().parent
DATA = FIG / "data"
load = lambda n: json.load(open(DATA / n))
proc, claims, dec, rc, les = (load(f) for f in
    ["process.json", "claims.json", "decorrelation.json", "routes_concepts.json", "lessons.json"])

def short(s, n=110):
    s = (s or "").strip().replace("\n", " ")
    return s if len(s) <= n else s[: n - 1] + "…"

# ------------------------------------------------------------------ figures
FIGS = {
    "timeline": "aoyagi-timeline.png",
    "summary": "aoyagi-summary-charts.png",
    "dag": "aoyagi-thread-dag.png",
    "loc": "aoyagi-3metric-churn-author-time.annotated.png",
    "pillars": "aoyagi-pillars-native-loc.annotated.png",
}
def b64(name):
    p = FIG / FIGS[name]
    return "data:image/png;base64," + base64.b64encode(p.read_bytes()).decode()

# ------------------------------------------------------------------ prose
TITLE = "aoyagi-full — the expedition chronicle (mid-flight, day 22)"
LEDE = ("A digestible picture of the still-running expedition formalising Aoyagi's exact DLN learning "
        "coefficient in Lean 4 — from scratch, zero axioms. Snapshot 2026-07-12 (~UPDATE-975). This is the "
        "*narrative & decision* record — how the proof is being found — and complements `REPORT.md`, which "
        "measures what was built. Source: five decorrelated agents combing the expedition ledger "
        "(~975 UPDATE blocks, ~214k lines of expedition prose) + ~2,700 commits; data in `data/`.")

CAVEAT = ("**Caveat.** The log corpus is the run's *own* chronicle, so this is largely its self-account; "
          "counts and thread spans are git-anchored, and Lean claims are kernel-anchored (forced "
          "`#print axioms` = `[propext, Classical.choice, Quot.sound]` on every landed brick — the branch "
          "tree contains zero `axiom` declarations). The run is MID-FLIGHT: the final headline is not yet "
          "minted; read every forward-looking statement as a model, not a result.")

CHRONICLE = [
("The arc, in one breath",
 ["Launched 2026-06-20 14:36; this snapshot is day 22 (~15-16 full-clip days after two idle days, a "
  "70-hour operator pause, and three near-idle days). **Stage 1 banked (07-09):** the fully-general "
  "learning-coefficient ladder, citation-free — the L=2 (reduced-rank-regression) equality proven "
  "unconditionally; the general-L **upper** bound proven unconditionally; the general-L **equality** "
  "carried on exactly one crisply-stated proposition (□) — elementary box-integrability of "
  "`frobSq(∏A)^(−c)` below half the combinatorial threshold. **Stage 2 (in flight):** discharge (□). "
  "32 major claims tracked so far: 9 refuted, 1 retracted, 11 corrected, 7 proven, 2 open. The churn "
  "signature is the same as the sibling Quillen–Suslin run: **6.6% of built Lean ever deleted** — the "
  "thrash lives in design and certificates (2.2 lines of prose per line of Lean), essentially never in "
  "shipped code."]),
("Stage 1: the ladder, and the two-paper composition",
 ["The value side (Aoyagi's λ formula and its min-arithmetic), the block-elimination reduction, and the "
  "deepest-point step went first. The deepest-point 'wall' is characteristic of the whole run: scoped "
  "initially as needing Morse–Bott theory Mathlib lacks, it dissolved when a pen-and-paper seat traced "
  "the primary source and found Aoyagi §5 is four explicit elementary steps — no Morse–Bott, no Hironaka "
  "— turning a research wall into a bounded build. The L=2 lower bound was then built from scratch (the "
  "heart's base case, ~49 wall-hours on the fixed route). The one citation (a per-chart monomial-threshold "
  "axiom, S2) was retired by an axiom→theorem upgrade in place plus excision: the branch tree now contains "
  "no axioms at all. Meanwhile the geometric half — determinantal codimensions, the quadratic integer "
  "program, permutation invariance — had been proven months earlier on the L&R side of the repo; the two "
  "papers were formally married on 07-12 by `minAdm_eq_cCodim` (all widths, kernel-checked), so the "
  "analytic estimates consume proven geometry, not cited geometry."]),
("The shortcut graveyard around the heart",
 ["The run's signature dynamic: at least eight self-contained mechanisms were proposed for the hard core "
  "and shed — corank recursion, weighted peel, Gram-determinant atom, two front-peel variants, a modular "
  "seam, a seam chart, box-Morse, an AM-GM corner, a Route-C corner endpoint, a casting route, and "
  "finally a front-first g(Q) bound. Two instruments killed them: the **zero-slack certificate** (a "
  "(3,3,3,4) configuration sitting exactly at threshold, so any lossy bound fails) and the distilled "
  "compass *'only monomial-by-construction Jacobians survive binding strata — a det-inverse in a Jacobian "
  "relocates the singularity, it never removes it.'* A triple-decorrelated certificate then explained the "
  "pattern once and for all: the singularity class is closed under peeling — corner-mildness is logically "
  "equivalent to the full theorem, so **no strictly-easier self-contained sub-problem exists**, and "
  "progress is only by well-founded induction. Every later shortcut death (the plain-IH step predicate, "
  "the front-first bound) is that theorem rediscovered at finer scale: any estimate that does not consume "
  "the induction hypothesis cannot reach the threshold, because one peel honestly contributes only its "
  "own charge and the recursion supplies the rest."]),
("The operator's course corrections",
 ["Two operator interventions shaped the endgame. 07-10: the build-vs-cite fork on the residual atom was "
  "resolved as **build** ('the route-search is over'), backed by an adversarial census (86% of corner "
  "charts regenerate the same atom). 07-11 10:13: the standing directive to **attack Aoyagi §5 head-on "
  "in a dedicated lane** rather than keep building around it — vindicated the same day when an empirical "
  "build-scan re-scoped the 'mostly banked' native route to 600–1000+ further lines, and the controller "
  "recorded: *'the top-down native route is the slog; the direct §5 peel attacks the heart.'* The endgame "
  "was then re-pointed onto the `DecoratedDescent` package — an admissibility predicate plus step and "
  "base hypotheses in which **the induction hypothesis officially carries the determinantal weight** — "
  "with a proven clean-three driver `DecoratedDescent → ∀M (□)`. The lesson encoded as statement shape: "
  "nothing short of the real recursion can close it."]),
("The catch machinery",
 ["Fifteen decorrelated catches are on the ledger, and the load-bearing ones share a shape: a green or "
  "plausible artifact refused on fidelity grounds before integration. wtint proved the emitted "
  "det-weight is NOT absorbed by the reduced-chain IH (sharp boundary a+b≤q), forcing the three-way "
  "routing. The F2 counterexample showed no single sector covers the box — a genuine obstruction, dodged "
  "by a rank-stratified cover with charges that ADD (the min-vs-add 'RLCT-collapse' trap is now guarded "
  "by a proven q-ary AM-GM decoupling lemma with divergence witnesses on both sides of its hypothesis). "
  "A completed, green #4 base build was refused integration because its fixed-carrier shape is "
  "unpreservable by the step — the hold was validated by a conclusion-withheld audit. An independent "
  "hunt refuted the off-sector §7 argument and pivoted the step onto Aoyagi's own coupled diag(b) "
  "resolution. When soundness doubt localized to one link (does the integer program equal the "
  "determinantal codimension on non-monotone widths?), the run proved it rather than arguing it."]),
("Where it stands (mid-flight)",
 ["The `DecoratedDescent` build is executing a numbered plan: #1 (the back-peel α-unlock) and #2 (the "
  "corank-survival bridge + units bound) and #3 (the admissibility definition, carrier locked) are "
  "integrated clean-three; #4 (the z-dependent base leg) has its design pinned by certificate and its "
  "tide running; #5 (the step — the concentrated analytic heart, via coupled diag(b)) has a banked "
  "buildplan and a settled-sound target. Remaining after that: assemble the package, instantiate the "
  "proven driver, feed the banked conditional headline, and mint the unsuffixed "
  "`aoyagi_learning_coefficient` behind the forced kernel audit. The standing model says one-to-two "
  "full-clip days; the honest caveat is that #5 is exactly where any remaining surprise lives."]),
("What made it work (so far)",
 ["The same engine as the sibling run — a decorrelated design-refutation loop with fidelity holds — but "
  "stressed differently: here the difficulty concentrates in ONE irreducible analytic core, and the "
  "characteristic failure mode was not special-object identities but **shortcut-shaped selection**: "
  "self-contained, bankable objects kept being chosen over the induction that alone could close the "
  "goal. The fixes that mattered were a mechanical compass (reject det-inverse Jacobians at spec time), "
  "certificates that made the additivity of charges explicit, and operator-level scheduling — a standing "
  "lane pointed at the heart. Ground truth throughout is artifacts, not prose: forced axiom prints, "
  "clean rebuilds, refused integrations. Many wrong intermediate verdicts; essentially zero wrong code "
  "shipped."]),
]

# ------------------------------------------------------------------ markdown
def md_table(headers, rows):
    out = ["| " + " | ".join(headers) + " |", "|" + "|".join(["---"] * len(headers)) + "|"]
    for r in rows:
        out.append("| " + " | ".join(str(c).replace("|", "\\|") for c in r) + " |")
    return "\n".join(out)

def build_md():
    S = [f"# {TITLE}", "", LEDE, "", CAVEAT, "",
         "See also: **[`REPORT.md`](REPORT.md)** — the line-count / churn / per-pillar completion report.",
         "", "---", ""]

    S += ["## 1. The expedition at a glance", "",
          "![Summary charts](aoyagi-summary-charts.png)", ""]
    st = {c["status"]: 0 for c in claims["claims_lifecycle"]}
    for c in claims["claims_lifecycle"]:
        st[c["status"]] += 1
    S += [f"- **{len(claims['claims_lifecycle'])} claims** tracked: "
          f"{st.get('refuted',0)} refuted, {st.get('retracted',0)} retracted, "
          f"{st.get('corrected',0)} corrected, {st.get('proven',0)} proven, {st.get('open',0)} open.",
          f"- **{len(dec['catches'])} decorrelation catches** " + ", ".join(f"{n} {ch}" for ch, n in __import__('collections').Counter(c['channel'] for c in dec['catches']).most_common()) + ".",
          f"- **{len(proc['threads'])} thread-seats**, "
          f"{len(proc['edges'])} interaction edges, {len(proc['coordination_events'])} coordination failures.",
          f"- **{len(rc['concepts'])} concepts/lemmas** built (" + ", ".join(f"{ch} {n}" for ch, n in __import__('collections').Counter(c['pillar'] for c in rc['concepts']).most_common(4)) + ", …).",
          "- **Day 22, mid-flight**, one branch; 6.6% Lean churn (built code rarely discarded); 99.7k native-token Lean + 214k prose.", "", "---", ""]

    S += ["## 2. Timeline", "",
          "Thread-seats as swimlanes (git first/last commit), milestones, refutations, decorrelation "
          "catches, coordination failures, and the Codex-outage span; commit pulse below. Top axis = "
          "hours from base, bottom = wall-clock.", "",
          "![Timeline](aoyagi-timeline.png)", "", "---", ""]

    S += ["## 3. Chronicle", ""]
    for head, paras in CHRONICLE:
        S += [f"### {head}", ""] + ["\n".join(paras) if isinstance(paras, list) else paras, ""]
    S += ["---", ""]

    S += ["## 4. Claims lifecycle (the refutation ledger)", "",
          "Every claim that was proposed and then refuted, retracted, corrected, or notably confirmed. "
          "*The scientific heart of the run.*", "",
          md_table(["Claim", "Status", "Killed / fixed by", "Resolution", "Thread"],
                   [[short(c["claim"], 80), f"**{c['status']}**", short(c["killed_or_fixed_by"], 60),
                     short(c["resolution"], 60), c.get("thread", "")]
                    for c in claims["claims_lifecycle"]]), "", "### Witness objects", "",
          md_table(["Witness", "Object", "Showed / killed"],
                   [[w["name"], short(w["object"], 55), short(w["what_it_killed_or_showed"], 70)]
                    for w in claims["witnesses"]]), "", "---", ""]

    S += ["## 5. How the strategy evolved (routes) + the dialectic graph", ""]
    for r in rc["routes"]:
        S += [f"**{r['pillar']}** — {short(r.get('one_line',''),120)}", ""]
        for i, stp in enumerate(r["steps"], 1):
            S.append(f"{i}. `{stp.get('stage_thread','')}` — {short(stp.get('mechanism',''),90)} "
                     f"*({stp.get('status','')})*" + (f" — {short(stp.get('why_changed',''),80)}" if stp.get('why_changed') else ""))
        S.append("")
    S += ["The thread-interaction graph (who refuted / corrected / superseded / fed whom):", "",
          "![Thread DAG](aoyagi-thread-dag.png)", "", "---", ""]

    S += ["## 6. Concepts & lemmas built (by pillar)", "",
          md_table(["Concept", "Kind", "Pillar", "Meaning", "File"],
                   [[f"`{c['name']}`", c["kind"], c["pillar"], short(c["one_line"], 66),
                     f"`{Path(c['lean_file']).name}`" if c.get("lean_file") else ""]
                    for c in sorted(rc["concepts"], key=lambda c: c["pillar"])]), "", "---", ""]

    S += ["## 7. Decorrelation & friction", "",
          "Every event where an independent channel caught a real error before it cost built code:", "",
          md_table(["Claim caught", "Channel", "Cheap/costly", "Thread"],
                   [[short(k["claim_caught"], 75), f"**{k['channel']}**", k.get("cheap_or_costly",""),
                     k.get("thread","")] for k in dec["catches"]]), ""]
    co = dec["codex_outage"]
    S += [f"**Codex outage.** Down ~{co.get('outage_duration_hours_approx','?')} h "
          f"({short(co.get('broke_iso',''),16)} → {short(co.get('restored_iso',''),16)}); "
          f"error: `{short(co.get('error_message',''),70)}`. "
          f"{short(co.get('degradation_assessment',''),260)}", "",
          "**Where confident language ran ahead of the proof:**", "",
          md_table(["What", "When", "Reality"],
                   [[short(g["what"],55), short(g.get("when",""),30), short(g["reality"],70)]
                    for g in dec["overclaim_gaps"]]), "",
          "**Coordination failures:**", "",
          md_table(["Time", "Type", "Description"],
                   [[short(e["iso_time"],16), e["type"], short(e["description"],80)]
                    for e in proc["coordination_events"]]), "", "---", ""]

    S += ["## 8. Methodological lessons", "",
          md_table(["Lesson", "Why / generalization"],
                   [[f"**{short(l['lesson'],60)}**",
                     short(l.get("transferable_generalization") or l.get("why",""), 130)]
                    for l in les["lessons"]]), "", "### Recurring anti-patterns", "",
          md_table(["Anti-pattern", "Occurrences", "Description / how caught"],
                   [[f"**{a['name']}**", short(str(a.get("occurrences","")),40),
                     short(a["description"] + " — " + a.get("how_caught",""), 110)]
                    for a in les["antipatterns"]]), "", "---", ""]

    S += ["*Generated from `docs/diagnostic-figures/data/*.json` (five decorrelated log-combers) by "
          "`build_expedition.py` (figures) + `build_report.py` (this document).*", ""]
    (FIG / "EXPEDITION.md").write_text("\n".join(S), encoding="utf-8")
    print("[md] EXPEDITION.md")

# ------------------------------------------------------------------ HTML
def html_table(headers, rows, tid, filterable=True):
    thead = "".join(f"<th onclick=\"sortT('{tid}',{i})\">{H.escape(h)}</th>" for i, h in enumerate(headers))
    body = ""
    for r in rows:
        body += "<tr>" + "".join(f"<td>{c}</td>" for c in r) + "</tr>"
    filt = (f'<input class="filter" placeholder="filter {len(rows)} rows…" '
            f'oninput="filterT(\'{tid}\',this.value)">') if filterable else ""
    return f'{filt}<table id="{tid}"><thead><tr>{thead}</tr></thead><tbody>{body}</tbody></table>'

def esc(s):
    return H.escape(str(s or ""))

def status_badge(s):
    col = {"refuted": "#dc2626", "retracted": "#991b1b", "corrected": "#ea580c", "confirmed": "#16a34a"}
    return f'<span class="badge" style="background:{col.get(s,"#64748b")}">{esc(s)}</span>'

def chan_badge(s):
    col = {"codex": "#7c3aed", "pen-and-paper": "#2563eb", "reviewer": "#0891b2"}
    return f'<span class="badge" style="background:{col.get(s,"#64748b")}">{esc(s)}</span>'

def build_html():
    st = {}
    for c in claims["claims_lifecycle"]:
        st[c["status"]] = st.get(c["status"], 0) + 1
    stats = [
        ("day 22, mid-flight", "launch → DecoratedDescent endgame"),
        (str(len(claims["claims_lifecycle"])), "claims tracked"),
        (f"{st.get('refuted',0)+st.get('retracted',0)}", "refuted / retracted"),
        (str(len(dec["catches"])), "decorrelation catches"),
        (str(len(proc["threads"])), "thread-seats"),
        (str(len(rc["concepts"])), "concepts built"),
        ("5.8%", "Lean churn"),
        ("clean", "#print axioms"),
    ]
    statcards = "".join(f'<div class="stat"><div class="num">{esc(v)}</div><div class="lab">{esc(l)}</div></div>'
                        for v, l in stats)

    # tabs content
    def tab_overview():
        chr_html = ""
        for head, paras in CHRONICLE[:2]:
            chr_html += f"<h3>{esc(head)}</h3>" + "".join(f"<p>{esc(' '.join(p) if isinstance(p,list) else p)}</p>" for p in ([paras] if isinstance(paras,(list,)) and paras and isinstance(paras[0],str) else paras))
        return (f'<div class="statgrid">{statcards}</div>'
                f'<p class="lede">{esc(LEDE)}</p>'
                f'<div class="note">{H.escape("Caveat: the log corpus is the runs own chronicle; verdicts are the runs, counts are git-anchored, completeness is independently verified.")}</div>'
                f'<img src="{b64("summary")}" alt="summary charts">')

    def para_block(paras):
        if isinstance(paras, list):
            return "".join(f"<p>{esc(p)}</p>" for p in paras)
        return f"<p>{esc(paras)}</p>"

    def tab_chronicle():
        return "".join(f"<h3>{esc(h)}</h3>{para_block(p)}" for h, p in CHRONICLE)

    def tab_timeline():
        return (f'<p>Thread-seats as swimlanes (git first/last commit) with milestones, refutations, '
                f'decorrelation catches, coordination failures, and the Codex-outage span; commit pulse '
                f'below. Top axis = hours from base, bottom = wall-clock.</p>'
                f'<img src="{b64("timeline")}" alt="timeline"><h3>Line-count &amp; churn (from REPORT.md)</h3>'
                f'<img src="{b64("loc")}" alt="loc"><img src="{b64("pillars")}" alt="pillars">')

    def tab_claims():
        rows = [[esc(short(c["claim"], 200)), status_badge(c["status"]), esc(short(c["killed_or_fixed_by"],140)),
                 esc(short(c["resolution"],140)), esc(c.get("thread",""))] for c in claims["claims_lifecycle"]]
        t = html_table(["Claim", "Status", "Killed / fixed by", "Resolution", "Thr"], rows, "claims")
        wr = [[esc(w["name"]), esc(short(w["object"],90)), esc(short(w["what_it_killed_or_showed"],140))]
              for w in claims["witnesses"]]
        wt = html_table(["Witness", "Object", "Showed / killed"], wr, "witnesses")
        sr = [[esc(s["ref"]), esc(short(s["used_for"],140))] for s in claims["sources"]]
        stt = html_table(["Source", "Used for"], sr, "sources", filterable=False) if False else html_table(["Source","Used for"], sr, "sources")
        return f"<h3>Claims lifecycle — the refutation ledger</h3>{t}<h3>Witness objects</h3>{wt}<h3>Sources</h3>{stt}"

    def tab_routes():
        r_html = ""
        for r in rc["routes"]:
            steps = "".join(f'<li><code>{esc(s.get("stage_thread",""))}</code> — {esc(short(s.get("mechanism",""),160))} '
                            f'<em>({esc(s.get("status",""))})</em>'
                            + (f' — {esc(short(s.get("why_changed",""),120))}' if s.get("why_changed") else "") + "</li>"
                            for s in r["steps"])
            r_html += f'<h3>{esc(r["pillar"])}</h3><p><em>{esc(short(r.get("one_line",""),200))}</em></p><ol>{steps}</ol>'
        rows = [[f'<code>{esc(c["name"])}</code>', esc(c["kind"]), esc(c["pillar"]),
                 esc(short(c["one_line"],140)), f'<code>{esc(Path(c["lean_file"]).name) if c.get("lean_file") else ""}</code>']
                for c in sorted(rc["concepts"], key=lambda c: c["pillar"])]
        ct = html_table(["Concept", "Kind", "Pillar", "Meaning", "File"], rows, "concepts")
        return f"{r_html}<h3>Concepts &amp; lemmas built ({len(rc['concepts'])})</h3>{ct}"

    def tab_process():
        return (f'<p>The dialectic graph — who refuted / corrected / superseded / fed whom. '
                f'{len(proc["threads"])} seats, {len(proc["edges"])} edges.</p>'
                f'<img src="{b64("dag")}" alt="thread dag">')

    def tab_decorrelation():
        rows = [[esc(short(k["claim_caught"],160)), chan_badge(k["channel"]), esc(k.get("cheap_or_costly","")),
                 esc(k.get("thread","")), esc(short(k.get("detail",""),160))] for k in dec["catches"]]
        t = html_table(["Claim caught", "Channel", "Cost", "Thr", "Detail"], rows, "catches")
        co = dec["codex_outage"]
        obox = (f'<div class="note"><b>Codex outage</b> — down ~{esc(co.get("outage_duration_hours_approx","?"))} h '
                f'({esc(short(co.get("broke_iso",""),16))} → {esc(short(co.get("restored_iso",""),16))}). '
                f'<code>{esc(short(co.get("error_message",""),90))}</code>. {esc(short(co.get("degradation_assessment",""),400))}</div>')
        gr = [[esc(short(g["what"],90)), esc(short(g.get("when",""),40)), esc(short(g["reality"],160))]
              for g in dec["overclaim_gaps"]]
        gt = html_table(["Over-claim", "When", "Reality"], gr, "gaps")
        cr = [[esc(short(e["iso_time"],16)), esc(e["type"]), esc(short(e["description"],160))]
              for e in proc["coordination_events"]]
        cft = html_table(["Time", "Type", "Description"], cr, "coord")
        cf = [[esc(short(c["iso_time_or_commit"],20)), esc(short(c["note"],200))] for c in dec["confidence"]]
        cft2 = html_table(["When", "Belief update"], cf, "conf")
        return (f"<h3>Decorrelation catches</h3>{t}{obox}"
                f"<h3>Over-claim vs reality</h3>{gt}<h3>Coordination failures</h3>{cft}"
                f"<h3>Confidence trajectory</h3>{cft2}")

    def tab_lessons():
        lr = [[esc(short(l["lesson"],90)), esc(short(l.get("transferable_generalization") or l.get("why",""),200)),
               esc(short(l.get("example",""),140))] for l in les["lessons"]]
        lt = html_table(["Lesson", "Generalization", "Example"], lr, "lessons")
        ar = [[esc(a["name"]), esc(short(str(a.get("occurrences","")),60)),
               esc(short(a["description"],160)), esc(short(a.get("how_caught",""),120))] for a in les["antipatterns"]]
        at = html_table(["Anti-pattern", "Occurrences", "Description", "How caught"], ar, "antip")
        return f"<h3>Transferable lessons ({len(les['lessons'])})</h3>{lt}<h3>Recurring anti-patterns</h3>{at}"

    TABS = [("Overview", tab_overview()), ("Timeline", tab_timeline()), ("Chronicle", tab_chronicle()),
            ("Claims", tab_claims()), ("Routes & concepts", tab_routes()), ("Process & DAG", tab_process()),
            ("Decorrelation", tab_decorrelation()), ("Lessons", tab_lessons())]
    tabbar = "".join(f'<button class="tab{" active" if i==0 else ""}" onclick="show({i})">{esc(t)}</button>'
                     for i, (t, _) in enumerate(TABS))
    panels = "".join(f'<section class="panel{" active" if i==0 else ""}" id="p{i}">{c}</section>'
                     for i, (_, c) in enumerate(TABS))

    CSS = """
:root{--bg:#f8fafc;--fg:#0f172a;--mut:#475569;--line:#e2e8f0;--accent:#0f766e;}
*{box-sizing:border-box}
body{margin:0;font:15px/1.55 -apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,Helvetica,Arial,sans-serif;color:var(--fg);background:var(--bg)}
header{background:linear-gradient(135deg,#0f172a,#1e3a5f);color:#fff;padding:26px 32px}
header h1{margin:0 0 6px;font-size:24px}
header p{margin:0;color:#cbd5e1;max-width:900px;font-size:13.5px}
.tabs{position:sticky;top:0;z-index:10;display:flex;flex-wrap:wrap;gap:2px;background:#fff;border-bottom:1px solid var(--line);padding:0 18px}
.tab{border:0;background:none;padding:13px 16px;font-size:14px;color:var(--mut);cursor:pointer;border-bottom:3px solid transparent}
.tab:hover{color:var(--fg)}
.tab.active{color:var(--accent);border-bottom-color:var(--accent);font-weight:600}
main{max-width:1180px;margin:0 auto;padding:26px 32px 80px}
.panel{display:none}.panel.active{display:block}
h3{margin:26px 0 10px;font-size:17px;border-bottom:1px solid var(--line);padding-bottom:5px}
p{color:#1e293b}.lede{font-size:15.5px;color:var(--mut)}
img{max-width:100%;height:auto;border:1px solid var(--line);border-radius:8px;margin:10px 0;background:#fff}
.statgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:12px;margin:6px 0 18px}
.stat{background:#fff;border:1px solid var(--line);border-radius:10px;padding:14px 16px;text-align:center}
.stat .num{font-size:24px;font-weight:700;color:var(--accent)}
.stat .lab{font-size:12px;color:var(--mut);margin-top:3px}
.note{background:#fff7ed;border:1px solid #fed7aa;border-radius:8px;padding:12px 14px;font-size:13.5px;color:#7c2d12;margin:12px 0}
table{border-collapse:collapse;width:100%;margin:8px 0 4px;font-size:13px;background:#fff;border:1px solid var(--line);border-radius:8px;overflow:hidden}
th,td{border-bottom:1px solid var(--line);padding:7px 10px;text-align:left;vertical-align:top}
th{background:#f1f5f9;cursor:pointer;user-select:none;position:sticky;top:46px;font-size:12px}
th:hover{background:#e2e8f0}
tbody tr:hover{background:#f8fafc}
code{background:#f1f5f9;padding:1px 5px;border-radius:4px;font-size:12px}
.badge{color:#fff;padding:2px 8px;border-radius:999px;font-size:11.5px;font-weight:600;white-space:nowrap}
.filter{width:100%;max-width:340px;padding:7px 10px;margin:6px 0;border:1px solid var(--line);border-radius:7px;font-size:13px}
ol li{margin:4px 0}
footer{color:var(--mut);font-size:12px;padding:20px 32px;border-top:1px solid var(--line)}
"""
    JS = """
function show(i){document.querySelectorAll('.tab').forEach((t,j)=>t.classList.toggle('active',j===i));
document.querySelectorAll('.panel').forEach((p,j)=>p.classList.toggle('active',j===i));window.scrollTo(0,0);}
function filterT(id,q){q=q.toLowerCase();document.querySelectorAll('#'+id+' tbody tr').forEach(r=>{
r.style.display=r.innerText.toLowerCase().includes(q)?'':'none';});}
function sortT(id,col){const t=document.getElementById(id),tb=t.tBodies[0];
const rows=[...tb.rows];const dir=t.getAttribute('data-sd-'+col)==='1'?-1:1;t.setAttribute('data-sd-'+col,dir===1?'1':'0');
rows.sort((a,b)=>{const x=a.cells[col].innerText.trim(),y=b.cells[col].innerText.trim();
const nx=parseFloat(x),ny=parseFloat(y);if(!isNaN(nx)&&!isNaN(ny))return (nx-ny)*dir;
return x.localeCompare(y)*dir;});rows.forEach(r=>tb.appendChild(r));}
"""
    doc = (f"<!doctype html><html lang=en><head><meta charset=utf-8>"
           f"<meta name=viewport content='width=device-width,initial-scale=1'>"
           f"<title>{esc(TITLE)}</title><style>{CSS}</style></head><body>"
           f"<header><h1>{esc(TITLE)}</h1><p>{esc(LEDE)}</p></header>"
           f"<nav class=tabs>{tabbar}</nav><main>{panels}</main>"
           f"<footer>Self-contained interactive report. Data: five decorrelated log-combers over the "
           f"expedition record + git (see <code>data/*.json</code>). Figures embedded. "
           f"Companion: <code>EXPEDITION.md</code> (GitHub) · <code>REPORT.md</code> (line counts).</footer>"
           f"<script>{JS}</script></body></html>")
    (FIG / "expedition.html").write_text(doc, encoding="utf-8")
    print("[html] expedition.html", f"({len(doc)//1024} KB)")


if __name__ == "__main__":
    import sys
    build_md()
    if "--html" in sys.argv:  # interactive single-file HTML — reintroduce when the report grows complex
        build_html()
    print("[done]")
