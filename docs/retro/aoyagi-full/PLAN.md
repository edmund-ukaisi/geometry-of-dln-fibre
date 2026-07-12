# The aoyagi-full comprehension instrument — working plan

Branch `retro/aoyagi-full`, branched off `expedition/aoyagi-full` (pull its progress in by merging;
this directory is disjoint from everything the live expedition writes, so merges stay clean).
Goal: not correctness review of the headline (small, kernel-assisted, handled separately) but
**understanding the expedition** — three thin documents over one shared substrate.

## The three products

1. **`proof-as-built/`** — the mathematical argument as actually formalised.
   Reverse blueprint: the headline's dependency cone extracted from the Lean environment,
   collapsed to three zoom levels (pillar → module → ~20 spine theorems), each spine node carrying
   a blind-written math statement; a ~10-page linearised narrative of the whole argument; and the
   chapter "how the formal proof differs from Aoyagi's paper, and why". Overlays: LoC per node,
   correction-events per node (the fights heat-map), fan-in.
2. **`process-retro/`** — what went down, measured then interpreted.
   Correction taxonomy with catch-latency trend; lesson-efficacy table (did recorded lessons
   change behaviour — recurrence by fresh-tide vs veteran); counterfactual scheduling (realised
   makespan vs DAG-optimal — the parallelisation number); harness-friction catalogue with proposed
   fixes; the gestalt questions run as opposing-brief seat pairs, every claim sha-linked.
3. **`library-report/`** — is it good code, and what should be extracted.
   Mechanical passes (Mathlib env linters, fan-in/orphan/duplicate analysis on the reference
   graph, hypothesis-bloat metrics) shortlist; policy-rubric semantic review of the shortlist;
   the extraction roadmap (candidate → home: Mathlib / Core / stays → generalisation delta),
   incl. the known Mathlib gaps the run filled by hand (Cauchy–Binet, PSD det-monotonicity,
   polar/box CoV family, q-ary AM-GM decoupling, monomial-box atoms).

## The shared substrate (`substrate/`)

- `decls.json` — every declaration in `lean/DLNFibre/DLN/RLCT` (+ consumed Core): name, kind,
  statement pretty-printed, file:line, direct dependencies (constants used by the proof term).
  Extracted by a Lean metaprogram (extend `LeanNativeTokenLineCount.lean`-style tooling or the
  cordon's CollectAxioms batch walker).
- `cone.json` — the headline's transitive dependency cone; spine identification (max-flow /
  articulation nodes between definitions and headline).
- `events.db` (sqlite or json) — ledger events ↔ commits ↔ files ↔ decls: UPDATE blocks parsed
  with dates, corrections/lessons/deviations tagged; joins the five chronicle JSONs in `data/`.
- Regeneration: all scripts runnable from this directory; git reads go through the shared object
  store (refs like `origin/expedition/aoyagi-full` work from any worktree).

## Sequencing

- **Now (pre-mint, against the moving branch):** events.db + ledger cross-audit; linter and
  graph mechanical passes; decl-dump metaprogram prototype; lesson-efficacy and friction tables.
- **At mint:** freeze the cone (well-defined only then); blind node summaries; spine narrative;
  paper-diff chapter; counterfactual scheduling on the final DAG.
- **Iterate:** merge `origin/expedition/aoyagi-full` → regenerate substrate → re-render.

## Inherited assets (in this directory)

- The chronicle toolkit (adapted from the QS expedition): `generate_loc.py` (3-metric + pillar
  LoC), `build_expedition.py` (timeline/DAG/summary figures), `build_report.py` (EXPEDITION.md),
  `data/*.json` (five decorrelated log-combing agents, snapshot 2026-07-12 ~UPDATE-975),
  `EXPEDITION.md` + `REPORT.md` (mid-flight editions), figures, per-commit CSV, token cache.
- Method notes: decorrelate interpretive seats (opposing briefs + reconciliation); blind readers
  never see docstrings; every interpretive claim links a sha/UPDATE; coverage tracked explicitly
  (which file/claim no seat examined) — no silent caps.
