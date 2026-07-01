# Lessons — `determinantal-atlas`

The proven craft from #14, FL-II, and FL-III carries over — see
`expeditions/2026-06-29-foundation-lift-iii/lessons.md` (L0–L8). The load-bearing ones to **apply every rung**:

- **L2 — transitive-consumer sweep.** After a namespace/file move, `rg` every moved identifier across all of
  `DLNFibre/` + full-build; transitive/unqualified consumers break only in the full-aggregator build.
- **L3 — gate next-rung dispatch on the prior formaliser's completion notification**, not a clean-tree snapshot.
- **L4 — `longLine` counts codepoints, not bytes**; reflow against the linter's `:N:100` column.
- **L5 — under load, re-gate at phase boundaries + crux rungs**, not every low-risk re-home (trust the
  formaliser's own fresh full-aggregator green for verbatim re-homes).
- **L6 — a file split can sever an incidental transitive instance import** (`Module.Free`/`Flat` via a
  now-removed import); fix with the honest minimal import, not by re-importing the heavy module. A green
  full build after a split is necessary; a missing-instance error there is the expected symptom.
- **L7 — a `DLNFibre.Core.X` namespace SHADOWS Mathlib's root `X`** for files that `open X` inside
  `namespace DLNFibre.Core`. New files mirroring a Mathlib target declare in the **bare Mathlib-mirror
  namespace** (`namespace AlgebraicGeometry…` / `Ideal` / `MvPolynomial`), NOT `DLNFibre.Core.`-prefixed.
- **L8 — GUARD-first when abstracting a concrete proof:** write the concrete discharge BEFORE fixing the
  abstract hypothesis signature; the naive forward shape can be undischargeable by the model it abstracts.

New lessons specific to this expedition accumulate below.

- **DA1 — warm a new worktree's `.lake` ONLY from a worktree at *identical source*.** Warming this worktree
  via `cp -al` of `.lake/build` from `foundation-lift` (a **pre-FL-III** source) left stale oleans for the
  trdeg/Dimension stack that FL-III had restructured (it moved `trdeg_eq_of_integral_injective` into a new
  `Dimension/Integral` module absent from the warm). The aggregator then failed with a **spurious
  `Unknown constant Algebra.trdeg`** — which looked like a dev regression but was pure cache contamination
  (the source is correct, the Mathlib API is present, FL-III built it green). **`scripts/sorries` (a text grep)
  cannot catch an elaboration failure**, so a contaminated branch can read "0 sorry" while red. Fix: `rm -rf
  .lake/build` + clean rebuild. Rule: warm only from an identical-commit worktree, else don't warm (pay the
  clean build) — a structurally-divergent warm is worse than none.
- **DA2 — under heavy multi-worktree box load, DEFER the from-scratch build; do not fight it, and do not
  manually `pkill`.** Parallel expeditions (aoyagi/main/genm) saturating the box OOM-reap a fresh det-atlas
  build mid-module (olean count static while lake PIDs churn) — `scripts/lb`'s worker-semaphore throttles
  count but not total memory pressure. Forcing it thrashes. Manual `pkill` of build processes on a shared box
  is error-prone (a kill loop signalled its own shell, exit 144). Right move: bank the state, defer to a
  quieter tick (the idle heartbeat is for exactly this re-check), and verify no det-atlas lake is alive
  before re-launching `scripts/lb`.
- **DA3 — a background teammate's `idle_notification` (`idleReason: "available"`) WITHOUT a completion
  report means INCOMPLETE, not done.** In Phase 2 this fired 3× (P2.d wrote both files sorry-free then idled
  before wiring/build/commit; `p2d-review` wrote its Codex consult then idled before its verdict + the
  re-gate — twice). The work-product looked plausible (`scripts/sorries` = 0) but was un-built / un-wired /
  un-committed, or the verdict/re-gate was missing — and **sorry-free ≠ green** (DA1). Right move on a
  no-report idle: (1) inspect actual state (git tip/tree, new files, aggregator wiring, the expected artefact
  dir), (2) do a controller read of what's there, then (3) **RESUME the teammate via `SendMessage`** with a
  precise finish-checklist (context intact) — do NOT assume done, and do NOT take over the build yourself
  (you'd reconstruct its design + lose its decorrelated Codex). A completed background agent is resumable by
  name; resuming is cheaper and safer than re-dispatching or hand-finishing. Contrast a teammate that sends a
  full report THEN idles (e.g. P2.c) — that idle is genuine completion, just acknowledge it.
- **DA4 — before replying "all resolved" on a PR, fetch the LATEST reviews/comments (incl. reviews
  submitted after your last fetch).** On PR #21 the operator posted a three-item review THEN a two-item
  follow-up review at the newer head; the controller's consolidated "resolved" reply answered the OLDER
  three-item review while the two follow-up items were still open, and the operator had to point it out.
  Reviews (`gh api …/pulls/N/reviews`) are SEPARATE from issue-comments (`gh pr view N --json comments`);
  fetch BOTH, newest-last, and confirm you're addressing the current head's open items before declaring done.
- **DA5 — a concrete DLN transition theorem named on the raw def `whnf`-times-out; the ABSTRACT/opaque form
  is the exported API.** `targetProductOverlapTransition` (and `overlapTriv`/`targetChartLoc`) are built
  through the concrete `perPivotLocalTrivializationDatum.trivialization`. `AtlasChart.overlapTransition_trans_symm`
  proves the round-trip GENERICALLY over the opaque structure field `C.trivK` (cheap) — but at the concrete
  `pivotAtlasChart`, `trivK` reduces to the trivialization monster, so BOTH a delegation and a direct
  groupoid-collapse proof `whnf`-timeout (200000) on the double-localized carrier. The base-side
  (`chartOverlapTransitionK`, on `awayOverlap` of base elements, no `trivK`) delegates fine. Keep
  transition-coherence theorems at the ABSTRACT `AtlasChart` level or the predicate level on derived charts;
  a raw-concrete-def named theorem needs `irreducible` on the trivialization or a `maxHeartbeats` bump.
  RESOLUTION (PR #21): a TARGETED `set_option maxHeartbeats 800000 in` on the delegation
  (`:= AtlasChart.overlapTransition_trans_symm (pivotAtlasChart I) (pivotAtlasChart J)`) COMPILES,
  axiom-clean — the bump is a per-declaration ceiling (no project-wide tax; other decls unaffected), costing
  ~40s extra only when `FibreTargetOverlap` itself recompiles. So `targetProductOverlapTransition_trans_symm`
  IS exported. Gotcha: `set_option … in` goes ABOVE the docstring (a docstring immediately before `set_option`
  fails to parse — "unexpected token 'set_option'; expected 'lemma'").
