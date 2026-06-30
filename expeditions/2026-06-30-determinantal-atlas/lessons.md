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
