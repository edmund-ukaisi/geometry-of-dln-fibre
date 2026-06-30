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

- _(none yet)_
