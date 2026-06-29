# Lessons — `foundation-lift-iii`

The proven craft from #14 (dimension stack) and FL-II carries over — see
`expeditions/2026-06-29-foundation-lift/lessons.md` (L0–L5). The load-bearing ones to **apply every rung**:

- **L2 — transitive-consumer sweep.** After a namespace move, `rg` every moved identifier across all of
  `DLNFibre/` + full-build; transitive/unqualified consumers (no direct import) break only in the
  full-aggregator build.
- **L3 — gate next-rung dispatch on the prior formaliser's completion notification**, not a clean-tree
  snapshot (a formaliser can return for a review-driven follow-up + `git reset` and race a concurrent agent).
  Per-rung push + a strict build-gate + a clean committed base are the safety net.
- **L4 — `longLine` counts codepoints, not bytes** (`≤`/`≃`/`⟹` etc.); reflow against the linter's `:N:100`
  column.
- **L5 — under sustained box load, re-gate at phase boundaries + crux rungs, not every low-risk re-home.** For
  verbatim re-home rungs the formaliser's own fresh full-aggregator green is sufficient; the authoritative
  controller re-gate lands at the phase boundary + on the flagged crux rungs.

New lessons specific to this expedition accumulate below.

- _(none yet)_
