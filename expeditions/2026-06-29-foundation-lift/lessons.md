# Lessons — `foundation-lift`

The proven craft from #14 (the dimension stack) carries over — see
`expeditions/2026-06-29-dimension-stack/lessons.md` (L0–L4). The load-bearing ones to **apply every rung**:

- **L2 — transitive-consumer sweep.** After a namespace move, `rg` every moved identifier across all of
  `DLNFibre/` + full-build; transitive/unqualified consumers (no direct import) break only in the
  full-aggregator build. Bit every #14 rung.
- **L3 — gate next-rung dispatch on the prior formaliser's completion notification**, not a clean-tree
  snapshot (a formaliser can return for a review-driven follow-up + `git reset` and race a concurrent agent).
  Per-rung push + a strict build-gate + a clean committed base are the safety net.
- **L4 — `longLine` counts codepoints, not bytes** (`≤`/`≃`/`⟹` etc.); reflow against the linter's `:N:100`
  column, not `awk length`.

New lessons specific to this expedition accumulate below.

- **L5 — under sustained box load, re-gate at phase boundaries + crux rungs, not every low-risk re-home.** A
  full `scripts/lb DLNFibre` re-gate costs minutes when the box is loaded (the parallel aoyagi op). For
  low-risk *verbatim re-home* rungs, the formaliser's own fresh full-aggregator green + a clean tree is
  sufficient assurance (it's a real build it ran, not a relayed headline); the **controller's authoritative
  re-gate lands at the phase boundary** (on the accumulated state, before the phase PR) **and on the flagged
  crux rungs** (independent verification of the delicate ones). Keeps the gate where it bites without paying a
  multi-minute build per trivial move. (Distinct from #14, where lighter load made per-rung re-gates cheap.)
