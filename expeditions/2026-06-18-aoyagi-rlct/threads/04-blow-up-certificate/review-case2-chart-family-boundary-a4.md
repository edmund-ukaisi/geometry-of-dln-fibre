# Review - A4 Case 2 Chart-Family Boundary

Status: reviewed; no blockers found.

## Reviewers

- Source/math reviewer: `Popper the 3rd`.
- Lean/API reviewer: `Nietzsche the 3rd`.

## Source and Math Review

The source/math review found no blocker. The package is correctly scoped as an
assumption boundary plus a small nonemptiness lemma.

- `SelectedEntryChartFamilyBoundary` contains only supplied chart-regularity
  and transition-regularity predicates over a finite center.
- It carries no chart data, maps, Jacobian statement, coverage statement, or
  source-order transition formula.
- `case2ResidualBlockPivotEntries_nonempty_of_cont` proves only that the
  displayed pivot `(J+1,J+1)` belongs to the Case 2 residual-block center under
  the continuation hypothesis.
- The Case 2 residual block keeps prefix-minimum row bounds and actual-width
  column bounds.

The reviewer flagged one wording caveat: the Lean docstring should not suggest
a formal coverage predicate. The docstring now says "chart-family regularity
interface" rather than "coverage/regularity interface".

## Lean and API Review

The Lean/API review found no blocker. The boundary adds no import or typeclass
burden and is placed coherently next to the selected-entry chart-map API.

One low-level API improvement was incorporated: the generic structure fields now
use implicit pivot binders, so projection-style use can omit the pivot when it
is inferred from the membership proof.

## Required Caveats

- This is a named assumption boundary, not a proof of chart coverage.
- This does not prove chart regularity or transition regularity.
- This does not prove an affine blow-up atlas.
- This does not prove source-order transition formulas for non-displayed
  pivots.
- This does not produce recurrence or exponent post-data.
- This does not prove Jacobian formulas, normal crossings, or RLCT extraction.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From the worktree root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory found no Lean forbidden-token use; hits are existing prose
  mentions in expedition notes and statement cards.
