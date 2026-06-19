# Review - A4 Case 1 selected-old source substitution

Status: reviewed; no blockers found.

## Reviewers

- Math/source reviewer: `Aquinas the 3rd`.
- Lean/API reviewer: `Heisenberg the 3rd`.
- Controller verification: current checkpoint commands listed below.

## Math Review

The boundary is source-faithful only because `source` is explicitly the
pullback after `old = u * old'`, not the raw pre-chart recurrence. With that
interpretation, the recurrence factor at level `J+J1` gains exactly one factor
`u`, and factors at other levels are unchanged.

The off-by-one convention is correct: a factor at level `J+J1` first affects
row `J+J1+1`, so strip rows `J+1..J+J1` do not yet include the old selected
factor in their source recurrence weights.

## Lean/API Review

The generic finite-product lemmas are same-domain update lemmas; they do not
insert a new label. This matches Case 1(2), where the hidden old selected
label is already in the introduced-label domain.

`Case1SelectedOldFactoredBaseData` keeps the needed assumptions explicit:
selected-label introducedness, same levels, selected-variable factorisation,
and non-selected introduced-variable agreement. The first-jump wrapper uses
only the selected level field, while the row-strip corollary connects this
source substitution to the existing row-strip old-weight convention.

## Caveats

- This does not follow from `Case1FirstJumpHypotheses` alone.
- This does not construct or validate the hidden old label represented by the
  `Unit` center generator.
- This does not construct the selected-old chart, the factored-base state, or
  chart-produced post-data.
- This does not prove coverage, regularity, Jacobian accounting, normal
  crossings, or RLCT extraction.

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
