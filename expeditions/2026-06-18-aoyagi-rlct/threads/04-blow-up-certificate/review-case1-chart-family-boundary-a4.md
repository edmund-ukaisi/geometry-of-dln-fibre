# Review - A4 Case 1 Chart-Family Boundary

Status: reviewed; no blockers found.

## Reviewers

- Source-order scout: `Ptolemy the 3rd`.
- Lean/API scout: `Kepler the 3rd`.
- Pen-and-paper/source-scope scout: `Dirac the 3rd`.
- Implementation reviewer: `Linnaeus the 3rd`.

## Source and Math Review

The review found the Case 1 boundary source-safe when stated as an assumption
boundary. The finite Case 1 center is the existing `Unit` old-exceptional
branch plus row-strip entries

```text
J+1 <= i <= J+J1,
J+1 <= j <= n_(S+1).
```

The source-justified displayed charts are the old-exceptional-variable chart
and the top-left row-strip pivot chart. Arbitrary row-strip pivots remain
finite-center candidates, not source-displayed transition formulas.

The independent source-order scout confirmed that Aoyagi displays only the
`u_(s,k)` chart in Case 1(1), the top-left selected-entry chart
`d_(J+1,J+1)` in Case 1(2), and the top-left selected-entry chart in Case 2.
The full affine atlas is implicit in the standard blow-up phrase, not
enumerated by source formulas for arbitrary selected entries.

The main caveat is the `Unit` branch: Lean membership of `Sum.inl ()` in the
finite center is unconditional, but the source validity of the hidden selected
old label `(s,k)` still requires the external first-jump and selected-label
data.

## Lean and API Review

The Lean/API review recommended a direct Case 1 specialization of
`SelectedEntryChartFamilyBoundary` using `case1CenterGenerators`, before any
source-order transition interface. It also recommended keeping
`Case1FirstJumpHypotheses` out of the boundary itself, because those
hypotheses describe transition/invariant data rather than finite chart-family
regularity obligations.

The implemented API follows that recommendation and adds only low-risk finite
set helpers and projection wrappers.

An independent implementation review found no blockers. It confirmed that the
boundary projections remain guarded by a supplied
`Case1CenterChartFamilyBoundary` hypothesis, that the finite nonemptiness and
membership lemmas have the right hypotheses, and that the Lean docstrings do
not claim chart coverage, chart regularity, source-order transitions, or
source validity of the hidden old label.

## Required Caveats

- This is a named assumption boundary, not a proof of chart coverage.
- This does not prove chart regularity or transition regularity.
- This does not prove the source validity of the hidden old label represented
  by `Unit`.
- This does not prove an affine blow-up atlas.
- This does not prove source-order transition formulas for non-displayed
  row-strip pivots.
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
