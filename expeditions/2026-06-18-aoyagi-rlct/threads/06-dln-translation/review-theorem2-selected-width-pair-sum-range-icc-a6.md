# Review - Theorem 2 selected-width pair sum range/Icc form

Date: 2026-06-25.

Reviewer: xhigh `Locke`.

## Verdict

Pass.  No blocking findings.

## Checks

- `lake env lean DLNFibre/DLN/Aoyagi/FinalFormula.lean` passed.
- The Lean theorem
  `aoyagiSelectedWidthPairSum_eq_range_Icc_selectedWidthNat` is an indexing
  conversion from the `Fin` double sum with indicator to the Nat-indexed
  `range`/`Icc` strict upper-triangle sum.
- The `i = ell` boundary is handled correctly by the empty inner `Icc`.
- Source fidelity checks against Aoyagi PDF pp. 8-9 passed: p. 9 contains the
  pair sum over `1 <= i < j <= ell+1`; p. 8 contains the printed
  nonselected upper inequality with `ell - 1`, and the boundary note correctly
  quarantines the repaired cutoff from printed `AoyagiDefinition3SourceData`.
- The Core/LR boundary is maintained: `FinalFormula.lean` does not import
  `ClosedForm.lean` or Core.

## Minor Fix Applied

The reproduction note originally said the total selected-width accessor was
"definitionally" the original finite-indexed value on `i < ell + 1`.  The
wording was tightened to say it "simp-rewrites" by
`aoyagiSelectedWidthNat_of_lt`.

