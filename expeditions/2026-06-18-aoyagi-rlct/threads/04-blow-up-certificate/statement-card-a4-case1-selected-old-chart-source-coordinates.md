# Statement card - A4 Case 1 selected-old chart source coordinates

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.case1SelectedOldPostWeight`
- `DLNFibre.DLN.Aoyagi.case1SelectedOld_diagonal_mul_sourceMatrix`
- `DLNFibre.DLN.Aoyagi.case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates`

## Statement

Lean proves the elementary source-coordinate row-strip identity for Aoyagi
Case 1(1).  If the selected old chart denominator is `u_old`, source entries
on the Case 1 row strip are `u_old` times the divided post entries, and lower
residual rows are unchanged.  Multiplying by pre-chart row weights is
therefore the same as multiplying the divided post matrix by row weights that
absorb `u_old` exactly on the strip:

```text
diag(b_pre) * D_source = diag(b_post) * D_post.
```

The source-coordinate specialization restricts a function
`Nat x Nat -> R` to residual rows and actual-width residual columns using the
existing `case2SourceResidualBlock` helper.

## Source Role

This matches the Case 1(1) chart on Aoyagi PDF p. 16, where the selected old
exceptional variable `u_(s,k)` itself divides the row strip.  It is separate
from the displayed Case 1(2) branch, where `u_(S,J+1)` is the displayed pivot
and `u_(s,k)=u_(S,J+1)u'_(s,k)`.

## Proved

- The Case 1 selected-old post row-weight convention.
- The generic row-strip identity
  `diag(baseWeight) * case1RowStripSourceMatrix strip u A =
   diag(case1SelectedOldPostWeight strip u baseWeight) * A`.
- The source-coordinate residual-block specialization using
  `case1ResidualRowStrip n S J J1` and `case2SourceResidualBlock residual`.
- The shared row-strip helper comments now distinguish the Case 1(1)
  selected old denominator from the displayed Case 1(2) pivot.

## Not Proved

- No construction of the selected old blow-up chart or affine atlas.
- No proof of chart coverage, regularity, transition regularity, or Jacobian.
- No `Q/P` source-order identity for Case 1(1).
- No introduction of the displayed label `(S,J+1)`.
- No proof that the chart produces the selected-label exponent update.
- No normal-crossing certificate or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-chart-source-coordinates-a4.md`.
- Review artifact:
  `review-case1-selected-old-chart-source-coordinates-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
