# Statement card - A4 generic pivot-first `Q/P` algebra bridge

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `cbf934d`.

Names:

- `DLNFibre.DLN.Aoyagi.pivotComplement`
- `DLNFibre.DLN.Aoyagi.pivotFirstIndexEquiv`
- `DLNFibre.DLN.Aoyagi.pivotFirstMatrix`
- `DLNFibre.DLN.Aoyagi.pivotFirstX`
- `DLNFibre.DLN.Aoyagi.pivotFirstY`
- `DLNFibre.DLN.Aoyagi.pivotFirstD`
- `DLNFibre.DLN.Aoyagi.pivotFirstMatrix_eq_pivotPreQBlock`
- `DLNFibre.DLN.Aoyagi.weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ`
- `DLNFibre.DLN.Aoyagi.weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul`

## Statement

Lean proves a generic algebraic bridge from an arbitrary normalised matrix pivot
to the already-formalised top-left `Q/P` pivot identities. For row pivot
`rowPivot`, column pivot `colPivot`, and a matrix `A` with
`A rowPivot colPivot = 1`, `pivotFirstMatrix` reindexes rows and columns by
putting the chosen pivot first. The theorem
`pivotFirstMatrix_eq_pivotPreQBlock` identifies this pivot-first matrix with
`pivotPreQBlock` using the named lower-left, upper-right, and lower-right
pieces `pivotFirstX`, `pivotFirstY`, and `pivotFirstD`.

The two `weightedPivotBlockRowOp...pivotFirstMatrix...` corollaries then apply
the existing normalised `Q/P` identities under the explicit quotient-witness
hypothesis:

```text
forall i, b i = q i * b0.
```

## Source role

Aoyagi displays the top-left pivot `d_(J+1,J+1)` in Case 1(2) and Case 2. The
non-displayed selected-entry chart family is not written in the paper. This
checkpoint formalises only the generic finite algebra that would be used after
a separate proof has supplied a selected-entry chart, pivot normalisation to
`1`, coordinate transport for following factors and weights, and quotient
witnesses for the pivot row.

## Proved

- `Unit ⊕ {i // i != pivot}` is equivalent to the original index type by
  putting the selected pivot first.
- A matrix with pivot entry `1` becomes the existing normalised block
  `[1 y; x D]` after pivot-first reindexing.
- The existing normalised `Q/P` clearing identities apply to that pivot-first
  block when the lower-row weights satisfy `b i = q i * b0`.
- The product-preservation version carries a following factor already expressed
  in the same pivot-first column coordinates.

## Assumed

- The selected pivot entry has already been normalised to `1`.
- The following factor, diagonal weights, and quotient witnesses are already in
  pivot-first coordinates.
- The quotient-witness hypothesis `forall i, b i = q i * b0` is supplied.

## Not proved

- No selected-entry chart construction, affine blow-up atlas, or chart coverage.
- No source reproduction of non-displayed arbitrary pivot charts.
- No Case 1 or Case 2 transition invariant.
- No proof that Case 1 strip pivots or Case 2 residual-block pivots satisfy the
  quotient-witness hypothesis.
- No row/column coordinate transport theorem for Aoyagi's following factors.
- No regularity, localization/unit, Jacobian, exponent update, termination,
  normal-crossing certificate, or RLCT extraction.

## Reproduction and review

- Reproduction artifact:
  `reproduction-arbitrary-pivot-q-p-bridge-a4.md`.
- Xhigh source/Lean scouts confirmed this is safe only as a generic algebraic
  bridge, not as source-backed arbitrary chart coverage.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
