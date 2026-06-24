# Statement card - A4 selected-entry source-point coverage with coordinate

Date: 2026-06-24.

## Claim

The finite selected-entry all-pivot chart family can produce every finite
center value by a source chart point `(u, residual)`, and in the same witness
the unique certificate coordinate is `u`.

This is a generic finite selected-entry theorem.  Case 1 and Case 2 can
specialize it through the existing all-pivot certificates when a downstream
consumer needs that package.

## Source Status

Aoyagi PDF pp. 15-18 display the old-variable chart and a representative
selected-entry pivot chart in Case 1, and selected-entry pivot charts in the
blow-up discussion.  Lean's all-pivot family is the finite formal
generalization over all selected finite center pivots.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-selected-entry-source-point-coverage-coordinate-a4.md`.

Review:
`review-selected-entry-source-point-coverage-coordinate-a4.md`.

## Lean Status

File:
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`.

Name:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value_and_coord_zero_eq
```

The Case 1 source-point wrapper was deliberately not added in this slice after
independent review: it is a thin specialization and should wait until a
downstream theorem directly consumes it.

## Verification

Controller ran:

```text
source ~/.elan/env && lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
source ~/.elan/env && LEAN_NUM_THREADS=1 lake build DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
source ~/.elan/env && LEAN_NUM_THREADS=1 lake build DLNFibre
scripts/sorries
git diff --check
```

All passed.  The full build emitted only pre-existing Core warnings.

## Nonclaims

No analytic atlas coverage, transition regularity, source production,
analytic Jacobian/volume-form theorem, global normal crossings, termination,
pole order, or RLCT extraction.
