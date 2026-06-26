# Review - A2 Case 2 concrete two-edge factor family

Date: 2026-06-26.

Reviewers: controller, using xhigh source auditor `Schrodinger` and xhigh
Lean/API scout `Sartre`.

## Verdict

Pass.  The Lean slice is a socket reducer for the already displayed Case 2
two-factor product.  It does not promote Aoyagi's relabelling instruction into
successor source-data construction.

## Source Check

Schrodinger checked Aoyagi pp. 11-13 and pp. 19-22.  The source supports the
local continuing product `D_(J+1) * C'_+`, and it supports the finite
bookkeeping that this is the post-pivot residual block followed by the
post-pivot free `C'` tail.

The source does not construct endpoint equivalences to a separately packaged
successor chart, does not source-produce `Cprime` as successor chart data, and
does not identify entries of the product with selected-entry center
coordinates.  The new selected-entry theorem therefore keeps the successor
entrywise readout as `hentry`.

## Lean/API Check

Sartre identified the concrete two-edge specialization as the next finite API
move after the generic bridge.  The helper family uses endpoints

```text
tau,
Case2ResidualColIndex n S (J+1),
Case2ResidualRowIndex n S (J+1).
```

The proof of the product theorem is a specialization of
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix`
with reflexive endpoint equivalences and factor identities by matrix
extensionality.  The selected-entry theorem then specializes the existing
successor `CenterCoord` bridge with the same concrete family.

## Lean Check

Focused module builds passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualSelectedEntryChartBridge
```

## Nonclaims

No construction of successor source coordinates, endpoint equivalences,
source-produced `Cprime`, selected-entry readout, source image, source-measure
transport, chart coverage, normal crossings, pole order, or RLCT.
