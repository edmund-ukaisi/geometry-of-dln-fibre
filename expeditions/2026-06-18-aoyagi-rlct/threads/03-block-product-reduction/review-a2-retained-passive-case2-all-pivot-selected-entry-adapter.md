# Review - A2 retained-passive Case 2 all-pivot selected-entry adapter

Reviewer: xhigh `Halley`.

## Verdict

PASS.  No findings.

## Scope checked

Reviewed the uncommitted diff adding:

```lean
exists_pivot_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero

exists_pivot_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero

PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_pivot_aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_of_ne_zero
```

The review checked theorem statement scope, coordinate/equivalence orientation,
docstring nonclaims, and whether a fresh reproduction card was required.

## Review notes

The fixed `pivot + hpivot` input is replaced correctly by
`hprod : case2DisplayedPostPivotFreeTwoEdgeFactorProduct ... != 0`.  The proof
uses the existing selected-entry all-pivot matrix inverse to choose a nonzero
displayed matrix entry, then transports it through
`(Equiv.prodCongr e2 e0).trans residualCoordEquiv`.  The resulting entrywise
orientation matches the pre-existing fixed-pivot retained-passive Case 2 bridge.

The docstrings keep the supplied displayed factor identities, displayed-product
nonzeroness, and lack of source production/factor alignment explicit.

No additional reproduction is required beyond the existing selected-entry
all-pivot reproduction and review.  The new endpoints add no analytic,
source-production, normal-crossing, pole-order, or RLCT content.

## Verification

The controller ran:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
scripts/sorries
git diff --check
```

Both focused builds passed with only pre-existing imported warning noise.  The
direct axiom-footprint check for all three new public endpoints reports:

```text
[propext, Classical.choice, Quot.sound]
```
