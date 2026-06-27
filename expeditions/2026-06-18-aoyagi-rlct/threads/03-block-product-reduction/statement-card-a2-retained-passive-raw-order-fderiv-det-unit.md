# Statement Card - A2 Retained-Passive Raw-Order FDeriv Determinant Unit

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

## Lean Names

```text
fderiv_topologyTupleEdgeRawOrderInverse_comp_fderiv_topologyTupleEdgeRawOrder
fderiv_topologyTupleEdgeRawOrder_comp_fderiv_topologyTupleEdgeRawOrderInverse
fderiv_topologyTupleEdgeRawOrder_det_isUnit_of_mem_topologyTupleDetChartSet
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-fderiv-det-unit.md
```

## Verification

Review:

```text
review-a2-retained-passive-raw-order-fderiv-det-unit.md
```

passed by xhigh read-only explorer `Hilbert the 4th`.

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
```

## Claim

At every point of the retained-passive tuple determinant chart, the ambient
Frechet derivative of

```text
topologyTupleEdgeRawOrder
```

has a tangent inverse given by the derivative of

```text
topologyTupleEdgeRawOrderInverse
```

at the corresponding raw-order target point.  Consequently the determinant of
the forward derivative is a unit.

## Role

This closes the density-free tangent-invertibility layer for the
retained-passive raw-order chart.  It is the prerequisite for later local
Jacobian-density or measure-transport statements, but it does not provide
those statements itself.

## Nonclaims

No explicit derivative formula, determinant formula, Jacobian density,
measure pushforward, source-rank coverage, normal crossing, pole order, or
RLCT statement is part of this slice.
