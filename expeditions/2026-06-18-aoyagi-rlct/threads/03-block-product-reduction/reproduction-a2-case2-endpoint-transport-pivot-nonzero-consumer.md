# Reproduction - A2 Case 2 endpoint-transport pivot nonzero consumer

## Shape

The endpoint-transported explicit Case 2 retained-passive datum already has
the factor-aligned all-pivot consumer

```text
exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_ne_zero.
```

Its only remaining finite selected-entry input is the displayed two-edge
product nonzero hypothesis

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont
  (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
  (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)
  != 0.
```

For the constructed successor selected-entry point, this nonzero hypothesis is
discharged by the coordinate hypothesis

```text
yNext ((J + 2, J + 2), membership) != 0.
```

## Derivation

The constructed Case 2 source residual and free `Cprime` were chosen so that
their displayed post-pivot free two-edge product is exactly the successor
selected-entry matrix:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_successorSelectedEntrySource_eq :
  case2DisplayedPostPivotFreeTwoEdgeFactorProduct ...
    (case2SuccessorSelectedEntrySourceResidual ...)
    (case2SuccessorSelectedEntrySourceCprime ...)
  =
  case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext.
```

The successor selected-entry matrix is nonzero when its displayed pivot
coordinate is nonzero:

```text
case2SuccessorSelectedEntryMatrix_ne_zero_of_yNext_pivot_ne_zero.
```

Therefore `hyNext` implies the displayed two-edge product is nonzero.  Feeding
that nonzero product into the factor-aligned endpoint-transported explicit
datum consumer gives the selected-entry residual-product readout with an
existential pivot and selected-entry coordinates.

## Boundary

This is constructed finite Case 2 source production.  It removes the displayed
product nonzero input only for the explicit endpoint-transported
selected-entry retained-passive datum, and only under the concrete
successor-pivot coordinate nonzero hypothesis.

It does not prove fixed-pivot nonzeroness for arbitrary displayed data, does
not prove nonzeroness for an arbitrary retained-passive `ofTopologyTuple`
datum, and does not identify an arbitrary fixed-base source-readback adjacent
window with the constructed Case 2 datum.

The all-pivot conclusion produces some selected-entry pivot and coordinates.
It does not identify that existential pivot with the successor pivot
`(J + 2, J + 2)`, and it does not identify the produced coordinates with the
input `yNext`.

## Proved / Assumed / Deferred

**Proved by this reproduction.** The explicit endpoint-transported Case 2
selected-entry retained-passive datum has the all-pivot selected-entry
residual-product readout under `hyNext`, without a separate displayed-product
nonzero hypothesis.

**Assumed.** Endpoint equivalences `e`, the successor endpoint equivalence
`eNext`, and the concrete pivot-coordinate nonzero hypothesis `hyNext`.

**Deferred.** Fixed-base endpoint provenance, arbitrary source-readback factor
alignment, source-prior transport, Jacobian comparison, normal crossings, pole
order, and RLCT.
