# Reproduction - A2 Case 2 endpoint-transport pre-measure from cardinalities

Date: 2026-06-28.

Status: reproduced; Lean target selected.

## Target

The existing Case 2 fixed-base pre-measure wrapper assumes endpoint equivalence
data:

```text
eNext : tau ~= Case2ResidualColIndex n S (J + 1),
e q   : case2PostPivotTwoEdgeDomain n S J tau q
          ~= throughSubspaceEndpointComplementIndex ... q.
```

The previous cardinality rung constructs exactly these equivalences from
explicit finite cardinality equalities.  This rung substitutes that constructor
into the pre-measure wrapper.

## Calculation

Assume:

```text
hNext :
  card tau = card (Case2ResidualColIndex n S (J + 1)),

hEndpoints q :
  card (case2PostPivotTwoEdgeDomain n S J tau q)
    = card (throughSubspaceEndpointComplementIndex ... q).
```

Define

```text
equivs :=
  case2EndpointTransportEquivs_of_card_eq
    (kappa := throughSubspaceEndpointComplementIndex ...)
    n S J hNext hEndpoints.
```

Then

```text
eNext := equivs.1,
e     := equivs.2.
```

With these definitions, the endpoint-transported retained-passive datum is the
same datum used by the existing pre-measure theorem:

```text
retainedData yNext =
  (case2PostPivotSelectedEntryRetainedPassiveData
    n hS hcont hnext yNext eNext).endpointTransport e.
```

Therefore the existing theorem

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

gives both local-source membership and source-readback selected-entry matrix
readout.  The residual-coordinate equivalence in the conclusion is read through
the noncanonical `e` and `eNext` just constructed:

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
  n S (J + 1) (e last).symm ((e 0).symm.trans eNext).
```

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** The first Case 2 fixed-base pre-measure
endpoint-transport wrapper can be stated with explicit endpoint cardinality
equalities instead of supplied endpoint equivalence data.

**Assumed.** The same finite Case 2 branch inequalities as the original
pre-measure theorem; the cardinality equalities `hNext` and `hEndpoints`.

**Cited.** None.

**Deferred.** Proving those cardinality equalities from Aoyagi's concrete
dimension hypotheses; canonical or label-preserving endpoint equivalences;
source-prior transport; Jacobian comparison; integrability; normal crossings;
pole order; and RLCT.
