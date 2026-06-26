# Statement Card - A2 Case 2 residual-coordinate endpoint-equivalence composition

## Claim

If the endpoint residual row and column coordinate types have already been
identified with the Case 2 residual row and column ranges, then the whole
endpoint residual scalar-coordinate index is equivalent to the Case 2
candidate selected-entry center:

```text
AoyagiResidualBlockCoordinateIndex mu nu
  ~= (case2ResidualBlockPivotEntries n S J : Type).
```

## Lean Name

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfCase2EndpointEquivs
```

## Boundaries

Finite product-index composition only.  The endpoint row/column equivalences
remain supplied hypotheses.  No source chart, compatible factor construction,
selected-entry matrix identity, source/image equality, normal crossings, pole
order, or RLCT.
