# Statement Card - A2 Case 2 residual-coordinate index pivot entries

## Claim

For the Case 2 residual block, Aoyagi's p.13 residual scalar-coordinate index
is equivalent to the finite set of candidate selected entries:

```text
AoyagiResidualBlockCoordinateIndex
  (Case2ResidualRowIndex n S J)
  (Case2ResidualColIndex n S J)
  ≃ (case2ResidualBlockPivotEntries n S J : Type).
```

## Lean Name

```text
case2ResidualBlockCoordinateIndexEquivPivotEntries
```

## Boundaries

Finite index bookkeeping only.  No chart construction, source/image equality,
compatible factor construction, selected-entry matrix identity, normal
crossings, pole order, or RLCT.

