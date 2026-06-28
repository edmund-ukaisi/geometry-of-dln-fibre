# A2 selected-entry all-pivot nonzero coverage

## Claim

The fixed selected-pivot inverse can be upgraded to an all-pivot finite
coverage statement at the finite coordinate level: every nonzero center
coordinate vector, and every nonzero residual matrix after a residual-coordinate
equivalence, lies in some selected-entry pivot chart.

## Reproduction

Let `center` be the finite set of residual-block entries used as the
selected-entry center.  For a selected pivot `p : center`, the center-indexed
chart map is

```text
chartMap p y p = y p,
chartMap p y i = y p * y i     for i != p.
```

If a target center-coordinate value `x : center -> R` has `x p != 0`, the fixed
inverse is

```text
y p = x p,
y i = x i / x p     for i != p.
```

Then

```text
chartMap p y p = x p,
chartMap p y i = x p * (x i / x p) = x i.
```

Thus `chartMap p y = x`.  This is already the fixed-pivot inverse.

For all-pivot coverage, assume only `x != 0`.  Then some center coordinate is
nonzero; choose it as `p`.  Applying the fixed-pivot inverse gives

```text
exists p : center, exists y : center -> R, chartMap p y = x.
```

For a residual matrix `D : Matrix μ ν R`, a residual-coordinate equivalence

```text
residualCoordEquiv : AoyagiResidualBlockCoordinateIndex μ ν ≃ center
```

turns entries into center coordinates by

```text
x p = D (residualCoordEquiv.symm p).1 (residualCoordEquiv.symm p).2.
```

If `D != 0`, some matrix entry `D i j` is nonzero.  Choosing

```text
p = residualCoordEquiv (i, j)
```

gives a nonzero pivot coordinate in the center-vector readout.  The fixed-pivot
matrix inverse then gives

```text
D =
  AoyagiResidualBlockCoordinateIndex.matrix
    (fun c => chartMap p y (residualCoordEquiv c)).
```

## Boundary

This removes the need to preselect a globally nonzero fixed pivot in the
finite selected-entry chart algebra.  It is not retained-passive
source-production: it does not prove that an actual `sourceReadback` residual
matrix is nonzero, does not identify the post-pivot and following factors, and
does not transport source measure, construct normal crossings, compute pole
order, or extract RLCT.
