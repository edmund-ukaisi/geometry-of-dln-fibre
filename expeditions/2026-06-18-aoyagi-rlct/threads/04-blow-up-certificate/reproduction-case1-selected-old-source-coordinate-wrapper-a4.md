# A4 Case 1(2) Selected-Old Source-Coordinate Wrapper

Status: reproduced a source-coordinate adapter for the already supplied
displayed Case 1(2) selected-old boundary.

## Source Situation

Aoyagi's Case 1 begins with a first jump after the current pivot level:

```text
b_(J+1) = ... = b_(J+J1),
{ tilde_t_(s,k) = i } is empty for i = J+1, ..., J+J1-1.
```

The source chooses an old exceptional variable `u_(s,k)` with
`tilde_t_(s,k)=J+J1` and blows up the finite center

```text
d_ij = 0,      J+1 <= i <= J+J1,    J+1 <= j <= M^(S+1),
u_(s,k) = 0.
```

In the displayed Case 1(2) chart, Aoyagi selects the top-left strip entry and
writes

```text
d_ij = u_(S,J+1) d'_ij        on the displayed row strip,
d'_(J+1,J+1) = 1,
u_(s,k) = u_(S,J+1) u'_(s,k).
```

The source then applies the displayed `Q` column operation, replaces the
following factor by `C' = Q^-1 C`, applies the displayed `P` row operation,
and obtains the block form `diag(1,D_(J+1))`. The relevant source pages are
Aoyagi PDF pp. 15-19: first-jump data on p. 15, the Case 1 center and
Case 1(2) chart on pp. 16-17, the displayed `Q/P` calculation on p. 18, and
the continuation/advance split on p. 19.

## Pen-And-Paper Target

The already proved selected-old supplied chart-family boundary works in
residual row/column subtype coordinates. The new adapter records the direct
source-coordinate input form for the displayed source-order identity.

Let

```text
residual : Nat x Nat -> R,
C        : Nat -> tau -> R.
```

Restrict these functions to the active residual block:

```text
A(i,j) = residual(i,j),
C_res(j,t) = C(j,t),
```

where residual rows are `J+1..M(S)` and residual columns are
`J+1..M^(S+1)`. For the displayed top-left pivot, the source-coordinate pivot
condition is exactly

```text
residual(J+1,J+1) = 1.
```

The existing selected-old boundary is still supplied. The adapter only feeds
the source-coordinate residual/following-factor functions into its already
available source-order identity:

```text
A = case2SourceResidualBlock residual,
C = case2DisplayedFollowingFactor(..., case2SourceFollowingFactor C).
```

This gives the same source-order `Q/P` identity as before, now written from
source-coordinate residual and following-factor functions.

## Displayed-Pivot Finite Center Projection

The checkpoint also projects the already proved selected-entry finite ideal
algebra through the same boundary. For the displayed top-left strip pivot:

```text
selectedEntryChartMap(pivot,u,residual)(pivot) = u,
u divides every transformed finite Case 1 center generator,
( transformed finite Case 1 center generators ) = (u).
```

These are finite center statements for the displayed pivot variable
`u_(S,J+1)`. The checkpoint deliberately does not make the analogous
selected-old `Unit` projection with this same variable, since in Case 1(2)
`u_(S,J+1)` is the displayed row-strip pivot factor in
`u_(s,k)=u_(S,J+1)u'_(s,k)`, not an independently produced selected-old chart
variable.

## Caveats

- This does not construct the selected-old chart.
- This does not prove an affine blow-up atlas or chart coverage.
- This does not derive `(s0,k0)` from the `Unit` center token.
- This does not construct the raw-coordinate-to-`source` pullback.
- This does not prove chart-produced post-data or a transition invariant.
- This does not compute Jacobians, prove normal crossings, or extract RLCT.
