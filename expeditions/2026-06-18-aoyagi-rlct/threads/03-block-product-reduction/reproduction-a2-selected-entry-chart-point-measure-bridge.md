# A2 selected-entry chart-point measure bridge

## Scope

This note records the finite selected-entry coordinate calculation that
connects two already-present Lean presentations:

- the center-indexed signed-box chart
  `SelectedEntrySignedBox.CenterCoord.chartMap pivot :
  (center -> R) -> (center -> R)`;
- the one-chart normal-crossing microcertificate
  `selectedEntryCenterSqFormalJacobianChartCertificate`, whose chart point is
  `(u, residual)` with residual indexed by `center.erase pivot`.

The source passage is Aoyagi's selected-entry blow-up in the product-reduction
proof: the displayed Case 1 and Case 2 local substitutions factor the selected
block by a new scalar `u_{S,J+1}`, normalize the chosen entry to `1`, and make
the remaining entries residual coordinates (Aoyagi PDF pp. 15-22, especially
the Case 2 block on pp. 19-22).  This checkpoint is only a finite coordinate
bridge and measure restatement.  It is not an analytic atlas construction or
an RLCT extraction.

## Coordinate calculation

Let `E` be a finite center set and choose a pivot `p in E`.  A chart point is

```text
(u, r) in R x (E \ {p} -> R).
```

Extend `r` to an ambient residual function by

```text
rho_i = r_i  if i != p and i in E,
rho_p = 0.
```

The selected-entry chart is

```text
x_p = u,
x_i = u * r_i  for i != p.
```

The center-indexed signed-box coordinates encode the same point by a function
`y : E -> R`:

```text
y_p = u,
y_i = r_i  for i != p.
```

Thus the chart-point adapter is

```text
theta(y) = (y_p, y|_{E \ {p}}).
```

Composing the normal-crossing chart map with this adapter gives the
center-indexed signed-box chart map:

```text
(chi o theta)(y)_p = y_p,
(chi o theta)(y)_i = y_p * y_i  for i != p.
```

This is exactly `SelectedEntrySignedBox.CenterCoord.chartMap pivot y`.

## Loss and determinant calculation

For the selected-entry square-sum,

```text
sum_{i in E} x_i^2
  = u^2 + sum_{i != p} (u r_i)^2
  = u^2 * (1 + sum_{i != p} r_i^2).
```

The one-chart normal-crossing microcertificate records:

```text
loss exponent        = 1,
loss unit            = 1 + sum_{i != p} r_i^2.
```

The derivative matrix of `(u,r) |-> x`, ordered with `u` first, is triangular
by blocks:

```text
[ 1   0  ]
[ r   uI ].
```

Therefore

```text
det D chi(u,r) = u ^ |E \ {p}|,
|det D chi(u,r)| = |u| ^ |E \ {p}|.
```

Under the adapter `theta(y) = (y_p, y|_{E \ {p}})`, this determinant density is

```text
|y_p| ^ |E \ {p}|,
```

which is exactly `SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y`.

The pivot hyperplane `u = 0` is not part of the injective chart locus.  In the
signed-box measure theorem it is removed up to Lebesgue-null equality before
using the Jacobian pushforward theorem, and then restored by the already-proved
null-image argument.

## Measure consequence

The existing signed-box theorem proves

```text
Measure.map (CenterCoord.chartMap pivot)
  ((prod_i volume|(-R_i,R_i)).withDensity
    (fun y => ofReal (sourceDensity pivot y)))
= volume.restrict (CenterCoord.chartMap pivot '' signedBoxSet R).
```

Since

```text
formalChartMap pivot (chartPointAdapter pivot y)
  = CenterCoord.chartMap pivot y,
```

the same equality can be restated through the chart-point coordinates:

```text
Measure.map (fun y => formalChartMap pivot (chartPointAdapter pivot y))
  ((prod_i volume|(-R_i,R_i)).withDensity
    (fun y => ofReal (sourceDensity pivot y)))
= volume.restrict (CenterCoord.chartMap pivot '' signedBoxSet R).
```

Because `chartPointAdapter` and `formalChartMap` are continuous, Mathlib's
measurable `Measure.map_map` gives the two-stage chart-point form:

```text
Measure.map (formalChartMap pivot)
  (Measure.map (chartPointAdapter pivot)
    ((prod_i volume|(-R_i,R_i)).withDensity
      (fun y => ofReal (sourceDensity pivot y))))
= volume.restrict (CenterCoord.chartMap pivot '' signedBoxSet R).
```

This is a transport of the already-proved signed-box measure theorem through a
finite coordinate adapter.  It is not a natural product-measure identification
on chart-point space and does not fill the analytic atlas volume record.

## Kill conditions

- Kill if this is described as constructing the analytic selected-entry atlas.
- Kill if the pivot hyperplane is treated as an injective chart locus rather
  than a null set handled by the existing signed-box theorem.
- Kill if the chart-point pushforward is presented as original source-prior
  transport or determinant-chart Haar transport.
- Kill if the theorem is used as source coverage, source-rank coverage,
  source-image equality, transition regularity, source production, branch
  termination, normal-crossing extraction, pole order, or RLCT.

