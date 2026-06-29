# A2 selected-entry chart-point weighted product measure

## Scope

This note records the finite-coordinate density transport for the
selected-entry chart-point adapter.  It starts from the already-formalized
adapter split

```text
y |-> (y_p, y|_{E \ {p}})
```

and adds the selected-entry Jacobian density

```text
sourceDensity_p(y) = |y_p|^(#(E \ {p})).
```

It is not an analytic atlas construction, not original/source-prior
transport, and not an RLCT extraction.  It is the chart-point version of the
same finite selected-entry substitution used in Aoyagi's product-reduction
calculation:

```text
x_p = u,
x_i = u r_i  for i != p.
```

## Density calculation

Let `E` be a finite center set and let `p in E`.  Write a center-coordinate
point as `y : E -> R`, and define the chart-point coordinates

```text
u = y_p,
r_i = y_i  for i in E \ {p}.
```

The chart-point adapter is

```text
T(y) = (u, r).
```

The selected-entry source density in center coordinates is

```text
sourceDensity_p(y) = |y_p|^(#(E \ {p})).
```

Since the first chart-point coordinate of `T(y)` is exactly `y_p`, the
corresponding chart-point density is

```text
chartPointDensity_p(u, r) = |u|^(#(E \ {p})).
```

Thus

```text
chartPointDensity_p(T(y)) = sourceDensity_p(y).
```

The absolute value is essential.  The signed box allows both signs of `u`, and
the selected-entry Jacobian density is the absolute determinant.

## Measure transport

The unweighted product-measure split already proves

```text
T_* (prod_{i in E} volume|(-R_i, R_i))
  = volume|(-R_p, R_p)
      x prod_{i in E \ {p}} volume|(-R_i, R_i).
```

Lean names the right-hand side:

```text
chartPointProductMeasure pivot R.
```

Combining this with the density pullback identity gives

```text
T_* ((prod_{i in E} volume|(-R_i, R_i))
        .withDensity (ofReal sourceDensity_p))
  = (chartPointProductMeasure pivot R)
        .withDensity (ofReal chartPointDensity_p).
```

No positivity hypothesis on `R` is needed.  Positivity is only needed for
nonzero-measure corollaries.  The pivot hyperplane is also not removed here:
this theorem is a pure adapter transport, and the density is defined on the
whole chart-point space.

## Lean route

The proof uses the generic `withDensity` pushforward identity

```text
map f (eta.withDensity (g o f)) = (map f eta).withDensity g,
```

with

```text
f = chartPointAdapter pivot,
eta = prod_{i in E} volume|(-R_i, R_i),
g = ofReal chartPointDensity_p.
```

The needed inputs are:

- `measurable_chartPointAdapter`;
- `map_chartPointAdapter_signedBoxMeasure_eq_chartPointProductMeasure`;
- `chartPointDensity_chartPointAdapter_eq_sourceDensity`;
- measurability of `x |-> ofReal (|x.1|^(#(E \ {p})))`.

The `withDensity` transport lemma is kept private in the Lean file, matching
the local pattern already used in other Aoyagi measure files.

## Kill conditions

- Kill if this is described as the unweighted chart-point product measure.
  The density remains on the chart-point side.
- Kill if `|x.1|` is replaced by `x.1`.
- Kill if a pivot-nonzero or positive-radius hypothesis is added to the
  equality itself.
- Kill if this is described as analytic atlas construction,
  `SelectedEntryAnalyticJacobianVolumeData`, original/source-prior transport,
  determinant-chart Haar transport, raw/source Haar, source coverage,
  source-rank coverage, transition regularity, source production, branch
  termination, normal-crossing extraction, pole order, or RLCT.
