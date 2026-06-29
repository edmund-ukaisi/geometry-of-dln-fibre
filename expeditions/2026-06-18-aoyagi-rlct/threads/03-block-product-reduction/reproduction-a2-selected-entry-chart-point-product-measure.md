# A2 selected-entry chart-point product measure

## Scope

This note records the finite-coordinate product-measure split for the
selected-entry chart-point adapter.  It is a coordinate bookkeeping theorem
for the map

```text
y |-> (y_p, y|_{E \ {p}}).
```

It is not an analytic atlas construction, not original/source-prior
transport, and not an RLCT extraction.

The Aoyagi source formula used in the nearby selected-entry calculation is
the same elementary substitution from the product-reduction proof:

```text
x_p = u,
x_i = u r_i  for i != p.
```

Here the adapter theorem concerns only the source-coordinate split
`y -> (u, r)`, before applying the selected-entry map `(u, r) -> x`.

## Product-coordinate split

Let `E` be a finite center set and `p in E`.  For a center-coordinate point
`y : E -> R`, define

```text
u = y_p,
r_i = y_i  for i in E \ {p}.
```

The inverse is also coordinate-level:

```text
(u, r) |-> y_p = u,
          y_i = r_i  for i != p.
```

Thus the chart-point adapter is exactly the finite product split

```text
E -> R  ~=  R x (E \ {p} -> R).
```

In Lean this is expressed by `chartPointSplitEquiv`.  It is assembled from
Mathlib's measurable equivalence
`MeasurableEquiv.piEquivPiSubtypeProd`, the singleton collapse
`MeasurableEquiv.piUnique`, and a reindexing equivalence between
`center.erase pivot.1` and the non-pivot subtype of `center`.

## Signed-box measure

For radii `R_i`, the center signed-box product measure is

```text
prod_{i in E} volume|(-R_i, R_i).
```

The product split sends it to

```text
volume|(-R_p, R_p)
  x prod_{i in E \ {p}} volume|(-R_i, R_i).
```

No positivity hypothesis is needed for this equality.  If some interval is
empty or degenerate, both sides still describe the same pushed-forward product
measure.

Lean names the chart-point measure as

```text
chartPointProductMeasure pivot R
```

and proves

```text
map chartPointAdapter
  (prod_{i in E} volume|(-R_i, R_i))
= chartPointProductMeasure pivot R.
```

## Relation to the Jacobian theorem

This theorem uses no selected-entry Jacobian.  The Jacobian density
`|u|^(|E|-1)` belongs to the later map

```text
(u, r) |-> (x_p = u, x_i = u r_i),
```

not to the adapter

```text
y |-> (y_p, y|_{E \ {p}}).
```

The earlier weighted pushforward theorem remains the theorem that pushes the
Jacobian-weighted source measure through the selected-entry chart map to
Lebesgue measure on the target image.

## Kill conditions

- Kill if this is described as analytic atlas construction or
  `SelectedEntryAnalyticJacobianVolumeData`.
- Kill if this is described as original/source-prior transport, determinant
  Haar transport, raw/source Haar, source coverage, source-rank coverage,
  transition regularity, source production, branch termination,
  normal-crossing extraction, pole order, or RLCT.
- Kill if the adapter is confused with the selected-entry chart map: the
  adapter has no nontrivial Jacobian factor; the chart map does.
