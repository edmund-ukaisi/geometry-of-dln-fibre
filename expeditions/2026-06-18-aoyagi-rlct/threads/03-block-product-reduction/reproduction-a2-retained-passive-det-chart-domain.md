# Reproduction - A2 Retained-Passive Determinant-Chart Domain

Date: 2026-06-26.

Status: determinant-domain layer for the nonredundant retained-passive
coordinate object.  This is the first topology/domain rung after the finite
dummy-slot cleanup.

## Question

The nonredundant retained-passive coordinate object has a source map

```text
edgeMatrix : retained coordinates -> fixed-base edge family.
```

The finite readback and extensionality theorem requires exactly two kinds of
determinant-unit side conditions:

```text
det(Ctop) is a unit,
det(A1passive_p) is a unit for every passive A1 block.
```

These are the retained-passive determinant-chart conditions.  They should be
named as one domain predicate before any source-rank coverage, image, or
measure theorem is attempted.

## Finite Domain Predicate

Define

```text
detChart(data) :=
  IsUnit data.Ctop.det
  and for every p : Fin M, IsUnit (data.A1passive p).det.
```

For `M=0`, the passive `A1` family is empty.  The determinant chart is then
only the active condition `IsUnit data.Ctop.det`, which is the expected
single-edge endpoint condition.

The predicate packages exactly the side conditions needed by the already
proved readback theorem:

```text
edgeMatrix_readbacks_eq_targets_of_detChart
```

and exactly the side conditions needed by the already proved full
nonredundant extensionality theorem:

```text
edgeMatrix_ext_of_detChart.
```

It also gives the set-level source-map injectivity statement

```text
injOn_edgeMatrix_detChartSet.
```

This is still injectivity of the finite source map on its determinant-domain
set, not a statement that the image is open or covers any source-rank stratum.

## Topology Tuple And Openness

To state openness, give the nonredundant coordinate record the product topology
on its finite matrix fields:

```text
(A1passive, F2, A3passive, C, Ctop, F3).
```

The determinant-domain set is the intersection of:

```text
{data | IsUnit data.Ctop.det}
```

and the finite intersection over `p : Fin M` of

```text
{data | IsUnit (data.A1passive p).det}.
```

Each component is open because the matrix coordinate projection is continuous,
the determinant is continuous, and the unit locus is open in a topological
ring with open units.  The finite intersection is open.

This proves:

```text
isOpen_detChartSet
detChartSet_mem_nhds.
```

The theorem is intentionally stated as topology of the coordinate domain.  It
does not prove that `edgeMatrix` is continuous, that the determinant-domain
image is open, or that a source-rank neighborhood lies in that image.

## Nonclaims

No source-rank coverage, source/image equality, image openness, continuity of
`edgeMatrix`, measure pushforward, density/Jacobian theorem, normal crossings,
pole order, or RLCT extraction is proved here.  The centered active coordinate
`X=Ctop-I` is also not introduced in this rung.
