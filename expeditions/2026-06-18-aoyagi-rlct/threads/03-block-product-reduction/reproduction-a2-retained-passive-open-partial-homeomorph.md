# Reproduction - A2 Retained-Passive Open Partial Homeomorphism

Date: 2026-06-26.

Status: reproduced and formalised the ambient open-partial-homeomorphism
package for the explicit retained-passive source-recursive chart.

## Question

The previous rungs proved:

```text
{data // data.detChart} equiv_homeomorph {E // sourceRecursiveDetChart E},
```

and then named the source-side set

```text
sourceRecursiveDetChartSet
```

and proved it open in the ambient edge-family space.  The coordinate-side set

```text
detChartSet
```

was already open.  The remaining topological packaging question is whether
these data give a single ambient chart object with source `detChartSet`,
target `sourceRecursiveDetChartSet`, forward map `edgeMatrix`, and inverse
map `sourceReadback`.

## Subtype Rewrite

The old homeomorphism uses predicate subtypes:

```text
{data // data.detChart}
{E // sourceRecursiveDetChart E}.
```

The ambient chart should use the named set subtypes:

```text
detChartSet
sourceRecursiveDetChartSet.
```

These are propositionally the same subtypes because

```text
data in detChartSet <-> data.detChart,
E in sourceRecursiveDetChartSet <-> sourceRecursiveDetChart E.
```

Lean records the rewritten subtype homeomorphism as:

```text
detChartSet_sourceRecursiveDetChartSet_homeomorph.
```

This is only a relabeling of the already-proved subtype homeomorphism.

## Open Partial Homeomorphism Fields

Define an ambient partial equivalence by:

```text
source := detChartSet,
target := sourceRecursiveDetChartSet,
toFun data := data.edgeMatrix,
invFun E := sourceReadback E.
```

The map-source field is exactly the previous theorem:

```text
sourceRecursiveDetChart_edgeMatrix_of_detChart.
```

If `data in detChartSet`, then `data.detChart`, hence `data.edgeMatrix` lies
in `sourceRecursiveDetChartSet`.

The map-target field is exactly:

```text
sourceReadback_detChart_of_sourceRecursiveDetChart.
```

If `E in sourceRecursiveDetChartSet`, then `sourceReadback E` lies in
`detChartSet`.

The inverse laws are the already banked finite inverse laws:

```text
sourceReadback_edgeMatrix_eq,
edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart.
```

The source and target are open by:

```text
isOpen_detChartSet,
isOpen_sourceRecursiveDetChartSet.
```

## Continuity Fields

For the forward continuity-on-source field, use the existing determinant-chart
subtype theorem:

```text
continuous_edgeMatrix_detChart_subtype.
```

The only bookkeeping is to rewrite the subtype `{data // data in detChartSet}`
as `{data // data.detChart}` using `mem_detChartSet`.

For the inverse continuity-on-target field, at every
`E in sourceRecursiveDetChartSet`, the existing pointwise theorem

```text
continuousAt_sourceReadback
```

applied to the identity edge-family map gives continuity at `E`; this implies
continuity within the target set.

Lean records the ambient chart as:

```text
detChart_sourceRecursiveDetChart_openPartialHomeomorph.
```

## Nonclaims

This is an ambient open partial homeomorphism between the explicit retained-
passive determinant coordinate chart and the explicit source-recursive
determinant edge chart.  It does not prove that this chart is the whole source
image, source-rank coverage, measure pushforward, density/Jacobian transport,
normal crossings, pole order, or RLCT extraction.
