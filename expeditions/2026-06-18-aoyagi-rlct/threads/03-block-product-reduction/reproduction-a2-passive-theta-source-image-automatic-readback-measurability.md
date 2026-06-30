# Reproduction - A2 passive theta source-image automatic readback measurability

Date: 2026-06-30.

## Question

In the bounded-density source-image pullback socket, can the hypothesis

```text
AEMeasurable readback (Measure.map sourceChart (thetaReference.restrict V))
```

be derived from the local passive-theta source-chart package?

Answer: yes, for the chart-produced source-image reference.  The local package
already provides a measurable open `V`, `ContinuousOn sourceChart V`,
`Set.InjOn sourceChart V`, and

```text
readback (sourceChart theta) = theta, for theta in V.
```

## Calculation

Let `Theta` be the passive-theta coordinate space and assume it is a Polish
Borel space.  Put

```text
sourceChartV : V -> E,       sourceChartV(theta) = sourceChart(theta)
thetaReferenceV = Measure.comap ((Subtype.val) : V -> Theta) thetaReference.
```

Since `sourceChart` is continuous and injective on the measurable set `V`,
Lusin-Souslin in Mathlib gives

```text
MeasurableEmbedding sourceChartV.
```

By `MeasurableEmbedding.aemeasurable_map_iff`, to prove

```text
AEMeasurable readback (Measure.map sourceChartV thetaReferenceV)
```

it is enough to prove

```text
AEMeasurable (readback ∘ sourceChartV) thetaReferenceV.
```

But on the subtype `V`,

```text
readback (sourceChartV theta) = theta.val.
```

The right side is the measurable subtype inclusion `V -> Theta`, hence the
composition is a.e.-measurable.

It remains to identify the measure:

```text
Measure.map sourceChartV thetaReferenceV
  =
Measure.map sourceChart (thetaReference.restrict V).
```

This is the usual subtype restriction identity
`map_comap_subtype_coe hV`, followed by map-map for the a.e.-measurable
composition `sourceChart ∘ Subtype.val`.

Therefore the readback is a.e.-measurable for the chart-produced source-image
reference.  Feeding this proof into the previous bounded-density socket removes
the explicit readback-measurability input from the concrete passive-theta
wrapper.

## Source Boundary

This is measure-theoretic/topological bookkeeping over the already-built
local p.13 source chart.  Aoyagi supplies the local coordinate/readback
calculation being formalised; the measurable-embedding step is standard
Lusin-Souslin infrastructure, not a new analytic or RLCT citation.

## Nonclaims

This does not identify an original/source prior, prove source-rank coverage,
prove equality with a source-rank stratum, prove Haar transport, construct
normal crossings, compute pole order, or extract RLCT.
