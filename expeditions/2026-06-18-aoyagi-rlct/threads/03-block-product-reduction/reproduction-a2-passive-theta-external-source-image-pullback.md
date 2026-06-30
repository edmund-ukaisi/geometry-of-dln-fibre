# Reproduction - A2 passive-theta external source-image pullback

Date: 2026-06-30.

## Goal

Bridge an external source-side measure into the concrete passive-theta chart
without pretending to have global source-prior transport.

For the local passive-theta source chart

```text
sourceChart : Theta -> EdgeFamily
readback    : EdgeFamily -> Theta
```

and the local measurable image `sourceChart '' V`, define the pulled-back
candidate measure

```text
candidateMeasure =
  Measure.map readback (externalMeasure.restrict (sourceChart '' V)).
```

The desired chart-theoretic identity is

```text
Measure.map sourceChart candidateMeasure =
  externalMeasure.restrict (sourceChart '' V),
```

with the additional support fact

```text
candidateMeasure.restrict V = candidateMeasure.
```

## Paper Scope

Aoyagi assumes an a priori probability density `phi(w)` on the parameter set,
and in the main DLN theorem assumes that `phi` is smooth with compact support
and positive at the true parameter.  The normal-crossing formula also uses the
transformed density factor `pi'(u) phi(pi(u))`.

Those analytic density facts are not proved here.  The present step is only
the local chart-image measure bookkeeping needed to state such a density
comparison in the passive-theta chart:

1. restrict the external source measure to an already proved measurable chart
   image;
2. pull it back by the local readback;
3. use the local right-inverse identity on the image to push it forward again.

## Calculation

Assume:

```text
V is measurable,
sourceChart '' V is measurable,
readback is a.e. measurable for externalMeasure.restrict (sourceChart '' V),
forall E in sourceChart '' V,
  readback E in V and sourceChart (readback E) = E.
```

First, since `externalMeasure.restrict (sourceChart '' V)` is concentrated on
`sourceChart '' V`, the pointwise implication `readback E in V` gives

```text
forall^ae theta with respect to candidateMeasure, theta in V.
```

Therefore:

```text
candidateMeasure.restrict V = candidateMeasure.
```

Second, `sourceChart` is continuous on `V` in the already proved local image
theorem.  Since `candidateMeasure` is supported on `V`, `sourceChart` is
a.e. measurable for `candidateMeasure`.

Now use the a.e.-measurable map-map theorem:

```text
Measure.map sourceChart (Measure.map readback externalImageMeasure)
  =
Measure.map (fun E => sourceChart (readback E)) externalImageMeasure.
```

The right-inverse identity gives

```text
fun E => sourceChart (readback E) = id
```

almost everywhere for `externalImageMeasure`, because that measure is
restricted to the image.  Hence:

```text
Measure.map sourceChart candidateMeasure =
  Measure.map id externalImageMeasure =
  externalImageMeasure.
```

## Boundary

This is not a proof that the original source prior is supported in one
passive-theta chart image.  It is only a theorem about the portion of an
external source measure already restricted to the chosen chart image.

It also does not prove a density bound

```text
candidateMeasure.restrict V <= c • baseJacobianMeasure.restrict V.
```

That domination remains the next source-prior/Jacobian handoff hypothesis or
target.  No determinant-chart Haar transport, raw-order Haar transport, normal
crossings, pole order, or RLCT extraction is proved here.

