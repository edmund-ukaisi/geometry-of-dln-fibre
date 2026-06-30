# Reproduction - A2 source-image external density automatic readback

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a generic source-image
measure handoff.  It is intentionally not an original-prior transport theorem.

## Question

Suppose a local chart

```text
sourceChart : Theta -> E
readback    : E -> Theta
```

is continuous and injective on a measurable coordinate set `V`, with

```text
readback (sourceChart theta) = theta
```

for `theta in V`.  If an external source-side measure is identified on the
chart image as a bounded-density perturbation of the chart-produced
pushforward, can we pull that restricted external measure back to a measure
dominated on coordinates?

## Calculation

Let

```text
sourceBase = Measure.map sourceChart (thetaReference.restrict V).
image      = sourceChart '' V.
```

Assume

```text
externalMeasure.restrict image =
  (sourceBase.withDensity density).restrict image
```

and

```text
density E <= c
```

for `sourceBase.restrict image` almost every `E`.

Since `sourceChart` is continuous and injective on `V`, and `Theta` is a
Polish Borel space, the restricted chart is a measurable embedding.  The
pointwise left inverse reduces readback measurability for `sourceBase` to the
measurability of the subtype inclusion:

```text
readback o sourceChart = id
```

on `V`.  Therefore the previously proved bounded-density pullback theorem
applies:

```text
Measure.map readback
  ((sourceBase.withDensity density).restrict image)
    <= c • thetaReference.restrict V.
```

Replacing the weighted source-image measure by the externally supplied
restricted measure using the displayed equality gives

```text
Measure.map readback (externalMeasure.restrict image)
  <= c • thetaReference.restrict V.
```

## Aoyagi Boundary

This theorem is deliberately generic in `Theta`.  In a future p.13 application
`Theta` can be the full product-coordinate space containing the residual
source coordinates and the regular variables `B = C1 - I`, `F2`, and `F3`.

The theorem does not build that p.13 chart, prove source-rank coverage, prove
Haar transport, or identify Aoyagi's original smooth prior with the supplied
source-image density.  Those remain separate source-prior/Jacobian tasks.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity_of_continuousOn_injOn
```

The theorem should derive readback a.e. measurability from
`ContinuousOn sourceChart V`, `Set.InjOn sourceChart V`, and the local left
inverse, then use the existing external-measure bounded-density handoff.

## Nonclaims

No original/source prior density identity, no domination for arbitrary
external measures, no passive-theta-only full p.13 prior transport, no
source-rank coverage, no Haar transport, no normal crossings, no pole order,
and no RLCT extraction.
