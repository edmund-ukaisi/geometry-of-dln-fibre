# Reproduction - A2 passive theta source-image bounded-density pullback

Date: 2026-06-30.

## Question

The previous source-image theorem constructs, for an external source-side
measure restricted to the local passive-theta image,

```text
candidate =
  Measure.map readback (externalMeasure.restrict (sourceChart '' V)).
```

Can the desired theta-domain domination

```text
candidate <= c • thetaReference.restrict V
```

be proved without assuming it?

Answer: only after a source-image density comparison is supplied.  For an
arbitrary external measure the statement is false: a Dirac mass on one image
point pulls back to a Dirac mass in theta coordinates, and this need not be
dominated by a product/Lebesgue-like theta reference measure.  The elementary
part is the bounded-density handoff below.

## Calculation

Let

```text
sourceBase =
  Measure.map sourceChart (thetaReference.restrict V).
```

Assume the local inverse and measurability data:

```text
readback (sourceChart theta) = theta, for theta in V,
MeasurableSet V,
MeasurableSet (sourceChart '' V),
AEMeasurable sourceChart (thetaReference.restrict V),
AEMeasurable readback sourceBase.
```

First, the chart-produced source-image reference pulls back exactly:

```text
Measure.map readback sourceBase
  = Measure.map (fun theta => readback (sourceChart theta))
      (thetaReference.restrict V)
  = thetaReference.restrict V.
```

Now suppose a source-image measure is a bounded-density perturbation of
`sourceBase`:

```text
sourceImageMeasure =
  (sourceBase.withDensity density).restrict (sourceChart '' V),
```

and

```text
density E <= c
```

for `sourceBase.restrict (sourceChart '' V)`-a.e. `E`.  Then

```text
sourceImageMeasure <= c • sourceBase
```

by the existing `restrict_withDensity_le_smul_of_ae_le` lemma.  Mapping both
sides by `readback` preserves the scalar domination:

```text
Measure.map readback sourceImageMeasure
  <= c • Measure.map readback sourceBase
  =  c • thetaReference.restrict V.
```

If an actual external measure satisfies the density identity

```text
externalMeasure.restrict (sourceChart '' V)
  =
  (sourceBase.withDensity density).restrict (sourceChart '' V),
```

then its pulled-back candidate has the same domination.

## Source Boundary

Aoyagi assumes a smooth compactly supported prior positive at the true
parameter.  Local boundedness of the prior and nonzero Jacobian units is
elementary after shrinking.  What is not supplied by the paper's p.13
block-product algebra is the project-specific theorem identifying the
restricted original/source prior on `sourceChart '' V` with the displayed
bounded-density perturbation of the chart-produced source-image reference.

## Nonclaims

No one-chart global support, source-rank coverage, source-image equality with
a source-rank stratum, original DLN prior transport, determinant/raw Haar
identification, normal crossings, pole order, or RLCT extraction is proved.
