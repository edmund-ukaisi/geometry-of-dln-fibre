# Reproduction - A2 Case 2 with-following endpoint reference image active-readout marginal

Date: 2026-07-02.

Status: endpoint-image active-readout marginal reproduced and formalised.
This note does not claim determinant-chart Haar transport, raw-map
pushforward, source-image coverage, normal crossings, pole order, or RLCT
extraction.

## Source Boundary

Aoyagi's Case 2 calculation, PDF pp. 19-21, supplies the selected-pivot
successor residual coordinates and the independent following-factor block.
The preceding endpoint active-readout reproduction checked the finite
coordinate fact:

```text
activeReadout (Y z)
  = ((z.1.1, chartMap pivotNext z.1.yNext), z.2).
```

Here

```text
Y z = case2PassiveThetaWithFollowingFactorEndpointTopologyTuple ... z.
```

The present step is a measure-theoretic consequence for the named endpoint
image measure.  It uses only the endpoint-image definition, measurability from
continuity, `Measure.map_map`, and the already-proved source-coordinate
product COV for `activeReadout o Y`.

## Calculation

Let

```text
referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
    (rho := rho) (tau := tau) n hS hnext Rres
```

and let

```text
endpointReferenceImage =
  case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
    (rho := rho) (tau := tau) (kappa' := kappa') n
    hS hcont hnext eNext e Rres Set.univ.
```

By definition of the endpoint image measure,

```text
endpointReferenceImage
  = Measure.map Y (referenceSource.restrict Set.univ).
```

Since `Set.univ` is the whole source domain,

```text
referenceSource.restrict Set.univ = referenceSource.
```

The active readout and the endpoint map are continuous finite-coordinate maps,
so they are measurable.  Therefore `Measure.map_map` gives

```text
Measure.map activeReadout endpointReferenceImage
  = Measure.map activeReadout (Measure.map Y referenceSource)
  = Measure.map (fun z => activeReadout (Y z)) referenceSource.
```

The previous active-readout bridge identifies the composite

```text
fun z => activeReadout (Y z)
```

with the active selected-entry source-coordinate chart

```text
z |-> ((z.1.1, chartMap pivotNext z.1.yNext), z.2).
```

The source-coordinate product COV already formalised for that chart then gives

```text
Measure.map activeReadout endpointReferenceImage
  =
(passiveRef.prod
  (volume.restrict (chartMap pivotNext '' signedBoxSet Rres))).prod
followingRef.
```

This equality is only a marginal equality after applying `activeReadout` to
the endpoint image.  It says nothing about coordinates of the endpoint tuple
that `activeReadout` discards.

## Checks

The calculation depends on the following checks:

- `activeReadout` is continuous, hence measurable.
- `Y` is continuous, hence measurable.
- The endpoint image is taken with `Set.univ`, so no restricted-domain product
  marginal is being asserted.
- The product measure on the right is the same product reference measure from
  the active selected-entry source-coordinate COV.

The result would not justify replacing the endpoint image measure itself by a
determinant-chart Haar/reference measure.  That stronger statement would
require a full endpoint coordinate COV and source-image coverage information,
neither of which is part of this step.
