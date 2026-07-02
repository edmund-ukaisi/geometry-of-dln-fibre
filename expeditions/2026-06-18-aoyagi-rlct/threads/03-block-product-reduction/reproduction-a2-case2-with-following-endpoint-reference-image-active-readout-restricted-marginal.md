# Reproduction - A2 Case 2 with-following endpoint reference image restricted active-readout marginal

Date: 2026-07-02.

Status: restricted endpoint-image active-readout marginal reproduced and
formalised.  This note does not claim a product marginal for arbitrary
restricted source sets, determinant-chart Haar transport, raw-map pushforward,
source-image coverage, normal crossings, pole order, or RLCT extraction.

## Source Boundary

Aoyagi's Case 2 calculation, PDF pp. 19-21, supplies the selected-pivot
successor residual coordinates and the independent following-factor block.
The endpoint coordinate readout already checked the finite-coordinate identity

```text
activeReadout (Y z)
  = activeChart z
  = ((z.1.1, chartMap pivotNext z.1.yNext), z.2),
```

where

```text
Y z = case2PassiveThetaWithFollowingFactorEndpointTopologyTuple ... z.
```

The previous `Set.univ` endpoint-image marginal used this identity plus the
source-coordinate COV to obtain an unrestricted product measure.  The present
step keeps an arbitrary source restriction `Omega` visible, because a
restricted source set need not be rectangular and need not have a product
active marginal.

## Calculation

Let

```text
referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
    (rho := rho) (tau := tau) n hS hnext Rres
```

and for an arbitrary source set `Omega` let

```text
endpointReferenceImage =
  case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
    (rho := rho) (tau := tau) (kappa' := kappa') n
    hS hcont hnext eNext e Rres Omega.
```

By definition,

```text
endpointReferenceImage
  = Measure.map Y (referenceSource.restrict Omega).
```

The active readout and endpoint map are continuous, hence measurable.  Thus
`Measure.map_map` gives

```text
Measure.map activeReadout endpointReferenceImage
  =
Measure.map (fun z => activeReadout (Y z))
  (referenceSource.restrict Omega).
```

The pointwise active-readout theorem identifies the composite:

```text
fun z => activeReadout (Y z)
  =
fun z => ((z.1.1, chartMap pivotNext z.1.yNext), z.2).
```

Therefore

```text
Measure.map activeReadout endpointReferenceImage
  =
Measure.map activeChart (referenceSource.restrict Omega).
```

This is the exact restricted-domain statement.  It is stronger than support
bookkeeping because it identifies the active readout of the endpoint image,
but weaker than the unrestricted product corollary because the right side
still contains `referenceSource.restrict Omega`.

## Checks

- No measurability assumption on `Omega` is needed for the identity itself:
  the restricted measure is a valid measure, and `Y` and `activeReadout` are
  globally measurable.
- The theorem is compatible with the `Set.univ` product corollary: when
  `Omega = Set.univ`, the right side becomes the already-formalised
  active selected-entry source-coordinate pushforward.
- No product measure is asserted for arbitrary `Omega`.
- No information about endpoint coordinates discarded by `activeReadout` is
  recovered.

The result is a local-sector socket: later source restrictions can be carried
through the endpoint-image layer without pretending that arbitrary local
pieces preserve product independence.
