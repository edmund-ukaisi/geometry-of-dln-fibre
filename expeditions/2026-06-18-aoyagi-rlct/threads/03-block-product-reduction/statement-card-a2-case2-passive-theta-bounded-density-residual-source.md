# Statement card - A2 Case 2 passive theta bounded-density residual-source adapter

Date: 2026-06-30.

## Statement

Specialize the generic bounded-density passive-product residual-source handoff
to the concrete full theta coordinate type `Case2PassiveTheta`.

Let

```text
passiveSource = passiveMeasure.prod weightedBox,
sourceMeasure = passiveSource.withDensity sourceDensity.
```

For a base theta point in the determinant sector with nonzero selected pivot,
finite passive mass, positive selected-entry radii, `0 <= t`, and the
selected-entry critical inequality, there is an open punctured
determinant-sector neighborhood `V` such that

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V)
```

is supported on the retained-passive p.13 local source.  Moreover, for every
finite scalar `c`, a local a.e. bound

```text
forall^ae z in passiveSource.restrict V,
  sourceDensity z <= c
```

implies source-side residual positivity and
`residualNegPowerIntegrableOn localSource mu t`.

## Lean Target

Module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductMeasure.lean
```

Theorem:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass
```

The proof should specialize the existing generic theorem:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass
```

with `eta = Case2PassiveTheta.PassiveFields`.

## Nonclaims

No construction of the original source-prior density, no proof that an original
source prior satisfies the local bound, no exact restricted `yNext` marginal
equality, determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, source-image
equality, source-rank coverage, normal crossings, pole order, or RLCT
extraction is claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-bounded-density-residual-source.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-bounded-density-residual-source.md
```
