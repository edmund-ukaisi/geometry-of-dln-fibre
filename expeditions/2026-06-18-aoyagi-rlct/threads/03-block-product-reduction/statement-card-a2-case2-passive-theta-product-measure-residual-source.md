# Statement card - A2 Case 2 passive theta product-measure residual-source adapter

Date: 2026-06-30.

## Statement

Specialize the passive-product selected-entry residual-source theorem to the
concrete full theta coordinate type `Case2PassiveTheta`.

For a base theta point in the determinant sector with nonzero selected pivot,
let

```text
sourceMeasure = passiveMeasure.prod weightedBox
```

where `passiveMeasure` is a finite-mass measure on
`Case2PassiveTheta.PassiveFields` and `weightedBox` is the selected-entry
signed-box measure with `sourceDensity`.  Under the selected-entry critical
inequality, there is an open punctured determinant-sector neighborhood `V`
such that

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V)
```

is supported on the retained-passive p.13 local source, has positive residual
square-sum almost everywhere on that local source, and satisfies
`residualNegPowerIntegrableOn localSource mu t`.

## Lean Target

Module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductMeasure.lean
```

Theorem:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_finiteMass
```

The proof should specialize the existing generic theorem:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass
```

with `eta = Case2PassiveTheta.PassiveFields`.

## Key Calculation

The proof uses domination, not exact marginal equality:

```text
Measure.map Case2PassiveTheta.yNext
    ((passiveMeasure.prod weightedBox).restrict V)
  <= passiveMeasure Set.univ • weightedBox.
```

Exact equality after restriction would require a product-saturated description
of `V`, which is not part of this theorem.

## Nonclaims

No exact restricted `yNext` marginal equality, determinant-chart Haar
transport, raw-order Haar transport, source-prior transport, exact
passive-sector pushforward, source-image equality, source-rank coverage,
finite-integral transfer for the original source prior, normal crossings, pole
order, or RLCT extraction is claimed.

## Local Domination Variant

The same module also exposes the arbitrary-source wrapper:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_passiveProductMeasure_finiteMass
```

It returns a sector `V` and proves the same residual-source conclusion under
the explicit local hypothesis:

```text
sourceMeasure.restrict V <= c • passiveSource,
c < infinity.
```

This is a reusable socket for future source-prior work; it does not prove that
any original source prior satisfies the local domination hypothesis.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-product-measure-residual-source.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-product-measure-residual-source.md
```
