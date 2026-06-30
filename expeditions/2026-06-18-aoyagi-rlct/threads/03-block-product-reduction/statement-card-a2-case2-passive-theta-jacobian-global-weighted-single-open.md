# Statement card - A2 Case 2 passive theta global Jacobian-weighted single open

Date: 2026-06-30.

## Statement

Repackage the Jacobian-weighted residual-source theorem so the source measure is
the globally weighted passive-product theta measure restricted to one open set.

Let

```text
passiveSource = passiveMeasure.prod weightedBox,
Y z = case2PassiveThetaEndpointTopologyTuple z,
J z = retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z),
jacobianDensity z = ofReal (J z).
```

For a base theta point in the passive determinant sector with nonzero selected
pivot, finite passive mass, positive selected-entry radii, `0 <= t`, and the
selected-entry critical inequality, there is an open neighborhood `W` of the
base point such that

```text
sourceMeasure = passiveSource.withDensity jacobianDensity
mu = Measure.map sourceChart (sourceMeasure.restrict W)
```

is supported on the retained-passive p.13 local source, and has a.e. residual
square-sum positivity plus `residualNegPowerIntegrableOn localSource mu t`.

## Lean Target

Module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Theorem:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_globalWithDensity_jacobian_finiteMass
```

## Nonclaims

No determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, source-image
equality, source-rank coverage, construction of an original source-prior
density, normal crossings, pole order, or RLCT extraction is claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-jacobian-global-weighted-single-open.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-jacobian-global-weighted-single-open.md
```
