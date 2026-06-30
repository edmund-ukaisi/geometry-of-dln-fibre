# Statement card - A2 Case 2 passive theta Jacobian-dominated source

Date: 2026-06-30.

## Statement

For an arbitrary candidate theta-domain source measure, local domination by the
globally Jacobian-weighted passive-product theta measure is enough to discharge
the retained-passive residual-source hypotheses on a smaller punctured sector.

Let

```text
passiveSource = passiveMeasure.prod weightedBox,
Y z = case2PassiveThetaEndpointTopologyTuple z,
J z = retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z),
jacobianDensity z = ofReal (J z),
baseJ = passiveSource.withDensity jacobianDensity.
```

For a base theta point in the passive determinant sector with nonzero selected
pivot, finite passive mass, positive selected-entry radii, `0 <= t`, and the
selected-entry critical inequality, there is an open neighborhood `W` of the
base point such that the chart-produced measure

```text
mu = Measure.map sourceChart (candidateMeasure.restrict W)
```

is supported on the retained-passive p.13 local source.  Moreover, for every
finite scalar `c`, if

```text
candidateMeasure.restrict W <= c * baseJ.restrict W,
```

then `mu` has a.e. residual square-sum positivity and
`residualNegPowerIntegrableOn localSource mu t`.

## Lean Target

Module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Theorem:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
```

## Proof Idea

Take `U` from the theta Jacobian sandwich and `V` from the existing
arbitrary-source passive-product residual-source socket applied to
`candidateMeasure.restrict U`.  Set `W = U inter V`.

The local domination hypothesis by `baseJ.restrict W` rewrites as domination
by `((passiveSource.restrict U).withDensity jacobianDensity).restrict V`.
The Jacobian upper sandwich bounds this restricted weighted measure by
`ofReal K * passiveSource`, so the candidate measure is dominated by
`(c * ofReal K) * passiveSource`.  The scalar is finite, and the existing
passive-product socket applies.

## Nonclaims

No source-prior construction, determinant-chart Haar transport, raw-order Haar
transport, exact passive-sector pushforward, source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT extraction is
claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-jacobian-dominated-source.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-jacobian-dominated-source.md
```
