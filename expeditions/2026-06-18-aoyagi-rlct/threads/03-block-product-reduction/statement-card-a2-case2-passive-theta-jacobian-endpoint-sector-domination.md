# Statement card - A2 Case 2 passive theta Jacobian endpoint-sector domination

Date: 2026-06-30.

## Statement

For

```text
passiveSource = passiveMeasure.prod weightedBox
Y theta = case2PassiveThetaEndpointTopologyTuple theta
jacobianDensity theta =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y theta)),
```

there is a positive `K` and an open neighborhood `U` of the passive
determinant-sector base point such that, for every measurability proof of

```text
S_U = case2PassiveThetaEndpointSectorSet U,
```

one has

```text
(Measure.map Y ((passiveSource.withDensity jacobianDensity).restrict U)).restrict S_U
  <= ofReal K *
     (Measure.map Y (passiveSource.restrict U)).restrict S_U.
```

## Lean Target

```text
exists_pos_open_measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_jacobian_restrict_endpointSectorSet_le_smul_passiveProductMeasure
```

## Proof Idea

Apply the existing Case 2 passive theta Jacobian sandwich to get the local
upper domination

```text
(passiveSource.restrict U).withDensity jacobianDensity
  <= ofReal K * passiveSource.restrict U.
```

Rewrite `(passiveSource.withDensity jacobianDensity).restrict U` by
`restrict_withDensity`, then apply the endpoint-sector domination transfer.

## Nonclaims

No exact passive-sector Haar pushforward, determinant-chart Haar transport,
raw-order Haar transport, source-prior comparison, source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT extraction is
claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-jacobian-endpoint-sector-domination.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-jacobian-endpoint-sector-domination.md
```
