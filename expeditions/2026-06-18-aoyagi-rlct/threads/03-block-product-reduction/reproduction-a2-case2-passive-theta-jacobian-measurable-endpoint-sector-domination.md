# Reproduction - A2 Case 2 passive theta Jacobian measurable endpoint-sector domination

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a local assumption-removal
wrapper: the previous endpoint-sector domination theorem required the local
endpoint image sector to be measurable as an input; the new endpoint local
injectivity theorem supplies that measurability after shrinking.

## Question

Can the local endpoint-sector domination theorem for the Jacobian-weighted
passive-product theta measure be stated without an explicit sector
measurability argument?

Answer: yes, locally and under the same standard descriptive-set-theoretic
hypotheses used for the local image theorem.  We shrink the Jacobian-unit
neighborhood to an open neighborhood whose endpoint image is measurable, then
restrict the Jacobian upper bound to that smaller open set.

## Setup

Write

```text
Y(z) = case2PassiveThetaEndpointTopologyTuple ... z eNext e

passiveSource = passiveMeasure.prod weightedBox

jacobianDensity(z) =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y(z))).
```

The Jacobian sandwich gives a positive constant `K` and an open neighborhood
`U` of the base theta point such that

```text
(passiveSource.restrict U).withDensity jacobianDensity
  <= ofReal K • passiveSource.restrict U.
```

The local endpoint-sector measurability theorem gives an open neighborhood
`V0` of the same base point on which `Y '' V0` is measurable.  In the relative
form needed here, if `G` is any open neighborhood of the base point, we take

```text
V = G ∩ V0.
```

Then `V` is open, contains the base point, is contained in `G`, and `Y '' V`
is measurable because the endpoint map is injective on the original local
injectivity neighborhood and continuous on `V`.

Apply this relative statement with `G = U`.  We obtain an open `V` such that

```text
V ⊆ U,
MeasurableSet (case2PassiveThetaEndpointSectorSet ... V).
```

## Restricting the Jacobian upper bound

Since `V ⊆ U`,

```text
(passiveSource.restrict U).restrict V = passiveSource.restrict V.
```

Also, because `V` is measurable,

```text
(passiveSource.withDensity jacobianDensity).restrict V
  = (passiveSource.restrict V).withDensity jacobianDensity
  = ((passiveSource.restrict U).withDensity jacobianDensity).restrict V.
```

Restricting the upper side of the Jacobian sandwich to `V` gives

```text
((passiveSource.restrict U).withDensity jacobianDensity).restrict V
  <= (ofReal K • passiveSource.restrict U).restrict V
  = ofReal K • passiveSource.restrict V.
```

Hence

```text
(passiveSource.withDensity jacobianDensity).restrict V
  <= ofReal K • passiveSource.restrict V.
```

## Endpoint-sector domination

Let

```text
S_V = case2PassiveThetaEndpointSectorSet ... V = Y '' V.
```

The previous endpoint-sector domination transfer applies to the theta-domain
domination above, using the measurable sector proof just obtained.  Therefore

```text
(Measure.map Y ((passiveSource.withDensity jacobianDensity).restrict V)).restrict S_V
  <= ofReal K •
     (Measure.map Y (passiveSource.restrict V)).restrict S_V.
```

The conclusion contains both the measurable-sector fact and the domination
inequality.  It is still only local; it does not identify the endpoint-sector
measure with determinant-chart Haar measure or with any original source prior.

## Lean Targets

Add a relative image-measurability theorem to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Suggested public name:

```text
exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet
```

Add the strengthened Jacobian endpoint-sector domination wrapper to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Suggested public name:

```text
exists_pos_open_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_jacobian_restrict_endpointSectorSet_le_smul_passiveProductMeasure
```

## Nonclaims

This slice does not prove global endpoint-sector measurability, exact
passive-sector Haar transport, determinant-chart Haar transport, raw-order
Haar transport, source-prior comparison, source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
