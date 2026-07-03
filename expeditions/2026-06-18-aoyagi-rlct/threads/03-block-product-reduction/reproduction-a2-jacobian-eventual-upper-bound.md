# A2 Jacobian eventual upper bound

Date: 2026-07-03.

## Calculation

For the enlarged with-following source, set

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    n hS hcont hnext z eNext e
```

and

```text
jacobianDensity z =
  ENNReal.ofReal
    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
      (M := 1) (Y z)).
```

The endpoint topology-tuple map is continuous:

```text
Continuous Y.
```

If the base point `z0` lies in the with-following determinant sector, then
the endpoint topology tuple lands in the retained-passive determinant chart:

```text
Y z0 in topologyTupleDetChartSet.
```

The retained-passive raw-order Jacobian local-unit theorem applied to `Y`
then gives real constants `epsilon` and `K` with `0 < K` and, eventually near
`z0`,

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z) <= K.
```

Take

```text
CJ = ENNReal.ofReal K.
```

This constant is finite by `ENNReal.ofReal_lt_top`.  The eventual real upper
bound lifts pointwise to the ENNReal bound by monotonicity of `ENNReal.ofReal`:

```text
ENNReal.ofReal
  (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))
    <= ENNReal.ofReal K.
```

Thus, eventually near `z0`,

```text
jacobianDensity z <= CJ.
```

This is exactly the Jacobian-side eventual upper-bound input needed by the
eventual-density coordinate-source finite-integral handoff.

## Lean Targets

Generic ENNReal continuity infrastructure:

```text
eventually_le_const_ennreal_of_continuousAt_lt
exists_lt_top_eventually_le_of_continuousAt_lt_top
exists_open_ae_restrict_le_of_continuousAt_lt_top
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

Jacobian endpoint specialization:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_finite_eventually_le_jacobianDensity_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

## Boundary

This proves only the Jacobian-side eventual upper bound.  It does not prove
the source-density eventual upper bound: the current source-image density is
an arbitrary argument, so that side needs an explicit continuity and finite
base-value hypothesis for `sourceImageDensity` composed with the endpoint
source chart, or a concrete source-image density construction.

It also proves no determinant-Haar/raw-Haar transport, original-prior
transport, normal crossings, pole order, or RLCT extraction.
