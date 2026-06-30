# Reproduction - A2 Case 2 passive theta Jacobian sandwich

Date: 2026-06-30.

Status: pen-and-paper check before the theta-specific passive-Jacobian
measure adapter.

## Question

The generic passive-parameter Case 2 Jacobian theorem proves that the
retained-passive raw-order Jacobian product is locally a bounded positive
unit, and therefore gives a two-sided `withDensity` comparison over the
passive-product selected-entry coordinate measure.

Can this be specialized to the concrete full theta coordinate type
`Case2PassiveTheta`?

## Calculation

Write

```text
Case2PassiveTheta = PassiveFields x Center
```

where

```text
PassiveFields = (A1passive, F2, A3passive, Ctop, F3)
Center        = case2ResidualBlockPivotEntries n S (J+1).
```

For a theta coordinate `z`, the endpoint topology tuple is

```text
Y z = case2PassiveThetaEndpointTopologyTuple z.
```

At a base point `z0` in the passive determinant sector,

```text
IsUnit (Ctop z0).det
forall p : Fin 1, IsUnit ((A1passive z0 p).det).
```

The selected residual coordinates do not enter these determinant conditions.
The coordinate projections from `PassiveFields` are continuous by product
topology, and `case2PassiveThetaEndpointTopologyTuple` is already proved
continuous.  Therefore the generic retained-passive Jacobian theorem applies:
there are positive constants `epsilon` and `K` such that, eventually near
`z0`,

```text
epsilon <= retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z) <= K.
```

After restricting the passive-product selected-entry source measure

```text
sourceMeasure = passiveMeasure.prod weightedBox
```

to a sufficiently small open neighborhood `U`, these inequalities hold
`sourceMeasure.restrict U`-almost everywhere.  Applying the elementary
measure helper

```text
withDensity_ofReal_sandwich_of_ae_bounds
```

gives the two-sided comparison

```text
ofReal epsilon • sourceMeasure.restrict U
  <= (sourceMeasure.restrict U).withDensity
       (fun z => ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)))

(sourceMeasure.restrict U).withDensity
       (fun z => ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)))
  <= ofReal K • sourceMeasure.restrict U.
```

This is the exact theta-domain specialization of the already-proved abstract
passive-parameter sandwich.

## Intended Lean Shape

Create a theta-specific adapter in a new module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

The public theorem should be:

```text
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
```

It should specialize:

```text
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
```

with

```text
eta = Case2PassiveTheta.PassiveFields.
```

## Source Boundary

Aoyagi pp. 10-13 support the retained-passive p.13 coordinate chart and the
passive determinant-unit conditions.  The present step is chart-domain
Jacobian bookkeeping over previously formalized retained-passive Jacobian
infrastructure and measure monotonicity.  It uses no quiver-paper evidence and
no new cited theorem.

## Nonclaims

This slice does not prove determinant-chart Haar transport, raw-order Haar
transport, source-prior transport, exact passive-sector pushforward,
source-image equality, source-rank coverage, construction of an original
source-prior density, normal crossings, pole order, or RLCT extraction.
