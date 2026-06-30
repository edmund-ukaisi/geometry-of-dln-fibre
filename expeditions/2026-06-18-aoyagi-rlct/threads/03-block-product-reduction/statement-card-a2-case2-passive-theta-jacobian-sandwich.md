# Statement card - A2 Case 2 passive theta Jacobian sandwich

Date: 2026-06-30.

## Statement

Specialize the generic passive-parameter retained-passive Jacobian sandwich to
the concrete full theta coordinate type `Case2PassiveTheta`.

Let

```text
sourceMeasure = passiveMeasure.prod weightedBox
Y z = case2PassiveThetaEndpointTopologyTuple z.
```

For a base theta point in the passive determinant sector, there are positive
constants `epsilon` and `K` and an open neighborhood `U` of the base point
such that

```text
ofReal epsilon • sourceMeasure.restrict U
  <= (sourceMeasure.restrict U).withDensity
       (fun z => ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)))
```

and

```text
(sourceMeasure.restrict U).withDensity
       (fun z => ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)))
  <= ofReal K • sourceMeasure.restrict U.
```

## Lean Target

Module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Theorem:

```text
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
```

The proof should specialize the existing generic theorem:

```text
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
```

with `eta = Case2PassiveTheta.PassiveFields`.

## Nonclaims

No determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, source-image
equality, source-rank coverage, construction of an original source-prior
density, normal crossings, pole order, or RLCT extraction is claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-jacobian-sandwich.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-jacobian-sandwich.md
```
