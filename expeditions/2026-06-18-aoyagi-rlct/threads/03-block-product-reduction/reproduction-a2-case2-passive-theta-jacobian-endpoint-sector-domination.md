# Reproduction - A2 Case 2 passive theta Jacobian endpoint-sector domination

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a local endpoint-sector
domination consequence of the already proved Jacobian sandwich, not Haar
transport or source-prior construction.

## Question

The previous slice proved that if a theta-domain measure is dominated by a
finite scalar multiple of a reference theta-domain measure, then the endpoint
topology-tuple pushforwards restricted to the named sector image satisfy the
same domination.  Can we instantiate that with the concrete retained-passive
formal raw-order Jacobian density on the passive-product theta measure?

Answer: yes.  The existing Case 2 passive theta Jacobian sandwich already
provides the local theta-domain domination.

## Setup

Let

```text
passiveSource = passiveMeasure.prod weightedBox
Y theta = case2PassiveThetaEndpointTopologyTuple theta
jacobianDensity theta =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y theta)).
```

The Jacobian sandwich gives positive constants `epsilon`, `K` and an open
neighborhood `U` of the base theta point such that

```text
(passiveSource.restrict U).withDensity jacobianDensity
  <= ofReal K * passiveSource.restrict U.
```

Since `U` is open, it is measurable, and

```text
(passiveSource.withDensity jacobianDensity).restrict U
  = (passiveSource.restrict U).withDensity jacobianDensity.
```

Therefore

```text
(passiveSource.withDensity jacobianDensity).restrict U
  <= ofReal K * passiveSource.restrict U.
```

## Endpoint Pushforward

Let

```text
S_U = case2PassiveThetaEndpointSectorSet U = Y '' U.
```

Assuming `S_U` is measurable, the endpoint-sector domination transfer gives

```text
(Measure.map Y ((passiveSource.withDensity jacobianDensity).restrict U)).restrict S_U
  <= ofReal K *
     (Measure.map Y (passiveSource.restrict U)).restrict S_U.
```

The measurability of `S_U` remains explicit.  This theorem supplies an actual
local domination instance for the endpoint topology-tuple sector, but it does
not identify the endpoint sector measure with ambient determinant-chart Haar
measure.

## Lean Target

Add the theorem to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Public name:

```text
exists_pos_open_measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_jacobian_restrict_endpointSectorSet_le_smul_passiveProductMeasure
```

## Nonclaims

This slice does not prove exact passive-sector Haar transport,
determinant-chart Haar transport, raw-order Haar transport, source-prior
comparison, source-image equality, source-rank coverage, normal crossings,
pole order, or RLCT extraction.  It uses only the upper side of the local
Jacobian sandwich and the conditional endpoint-sector domination transfer.
