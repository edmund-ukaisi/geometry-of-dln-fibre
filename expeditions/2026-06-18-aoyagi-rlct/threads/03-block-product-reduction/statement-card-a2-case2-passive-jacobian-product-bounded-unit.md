# Statement Card - A2 Case 2 Passive Jacobian Product Bounded Unit

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Lean Names

```text
exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive
```

## Reproduction

```text
reproduction-a2-case2-passive-jacobian-product-bounded-unit.md
```

## Claim

For the endpoint-transported passive-parameter Case 2 selected-entry
retained-passive coordinates, the solved-`A1` product raw-order Jacobian
density is locally bounded above and below by positive constants near any
parameter point, assuming the passive fields are continuous and the active
top block and passive `A1` blocks have unit determinant at that parameter
point.

## Role

This supplies passive Jacobian/unit accounting for the larger
source-prior/passive-variable frontier.  It records that the passive
retained-coordinate Jacobian factor is locally a positive bounded unit along
the Case 2 passive selected-entry parametrization.

## Proved

An eventual-neighborhood statement:

```text
exists epsilon K, 0 < epsilon, 0 < K, and eventually near z0
  epsilon <= retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
  retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z) <= K
```

where `Y z` is the topology tuple of the endpoint-transported passive
selected-entry retained-passive datum.

## Assumed

Continuity of the passive fields and basepoint determinant-unit hypotheses for
`Ctop z0.1` and `A1passive z0.1`.

## Cited

None.

## Deferred

Determinant-chart Haar transport for the passive selected-entry sector,
external/original source-prior comparison, selected-entry image coverage,
source-rank coverage, normal crossings, pole order, and RLCT extraction.

## Status

Proved in Lean and reviewed.  Focused build, `git diff --check`,
`scripts/sorries`, and direct axiom probe passed.
